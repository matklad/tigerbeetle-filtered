//! An LSM tree.
const std = @import("std");
const builtin = @import("builtin");
const assert = std.debug.assert;
const math = std.math;
const mem = std.mem;
const os = std.os;
const maybe = stdx.maybe;
const div_ceil = stdx.div_ceil;

const log = std.log.scoped(.tree);
const tracer = @import("../tracer.zig");

const stdx = @import("../stdx.zig");
const constants = @import("../constants.zig");
const vsr = @import("../vsr.zig");
const schema = @import("schema.zig");

const CompositeKeyType = @import("composite_key.zig").CompositeKeyType;
const NodePool = @import("node_pool.zig").NodePool(constants.lsm_manifest_node_size, 16);
const RingBuffer = @import("../ring_buffer.zig").RingBuffer;
pub const ScopeCloseMode = enum { persist, discard };
const snapshot_min_for_table_output = @import("compaction.zig").snapshot_min_for_table_output;

/// We reserve maxInt(u64) to indicate that a table has not been deleted.
/// Tables that have not been deleted have snapshot_max of maxInt(u64).
/// Since we ensure and assert that a query snapshot never exactly matches
/// the snapshot_min/snapshot_max of a table, we must use maxInt(u64) - 1
/// to query all non-deleted tables.
pub const snapshot_latest: u64 = math.maxInt(u64) - 1;

const half_bar_beat_count = @divExact(constants.lsm_batch_multiple, 2);

// StateMachine:
//
// /// state machine will pass this on to all object stores
// /// Read I/O only
// pub fn read(batch, callback) void
//
// /// write the ops in batch to the memtable/objcache, previously called commit()
// pub fn write(batch) void
//
// /// Flush in memory state to disk, perform merges, etc
// /// Only function that triggers Write I/O in LSMs, as well as some Read
// /// Make as incremental as possible, don't block the main thread, avoid high latency/spikes
// pub fn flush(callback) void
//
// /// Write manifest info for all object stores into buffer
// pub fn encode_superblock(buffer) void
//
// /// Restore all in-memory state from the superblock data
// pub fn decode_superblock(buffer) void
//

/// The maximum number of tables for a single tree.
pub const table_count_max = table_count_max_for_tree(
    constants.lsm_growth_factor,
    constants.lsm_levels,
);

pub const TreeConfig = struct {
    /// Unique (stable) identifier, across all trees in the forest.
    id: u16,
    /// Human-readable tree name for logging.
    name: []const u8,
};

pub fn TreeType(comptime TreeTable: type, comptime Storage: type) type {
    const Key = TreeTable.Key;
    const Value = TreeTable.Value;
    const tombstone = TreeTable.tombstone;

    return struct {
        const Tree = @This();

        pub const Table = TreeTable;
        pub const TableMemory = @import("table_memory.zig").TableMemoryType(Table);
        pub const Manifest = @import("manifest.zig").ManifestType(Table, Storage);

        const Grid = @import("../vsr/grid.zig").GridType(Storage);
        const ManifestLog = @import("manifest_log.zig").ManifestLogType(Storage);
        const KeyRange = Manifest.KeyRange;

        const CompactionType = @import("compaction.zig").CompactionType;
        const Compaction = CompactionType(Table, Tree, Storage);

        pub const LookupMemoryResult = union(enum) {
            negative,
            positive: *const Value,
            possible: u8,
        };

        grid: *Grid,
        config: Config,
        options: Options,

        table_mutable: TableMemory,
        table_immutable: TableMemory,

        manifest: Manifest,

        /// The forest can run compactions in any order, potentially concurrently across all levels
        /// simultaneously. There's a + 1 here for the immmutable table to level 0, but it's
        /// cancelled by a - 1 since the last level doesn't compact to anything.
        /// FIXME: We might not want the memory overhead for the context. Let's work out what it is first.
        ///       As of very early on - ~2kb per compaction, so ~16kb per tree
        compactions: [constants.lsm_levels]Compaction,

        /// While a compaction is running, this is the op of the last compact().
        /// While no compaction is running, this is the op of the last compact() to complete.
        /// (When recovering from a checkpoint, compaction_op starts at op_checkpoint).
        compaction_op: ?u64 = null,

        tracer_slot: ?tracer.SpanStart = null,

        active_scope: ?TableMemory.ValueContext = null,

        /// The range of keys in this tree at snapshot_latest.
        key_range: ?KeyRange = null,

        /// (Constructed by the Forest.)
        pub const Config = TreeConfig;

        /// (Constructed by the StateMachine.)
        pub const Options = struct {
            // No options currently.
        };

        pub fn init(
            allocator: mem.Allocator,
            node_pool: *NodePool,
            grid: *Grid,
            config: Config,
            options: Options,
        ) !Tree {
            assert(grid.superblock.opened);
            assert(config.id != 0); // id=0 is reserved.
            assert(config.name.len > 0);

            var table_mutable = try TableMemory.init(allocator, .mutable, config.name);
            errdefer table_mutable.deinit(allocator);

            var table_immutable = try TableMemory.init(
                allocator,
                .{ .immutable = .{} },
                config.name,
            );
            errdefer table_immutable.deinit(allocator);

            var manifest = try Manifest.init(allocator, node_pool, config);
            errdefer manifest.deinit(allocator);

            var compactions: [constants.lsm_levels]Compaction = undefined;

            for (0..compactions.len) |i| {
                errdefer for (compactions[0..i]) |*c| c.deinit();
                compactions[i] = try Compaction.init(config, grid, @intCast(i));
            }
            errdefer for (compactions) |*c| c.deinit();

            return Tree{
                .grid = grid,
                .config = config,
                .options = options,
                .table_mutable = table_mutable,
                .table_immutable = table_immutable,
                .manifest = manifest,
                .compactions = compactions,
            };
        }

        pub fn deinit(tree: *Tree, allocator: mem.Allocator) void {
            assert(tree.tracer_slot == null);

            for (&tree.compactions) |*compaction| compaction.deinit();

            // TODO Consider whether we should release blocks acquired from Grid.block_free_set.
            tree.manifest.deinit(allocator);
            tree.table_immutable.deinit(allocator);
            tree.table_mutable.deinit(allocator);
        }

        pub fn reset(tree: *Tree) void {
            tree.table_mutable.reset();
            tree.table_immutable.reset();
            tree.manifest.reset();

            for (&tree.compactions) |*compaction| compaction.reset();

            tree.* = .{
                .grid = tree.grid,
                .config = tree.config,
                .options = tree.options,
                .table_mutable = tree.table_mutable,
                .table_immutable = tree.table_immutable,
                .manifest = tree.manifest,
                .compactions = tree.compactions,
            };
        }

        /// Open a new scope. Within a scope, changes can be persisted
        /// or discarded. Only one scope can be active at a time.
        pub fn scope_open(tree: *Tree) void {
            assert(tree.active_scope == null);
            tree.active_scope = tree.table_mutable.value_context;
        }

        pub fn scope_close(tree: *Tree, mode: ScopeCloseMode) void {
            assert(tree.active_scope != null);
            assert(tree.active_scope.?.count <= tree.table_mutable.value_context.count);

            if (mode == .discard) {
                tree.table_mutable.value_context = tree.active_scope.?;
            }

            tree.active_scope = null;
        }

        pub fn put(tree: *Tree, value: *const Value) void {
            tree.table_mutable.put(value);
        }

        pub fn remove(tree: *Tree, value: *const Value) void {
            tree.table_mutable.put(&Table.tombstone_from_key(Table.key_from_value(value)));
        }

        pub fn key_range_update(tree: *Tree, key: Key) void {
            if (tree.key_range) |*key_range| {
                if (key < key_range.key_min) key_range.key_min = key;
                if (key > key_range.key_max) key_range.key_max = key;
            } else {
                tree.key_range = KeyRange{ .key_min = key, .key_max = key };
            }
        }

        /// Returns True if the given key may be present in the Tree, False if the key is
        /// guaranteed to not be present.
        ///
        /// Specifically, it checks whether the key exists within the Tree's key range.
        pub fn key_range_contains(tree: *const Tree, snapshot: u64, key: Key) bool {
            if (snapshot == snapshot_latest) {
                return tree.key_range != null and
                    tree.key_range.?.key_min <= key and
                    key <= tree.key_range.?.key_max;
            } else {
                return true;
            }
        }

        /// This function is intended to never be called by regular code. It only
        /// exists for fuzzing, due to the performance overhead it carries. Real
        /// code must rely on the Groove cache for lookups.
        /// The returned Value pointer is only valid synchronously.
        pub fn lookup_from_memory(tree: *Tree, key: Key) ?*const Value {
            assert(constants.verify);

            return tree.table_mutable.get(key) orelse tree.table_immutable.get(key);
        }

        /// Returns:
        /// - .negative if the key does not exist in the Manifest.
        /// - .positive if the key exists in the Manifest, along with the associated value.
        /// - .possible if the key may exist in the Manifest but its existence cannot be
        ///  ascertained without IO, along with the level number at which IO must be performed.
        ///
        /// This function attempts to fetch the index & data blocks for the tables that
        /// could contain the key synchronously from the Grid cache. It then attempts to ascertain
        /// the existence of the key in the data block. If any of the blocks needed to
        /// ascertain the existence of the key are not in the Grid cache, it bails out.
        /// The returned `.positive` Value pointer is only valid synchronously.
        pub fn lookup_from_levels_cache(tree: *Tree, snapshot: u64, key: Key) LookupMemoryResult {
            var iterator = tree.manifest.lookup(snapshot, key, 0);
            while (iterator.next()) |table| {
                const index_block = tree.grid.read_block_from_cache(
                    table.address,
                    table.checksum,
                    .{ .coherent = true },
                ) orelse {
                    // Index block not in cache. We cannot rule out existence without I/O,
                    // and therefore bail out.
                    return .{ .possible = iterator.level - 1 };
                };

                const key_blocks = Table.index_blocks_for_key(index_block, key) orelse continue;
                switch (tree.cached_data_block_search(
                    key_blocks.data_block_address,
                    key_blocks.data_block_checksum,
                    key,
                )) {
                    .negative => {},
                    // Key present in the data block.
                    .positive => |value| return .{ .positive = value },
                    // Data block was not found in the grid cache. We cannot rule out
                    // the existence of the key without I/O, and therefore bail out.
                    .block_not_in_cache => return .{ .possible = iterator.level - 1 },
                }
            }
            // Key not present in the Manifest.
            return .negative;
        }

        fn cached_data_block_search(
            tree: *Tree,
            address: u64,
            checksum: u128,
            key: Key,
        ) union(enum) {
            positive: *const Value,
            negative,
            block_not_in_cache,
        } {
            if (tree.grid.read_block_from_cache(
                address,
                checksum,
                .{ .coherent = true },
            )) |data_block| {
                if (Table.data_block_search(data_block, key)) |value| {
                    return .{ .positive = value };
                } else {
                    return .negative;
                }
            } else {
                return .block_not_in_cache;
            }
        }

        /// Call this function only after checking `lookup_from_memory()`.
        /// The callback's Value pointer is only valid synchronously within the callback.
        pub fn lookup_from_levels_storage(tree: *Tree, parameters: struct {
            callback: *const fn (*LookupContext, ?*const Value) void,
            context: *LookupContext,
            snapshot: u64,
            key: Key,
            level_min: u8,
        }) void {
            var index_block_count: u8 = 0;
            var index_block_addresses: [constants.lsm_levels]u64 = undefined;
            var index_block_checksums: [constants.lsm_levels]u128 = undefined;
            {
                var it = tree.manifest.lookup(
                    parameters.snapshot,
                    parameters.key,
                    parameters.level_min,
                );
                while (it.next()) |table| : (index_block_count += 1) {
                    assert(table.visible(parameters.snapshot));
                    assert(table.key_min <= parameters.key);
                    assert(parameters.key <= table.key_max);

                    index_block_addresses[index_block_count] = table.address;
                    index_block_checksums[index_block_count] = table.checksum;
                }
            }

            if (index_block_count == 0) {
                parameters.callback(parameters.context, null);
                return;
            }

            parameters.context.* = .{
                .tree = tree,
                .completion = undefined,
                .key = parameters.key,
                .index_block_count = index_block_count,
                .index_block_addresses = index_block_addresses,
                .index_block_checksums = index_block_checksums,
                .callback = parameters.callback,
            };

            parameters.context.read_index_block();
        }

        pub const LookupContext = struct {
            const Read = Grid.Read;
            const BlockPtrConst = Grid.BlockPtrConst;

            tree: *Tree,
            completion: Read,

            key: Key,

            /// This value is an index into the index_block_addresses/checksums arrays.
            index_block: u8 = 0,
            index_block_count: u8,
            index_block_addresses: [constants.lsm_levels]u64,
            index_block_checksums: [constants.lsm_levels]u128,

            data_block: ?struct {
                address: u64,
                checksum: u128,
            } = null,

            callback: *const fn (*Tree.LookupContext, ?*const Value) void,

            fn read_index_block(context: *LookupContext) void {
                assert(context.data_block == null);
                assert(context.index_block < context.index_block_count);
                assert(context.index_block_count > 0);
                assert(context.index_block_count <= constants.lsm_levels);

                context.tree.grid.read_block(
                    .{ .from_local_or_global_storage = read_index_block_callback },
                    &context.completion,
                    context.index_block_addresses[context.index_block],
                    context.index_block_checksums[context.index_block],
                    .{ .cache_read = true, .cache_write = true },
                );
            }

            fn read_index_block_callback(completion: *Read, index_block: BlockPtrConst) void {
                const context = @fieldParentPtr(LookupContext, "completion", completion);
                assert(context.data_block == null);
                assert(context.index_block < context.index_block_count);
                assert(context.index_block_count > 0);
                assert(context.index_block_count <= constants.lsm_levels);
                assert(schema.TableIndex.metadata(index_block).tree_id == context.tree.config.id);

                const blocks = Table.index_blocks_for_key(index_block, context.key) orelse {
                    // The key is not present in this table, check the next level.
                    context.advance_to_next_level();
                    return;
                };

                context.data_block = .{
                    .address = blocks.data_block_address,
                    .checksum = blocks.data_block_checksum,
                };

                context.tree.grid.read_block(
                    .{ .from_local_or_global_storage = read_data_block_callback },
                    completion,
                    context.data_block.?.address,
                    context.data_block.?.checksum,
                    .{ .cache_read = true, .cache_write = true },
                );
            }

            fn read_data_block_callback(completion: *Read, data_block: BlockPtrConst) void {
                const context = @fieldParentPtr(LookupContext, "completion", completion);
                assert(context.data_block != null);
                assert(context.index_block < context.index_block_count);
                assert(context.index_block_count > 0);
                assert(context.index_block_count <= constants.lsm_levels);
                assert(schema.TableData.metadata(data_block).tree_id == context.tree.config.id);

                if (Table.data_block_search(data_block, context.key)) |value| {
                    context.callback(context, unwrap_tombstone(value));
                } else {
                    // The key is not present in this table, check the next level.
                    context.advance_to_next_level();
                }
            }

            fn advance_to_next_level(context: *LookupContext) void {
                assert(context.index_block < context.index_block_count);
                assert(context.index_block_count > 0);
                assert(context.index_block_count <= constants.lsm_levels);

                // Data block may be null if the key is not contained in the
                // index block's key range.
                maybe(context.data_block == null);

                context.index_block += 1;
                if (context.index_block == context.index_block_count) {
                    context.callback(context, null);
                    return;
                }
                assert(context.index_block < context.index_block_count);

                context.data_block = null;
                context.read_index_block();
            }
        };

        /// Returns null if the value is null or a tombstone, otherwise returns the value.
        /// We use tombstone values internally, but expose them as null to the user.
        /// This distinction enables us to cache a null result as a tombstone in our hash maps.
        pub inline fn unwrap_tombstone(value: ?*const Value) ?*const Value {
            return if (value == null or tombstone(value.?)) null else value.?;
        }

        pub fn open_commence(tree: *Tree, manifest_log: *ManifestLog) void {
            assert(tree.compaction_op == null);
            assert(tree.key_range == null);

            tree.manifest.open_commence(manifest_log);
        }

        pub fn open_table(
            tree: *Tree,
            table: *const schema.ManifestNode.TableInfo,
        ) void {
            assert(tree.compaction_op == null);
            assert(tree.key_range == null);

            const tree_table = Manifest.TreeTableInfo.decode(table);
            tree.manifest.levels[table.label.level].insert_table(
                tree.manifest.node_pool,
                &tree_table,
            );
        }

        pub fn open_complete(tree: *Tree) void {
            assert(tree.compaction_op == null);
            assert(tree.key_range == null);

            tree.compaction_op = tree.grid.superblock.working.vsr_state.checkpoint.commit_min;
            tree.key_range = tree.manifest.key_range();

            tree.manifest.verify(snapshot_latest);
            assert(tree.compaction_op.? == 0 or
                (tree.compaction_op.? + 1) % constants.lsm_batch_multiple == 0);
            maybe(tree.key_range == null);
        }

        /// Called after the last beat of a full compaction bar, by the compaction instance.
        pub fn swap_mutable_and_immutable(tree: *Tree, snapshot_min: u64) void {
            assert(tree.table_mutable.mutability == .mutable);
            assert(tree.table_immutable.mutability == .immutable);
            assert(tree.table_immutable.mutability.immutable.flushed);
            assert(snapshot_min > 0);
            assert(snapshot_min < snapshot_latest);

            // TODO
            // assert((tree.compaction_op.? + 1) % constants.lsm_batch_multiple == 0);

            // The immutable table must be visible to the next bar.
            // In addition, the immutable table is conceptually an output table of this compaction
            // bar, and now its snapshot_min matches the snapshot_min of the Compactions' output
            // tables.
            tree.table_mutable.make_immutable(snapshot_min);
            tree.table_immutable.make_mutable();
            std.mem.swap(TableMemory, &tree.table_mutable, &tree.table_immutable);

            assert(tree.table_mutable.count() == 0);
            assert(tree.table_mutable.mutability == .mutable);
            assert(tree.table_immutable.mutability == .immutable);
        }
    };
}

/// The total number of tables that can be supported by the tree across so many levels.
pub fn table_count_max_for_tree(growth_factor: u32, levels_count: u32) u32 {
    assert(growth_factor >= 4);
    assert(growth_factor <= 16); // Limit excessive write amplification.
    assert(levels_count >= 2);
    assert(levels_count <= 10); // Limit excessive read amplification.
    assert(levels_count <= constants.lsm_levels);

    var count: u32 = 0;
    var level: u32 = 0;
    while (level < levels_count) : (level += 1) {
        count += table_count_max_for_level(growth_factor, level);
    }
    return count;
}

/// The total number of tables that can be supported by the level alone.
pub fn table_count_max_for_level(growth_factor: u32, level: u32) u32 {
    assert(level >= 0);
    assert(level < constants.lsm_levels);

    return math.pow(u32, growth_factor, level + 1);
}

test "table_count_max_for_level/tree" {
    const expectEqual = std.testing.expectEqual;

    try expectEqual(@as(u32, 8), table_count_max_for_level(8, 0));
    try expectEqual(@as(u32, 64), table_count_max_for_level(8, 1));
    try expectEqual(@as(u32, 512), table_count_max_for_level(8, 2));
    try expectEqual(@as(u32, 4096), table_count_max_for_level(8, 3));
    try expectEqual(@as(u32, 32768), table_count_max_for_level(8, 4));
    try expectEqual(@as(u32, 262144), table_count_max_for_level(8, 5));
    try expectEqual(@as(u32, 2097152), table_count_max_for_level(8, 6));

    try expectEqual(@as(u32, 8 + 64), table_count_max_for_tree(8, 2));
    try expectEqual(@as(u32, 72 + 512), table_count_max_for_tree(8, 3));
    try expectEqual(@as(u32, 584 + 4096), table_count_max_for_tree(8, 4));
    try expectEqual(@as(u32, 4680 + 32768), table_count_max_for_tree(8, 5));
    try expectEqual(@as(u32, 37448 + 262144), table_count_max_for_tree(8, 6));
    try expectEqual(@as(u32, 299592 + 2097152), table_count_max_for_tree(8, 7));
}

test "TreeType" {
    const CompositeKey = @import("composite_key.zig").CompositeKeyType(u64);
    const Table = @import("table.zig").TableType(
        CompositeKey.Key,
        CompositeKey,
        CompositeKey.key_from_value,
        CompositeKey.sentinel_key,
        CompositeKey.tombstone,
        CompositeKey.tombstone_from_key,
        constants.state_machine_config.lsm_batch_multiple * 1024,
        .secondary_index,
    );

    const Storage = @import("../storage.zig").Storage;
    std.testing.refAllDecls(TreeType(Table, Storage));
}
