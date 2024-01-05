const std = @import("std");
const builtin = @import("builtin");
const assert = std.debug.assert;
const maybe = stdx.maybe;
const mem = std.mem;
const log = std.log.scoped(.forest);

const stdx = @import("../stdx.zig");
const constants = @import("../constants.zig");
const vsr = @import("../vsr.zig");

const schema = @import("schema.zig");
const GridType = @import("../vsr/grid.zig").GridType;
const BlockPtr = @import("../vsr/grid.zig").BlockPtr;
const allocate_block = @import("../vsr/grid.zig").allocate_block;
const NodePool = @import("node_pool.zig").NodePool(constants.lsm_manifest_node_size, 16);
const ManifestLogType = @import("manifest_log.zig").ManifestLogType;
const ScanBufferPool = @import("scan_buffer.zig").ScanBufferPool;
const CompactionInfo = @import("compaction.zig").CompactionInfo;

const table_count_max = @import("tree.zig").table_count_max;

pub fn ForestType(comptime _Storage: type, comptime groove_cfg: anytype) type {
    var groove_fields: []const std.builtin.Type.StructField = &.{};
    var groove_options_fields: []const std.builtin.Type.StructField = &.{};

    for (std.meta.fields(@TypeOf(groove_cfg))) |field| {
        const Groove = @field(groove_cfg, field.name);
        groove_fields = groove_fields ++ [_]std.builtin.Type.StructField{
            .{
                .name = field.name,
                .type = Groove,
                .default_value = null,
                .is_comptime = false,
                .alignment = @alignOf(Groove),
            },
        };

        groove_options_fields = groove_options_fields ++ [_]std.builtin.Type.StructField{
            .{
                .name = field.name,
                .type = Groove.Options,
                .default_value = null,
                .is_comptime = false,
                .alignment = @alignOf(Groove),
            },
        };
    }

    const _Grooves = @Type(.{
        .Struct = .{
            .layout = .Auto,
            .fields = groove_fields,
            .decls = &.{},
            .is_tuple = false,
        },
    });

    const _GroovesOptions = @Type(.{
        .Struct = .{
            .layout = .Auto,
            .fields = groove_options_fields,
            .decls = &.{},
            .is_tuple = false,
        },
    });

    {
        // Verify that every tree id is unique.
        comptime var ids: []const u16 = &.{};

        inline for (std.meta.fields(_Grooves)) |groove_field| {
            const Groove = groove_field.type;

            for (std.meta.fields(@TypeOf(Groove.config.ids))) |field| {
                const id = @field(Groove.config.ids, field.name);
                assert(id > 0);
                assert(std.mem.indexOfScalar(u16, ids, id) == null);

                ids = ids ++ [_]u16{id};
            }
        }
    }

    const TreeInfo = struct {
        Tree: type,
        tree_name: []const u8,
        tree_id: u16,
        groove_name: []const u8,
        groove_tree: union(enum) { objects, ids, indexes: []const u8 },
    };

    // Invariants:
    // - tree_infos[tree_id - tree_id_range.min].tree_id == tree_id
    // - tree_infos.len == tree_id_range.max - tree_id_range.min
    const _tree_infos: []const TreeInfo = tree_infos: {
        var tree_infos: []const TreeInfo = &[_]TreeInfo{};
        for (std.meta.fields(_Grooves)) |groove_field| {
            const Groove = groove_field.type;

            tree_infos = tree_infos ++ &[_]TreeInfo{.{
                .Tree = Groove.ObjectTree,
                .tree_name = groove_field.name,
                .tree_id = @field(Groove.config.ids, "timestamp"),
                .groove_name = groove_field.name,
                .groove_tree = .objects,
            }};

            if (Groove.IdTree != void) {
                tree_infos = tree_infos ++ &[_]TreeInfo{.{
                    .Tree = Groove.IdTree,
                    .tree_name = groove_field.name ++ ".id",
                    .tree_id = @field(Groove.config.ids, "id"),
                    .groove_name = groove_field.name,
                    .groove_tree = .ids,
                }};
            }

            for (std.meta.fields(Groove.IndexTrees)) |tree_field| {
                tree_infos = tree_infos ++ &[_]TreeInfo{.{
                    .Tree = tree_field.type,
                    .tree_name = groove_field.name ++ "." ++ tree_field.name,
                    .tree_id = @field(Groove.config.ids, tree_field.name),
                    .groove_name = groove_field.name,
                    .groove_tree = .{ .indexes = tree_field.name },
                }};
            }
        }

        var tree_id_min = std.math.maxInt(u16);
        for (tree_infos) |tree_info| tree_id_min = @min(tree_id_min, tree_info.tree_id);

        var tree_infos_sorted: [tree_infos.len]TreeInfo = undefined;
        var tree_infos_set = std.StaticBitSet(tree_infos.len).initEmpty();
        for (tree_infos) |tree_info| {
            const tree_index = tree_info.tree_id - tree_id_min;
            assert(!tree_infos_set.isSet(tree_index));

            tree_infos_sorted[tree_index] = tree_info;
            tree_infos_set.set(tree_index);
        }

        // There are no gaps in the tree ids.
        assert(tree_infos_set.count() == tree_infos.len);

        break :tree_infos tree_infos_sorted[0..];
    };

    // FIXME: How could we move these into compaction.zig?
    const CompactionDispatcher = T: {
        var type_info = @typeInfo(union(enum) {});

        // Union fields for each compaction type.
        for (_tree_infos) |tree_info| {
            const Compaction = tree_info.Tree.Compaction;
            // @compileLog(@typeName(tree_info.Tree));
            // @compileLog(@typeName(Compaction));
            const type_name = @typeName(Compaction);

            for (type_info.Union.fields) |field| {
                if (std.mem.eql(u8, field.name, type_name)) {
                    break;
                }
            } else {
                type_info.Union.fields = type_info.Union.fields ++ [_]std.builtin.Type.UnionField{.{
                    .name = type_name,
                    .type = *Compaction,
                    .alignment = @alignOf(*Compaction),
                }};
            }
        }

        // We need a tagged union for dynamic dispatching.
        type_info.Union.tag_type = blk: {
            const union_fields = type_info.Union.fields;
            var tag_fields: [union_fields.len]std.builtin.Type.EnumField =
                undefined;
            for (&tag_fields, union_fields, 0..) |*tag_field, union_field, i| {
                tag_field.* = .{
                    .name = union_field.name,
                    .value = i,
                };
            }

            break :blk @Type(.{ .Enum = .{
                .tag_type = std.math.IntFittingRange(0, tag_fields.len - 1),
                .fields = &tag_fields,
                .decls = &.{},
                .is_exhaustive = true,
            } });
        };

        break :T @Type(type_info);
    };

    const Grid = GridType(_Storage);

    const CompactionInterface = struct {
        dispatcher: CompactionDispatcher,
        info: CompactionInfo,

        pub fn init(info: CompactionInfo, compaction: anytype) @This() {
            const Compaction = @TypeOf(compaction.*);
            const type_name = @typeName(Compaction);

            return .{
                .info = info,
                .dispatcher = @unionInit(CompactionDispatcher, type_name, compaction),
            };
        }

        pub fn beat_setup(self: *const @This(), blocks: []BlockPtr, grid_reads: []Grid.FatRead, grid_writes: []Grid.FatWrite) void {
            return switch (self.dispatcher) {
                inline else => |compaction_impl| compaction_impl.beat_setup(blocks, grid_reads, grid_writes),
            };
        }

        pub fn blip_read(self: *const @This(), callback: *const fn (*anyopaque, u64, u64) void) void {
            return switch (self.dispatcher) {
                inline else => |compaction_impl| compaction_impl.blip_read(callback),
            };
        }

        pub fn blip_cpu(self: *const @This()) void {
            return switch (self.dispatcher) {
                inline else => |compaction_impl| compaction_impl.blip_cpu(),
            };
        }

        pub fn blip_write(self: *const @This()) void {
            return switch (self.dispatcher) {
                inline else => |compaction_impl| compaction_impl.blip_write(),
            };
        }

        pub fn beat_finish(self: *const @This()) void {
            return switch (self.dispatcher) {
                inline else => |compaction_impl| compaction_impl.beat_finish(),
            };
        }
    };

    return struct {
        const Forest = @This();

        const ManifestLog = ManifestLogType(Storage);

        const Callback = *const fn (*Forest) void;
        const GroovesBitSet = std.StaticBitSet(std.meta.fields(Grooves).len);

        pub const Storage = _Storage;
        pub const groove_config = groove_cfg;
        pub const Grooves = _Grooves;
        pub const GroovesOptions = _GroovesOptions;
        pub const tree_infos = _tree_infos;
        pub const tree_id_range = .{
            .min = tree_infos[0].tree_id,
            .max = tree_infos[tree_infos.len - 1].tree_id,
        };

        progress: ?union(enum) {
            open: struct { callback: Callback },
            checkpoint: struct { callback: Callback },
            compact: struct {
                op: u64,
                callback: Callback,
            },
        } = null,
        bar_compactions: stdx.BoundedArray(CompactionInterface, (tree_id_range.max - tree_id_range.min) * constants.lsm_levels) = .{},

        grid: *Grid,
        grooves: Grooves,
        node_pool: *NodePool,
        manifest_log: ManifestLog,
        manifest_log_progress: enum { idle, compacting, done, skip } = .idle,

        compaction_blocks: []BlockPtr,
        compaction_reads: []Grid.FatRead,
        compaction_writes: []Grid.FatWrite,

        scan_buffer_pool: ScanBufferPool,

        pub fn init(
            allocator: mem.Allocator,
            grid: *Grid,
            node_count: u32,
            // (e.g.) .{ .transfers = .{ .cache_entries_max = 128, … }, .accounts = … }
            grooves_options: GroovesOptions,
        ) !Forest {
            // NodePool must be allocated to pass in a stable address for the Grooves.
            const node_pool = try allocator.create(NodePool);
            errdefer allocator.destroy(node_pool);

            // TODO: look into using lsm_table_size_max for the node_count.
            node_pool.* = try NodePool.init(allocator, node_count);
            errdefer node_pool.deinit(allocator);

            var manifest_log = try ManifestLog.init(allocator, grid, .{
                .tree_id_min = tree_id_range.min,
                .tree_id_max = tree_id_range.max,
                // TODO Make this a runtime argument (from the CLI, derived from storage-size-max if
                // possible).
                .forest_table_count_max = table_count_max,
            });
            errdefer manifest_log.deinit(allocator);

            var grooves: Grooves = undefined;
            var grooves_initialized: usize = 0;

            errdefer inline for (std.meta.fields(Grooves), 0..) |field, field_index| {
                if (grooves_initialized >= field_index + 1) {
                    @field(grooves, field.name).deinit(allocator);
                }
            };

            inline for (std.meta.fields(Grooves)) |groove_field| {
                const groove = &@field(grooves, groove_field.name);
                const Groove = @TypeOf(groove.*);
                const groove_options: Groove.Options = @field(grooves_options, groove_field.name);

                groove.* = try Groove.init(allocator, node_pool, grid, groove_options);
                grooves_initialized += 1;
            }

            const compaction_blocks = try allocator.alloc(BlockPtr, 1024);
            errdefer allocator.free(compaction_blocks);

            for (compaction_blocks, 0..) |*cache_block, i| {
                errdefer for (compaction_blocks[0..i]) |block| allocator.free(block);
                cache_block.* = try allocate_block(allocator);
            }
            errdefer for (compaction_blocks) |block| allocator.free(block);

            const compaction_reads = try allocator.alloc(Grid.FatRead, 1024);
            errdefer allocator.free(compaction_reads);

            const compaction_writes = try allocator.alloc(Grid.FatWrite, 1024);
            errdefer allocator.free(compaction_writes);

            const scan_buffer_pool = try ScanBufferPool.init(allocator);
            errdefer scan_buffer_pool.deinit(allocator);

            return Forest{
                .grid = grid,
                .grooves = grooves,
                .node_pool = node_pool,
                .manifest_log = manifest_log,

                .compaction_blocks = compaction_blocks,
                .compaction_reads = compaction_reads,
                .compaction_writes = compaction_writes,

                .scan_buffer_pool = scan_buffer_pool,
            };
        }

        pub fn deinit(forest: *Forest, allocator: mem.Allocator) void {
            inline for (std.meta.fields(Grooves)) |field| {
                @field(forest.grooves, field.name).deinit(allocator);
            }

            forest.manifest_log.deinit(allocator);
            forest.node_pool.deinit(allocator);
            allocator.destroy(forest.node_pool);

            // FIXME: Deinit compaction_blocks
            forest.scan_buffer_pool.deinit(allocator);
        }

        pub fn reset(forest: *Forest) void {
            inline for (std.meta.fields(Grooves)) |field| {
                @field(forest.grooves, field.name).reset();
            }

            forest.manifest_log.reset();
            forest.node_pool.reset();
            forest.scan_buffer_pool.reset();

            forest.* = .{
                // Don't reset the grid – replica is responsible for grid cancellation.
                .grid = forest.grid,
                .grooves = forest.grooves,
                .node_pool = forest.node_pool,
                .manifest_log = forest.manifest_log,

                .compaction_blocks = forest.compaction_blocks,
                .compaction_reads = forest.compaction_reads,
                .compaction_writes = forest.compaction_writes,

                .scan_buffer_pool = forest.scan_buffer_pool,
            };
        }

        pub fn open(forest: *Forest, callback: Callback) void {
            assert(forest.progress == null);
            assert(forest.manifest_log_progress == .idle);

            forest.progress = .{ .open = .{ .callback = callback } };

            inline for (std.meta.fields(Grooves)) |field| {
                @field(forest.grooves, field.name).open_commence(&forest.manifest_log);
            }

            forest.manifest_log.open(manifest_log_open_event, manifest_log_open_callback);
        }

        fn manifest_log_open_event(
            manifest_log: *ManifestLog,
            table: *const schema.ManifestNode.TableInfo,
        ) void {
            const forest = @fieldParentPtr(Forest, "manifest_log", manifest_log);
            assert(forest.progress.? == .open);
            assert(forest.manifest_log_progress == .idle);
            assert(table.label.level < constants.lsm_levels);
            assert(table.label.event != .remove);

            switch (table.tree_id) {
                inline tree_id_range.min...tree_id_range.max => |tree_id| {
                    var tree: *TreeForIdType(tree_id) = forest.tree_for_id(tree_id);
                    tree.open_table(table);
                },
                else => {
                    log.err("manifest_log_open_event: unknown table in manifest: {}", .{table});
                    @panic("Forest.manifest_log_open_event: unknown table in manifest");
                },
            }
        }

        fn manifest_log_open_callback(manifest_log: *ManifestLog) void {
            const forest = @fieldParentPtr(Forest, "manifest_log", manifest_log);
            assert(forest.progress.? == .open);
            assert(forest.manifest_log_progress == .idle);
            forest.verify_tables_recovered();

            inline for (std.meta.fields(Grooves)) |field| {
                @field(forest.grooves, field.name).open_complete();
            }
            forest.verify_table_extents();

            const callback = forest.progress.?.open.callback;
            forest.progress = null;
            callback(forest);
        }

        pub fn compact(forest: *Forest, callback: Callback, op: u64) void {
            const compaction_beat = op % constants.lsm_batch_multiple;

            // Note: The first beat of the first bar is a special case. It has op 1, and so
            // no bar_setup is called. bar_finish compensates for this internally currently.
            const first_beat = compaction_beat == 0;
            const last_beat = compaction_beat == constants.lsm_batch_multiple - 1;

            // Setup loop, runs only on the first beat of every bar, before any async work is done.
            if (first_beat) {
                assert(forest.bar_compactions.count() == 0);

                inline for (0..constants.lsm_levels) |level_b| {
                    inline for (tree_id_range.min..tree_id_range.max) |tree_id| {
                        var tree = tree_for_id(forest, tree_id);
                        assert(tree.compactions.len == constants.lsm_levels);

                        var compaction = &tree.compactions[level_b];

                        std.log.info("Target Level: {}, Tree: {s}@{}", .{ level_b, tree.config.name, op });

                        // This will return how many compactions and stuff this level needs to do...
                        const maybe_info = compaction.bar_setup(tree, op, forest);
                        if (maybe_info) |info| {
                            // FIXME: Assert len?
                            forest.bar_compactions.append_assume_capacity(CompactionInterface.init(info, compaction));
                            std.log.info("... need to do: {?}", .{info});

                            // FIXME: Move this outside the loop since we need to do it once we know everyhthing we must do.
                            // +1 for len to count
                            compaction.bar_setup_budget(constants.lsm_batch_multiple - 1, forest.compaction_blocks[1000..1024]);
                        } else {
                            std.log.info("... nothing to do", .{});
                        }
                    }
                }
            }

            const compactions = &forest.bar_compactions;
            // Compaction only starts > lsm_batch_multiple because nothing compacts in the first bar.
            if (op > constants.lsm_batch_multiple) {
                for (compactions.slice()) |compaction| {
                    // Then we'll set up the beat depending on what buffers we have available.
                    _ = compaction.beat_setup(
                        forest.compaction_blocks[0..1000],
                        forest.compaction_reads,
                        forest.compaction_writes,
                    );
                    // compaction.blip_read(Forest.blip_callback);
                    // compaction.blip_cpu();
                    // compaction.blip_write();

                    compaction.beat_finish();
                }
            }

            // Finish loop, runs only on the last beat of every bar, after all async work is done.
            // FIXME: This will need to be split oujt into _finish
            if (last_beat) {
                inline for (0..constants.lsm_levels) |level_b| {
                    inline for (tree_id_range.min..tree_id_range.max) |tree_id| {
                        var tree = tree_for_id(forest, tree_id);
                        assert(tree.compactions.len == constants.lsm_levels);

                        var compaction = &tree.compactions[level_b];
                        compaction.bar_finish(op, tree);
                    }
                }

                // FIXME: actually it shoujld pop and we should assert len == 0.
                forest.bar_compactions.clear();
            }

            // Groove sync compaction - must be done after all async work for the beat completes???
            inline for (std.meta.fields(Grooves)) |field| {
                @field(forest.grooves, field.name).compact(op);
            }

            if (op % @divExact(constants.lsm_batch_multiple, 2) == 0) {
                assert(forest.manifest_log_progress == .idle);

                forest.manifest_log_progress = .compacting;
                // FIXME - manifest log reservation needs to be brought in with the above somehow
                // forest.manifest_log.compact(compact_manifest_log_callback, op);
            } else {
                if (op == 1) {
                    assert(forest.manifest_log_progress == .idle);
                    forest.manifest_log_progress = .skip;
                } else {
                    assert(forest.manifest_log_progress != .idle);
                    // FIXME manifest hack
                    forest.manifest_log_progress = .skip;
                }
            }

            forest.progress = .{ .compact = .{
                .op = op,
                .callback = callback,
            } };

            forest.compact_callback();
        }

        fn blip_callback(forest_opaque: *anyopaque, tree_id: u64, level_b: u64) void {
            var forest: *Forest = @ptrCast(@alignCast(forest_opaque));

            std.log.info("Blip callback for: {*} {} {}", .{ forest, tree_id, level_b });
        }

        // FIXME: This mixes both manifest and non-manifest compaction
        fn compact_callback(forest: *Forest) void {
            assert(forest.progress.? == .compact);
            assert(forest.manifest_log_progress != .idle);
            forest.verify_table_extents();

            const progress = &forest.progress.?.compact;

            const half_bar_end =
                (progress.op + 1) % @divExact(constants.lsm_batch_multiple, 2) == 0;
            // On the last beat of the bar, make sure that manifest log compaction is finished.
            if (half_bar_end and forest.manifest_log_progress == .compacting) return;

            // FIXME
            // inline for (std.meta.fields(Grooves)) |field| {
            //     @field(forest.grooves, field.name).compact_end();
            // }

            if (half_bar_end) {
                switch (forest.manifest_log_progress) {
                    .idle => unreachable,
                    .compacting => unreachable,
                    .done => forest.manifest_log.compact_end(),
                    .skip => {},
                }
                forest.manifest_log_progress = .idle;
            }

            const callback = progress.callback;
            forest.progress = null;
            callback(forest);
        }

        fn compact_manifest_log_callback(manifest_log: *ManifestLog) void {
            const forest = @fieldParentPtr(Forest, "manifest_log", manifest_log);
            assert(forest.manifest_log_progress == .compacting);

            forest.manifest_log_progress = .done;

            if (forest.progress) |progress| {
                assert(progress == .compact);

                forest.compact_callback();
            } else {
                // The manifest log compaction completed between compaction beats.
            }
        }

        fn GrooveFor(comptime groove_field_name: []const u8) type {
            const groove_field = @field(std.meta.FieldEnum(Grooves), groove_field_name);
            return std.meta.FieldType(Grooves, groove_field);
        }

        pub fn checkpoint(forest: *Forest, callback: Callback) void {
            assert(forest.progress == null);
            assert(forest.manifest_log_progress == .idle);
            forest.grid.assert_only_repairing();
            forest.verify_table_extents();

            forest.progress = .{ .checkpoint = .{ .callback = callback } };

            inline for (std.meta.fields(Grooves)) |field| {
                @field(forest.grooves, field.name).assert_between_bars();
            }

            forest.manifest_log.checkpoint(checkpoint_manifest_log_callback);
        }

        fn checkpoint_manifest_log_callback(manifest_log: *ManifestLog) void {
            const forest = @fieldParentPtr(Forest, "manifest_log", manifest_log);
            assert(forest.progress.? == .checkpoint);
            assert(forest.manifest_log_progress == .idle);
            forest.grid.assert_only_repairing();
            forest.verify_table_extents();
            forest.verify_tables_recovered();

            const callback = forest.progress.?.checkpoint.callback;
            forest.progress = null;
            callback(forest);
        }

        fn TreeForIdType(comptime tree_id: u16) type {
            const tree_info = tree_infos[tree_id - tree_id_range.min];
            assert(tree_info.tree_id == tree_id);

            return tree_info.Tree;
        }

        pub fn tree_for_id(forest: *Forest, comptime tree_id: u16) *TreeForIdType(tree_id) {
            const tree_info = tree_infos[tree_id - tree_id_range.min];
            assert(tree_info.tree_id == tree_id);

            var groove = &@field(forest.grooves, tree_info.groove_name);

            switch (tree_info.groove_tree) {
                .objects => return &groove.objects,
                .ids => return &groove.ids,
                .indexes => |index_name| return &@field(groove.indexes, index_name),
            }
        }

        pub fn tree_for_id_const(
            forest: *const Forest,
            comptime tree_id: u16,
        ) *const TreeForIdType(tree_id) {
            const tree_info = tree_infos[tree_id - tree_id_range.min];
            assert(tree_info.tree_id == tree_id);

            const groove = &@field(forest.grooves, tree_info.groove_name);

            switch (tree_info.groove_tree) {
                .objects => return &groove.objects,
                .ids => return &groove.ids,
                .indexes => |index_name| return &@field(groove.indexes, index_name),
            }
        }

        /// Verify that `ManifestLog.table_extents` has an extent for every active table.
        ///
        /// (Invoked between beats.)
        fn verify_table_extents(forest: *const Forest) void {
            var tables_count: usize = 0;
            inline for (tree_id_range.min..tree_id_range.max + 1) |tree_id| {
                for (0..constants.lsm_levels) |level| {
                    const tree_level = forest.tree_for_id_const(tree_id).manifest.levels[level];
                    tables_count += tree_level.tables.len();

                    if (constants.verify) {
                        var tables_iterator = tree_level.tables.iterator_from_index(0, .ascending);
                        while (tables_iterator.next()) |table| {
                            assert(forest.manifest_log.table_extents.get(table.address) != null);
                        }
                    }
                }
            }
            assert(tables_count == forest.manifest_log.table_extents.count());
        }

        /// Verify the tables recovered into the ManifestLevels after opening the manifest log.
        ///
        /// There are two strategies to reconstruct the LSM's manifest levels (i.e. the list of
        /// tables) from a superblock manifest:
        ///
        /// 1. Iterate the manifest events in chronological order, replaying each
        ///    insert/update/remove in sequence.
        /// 2. Iterate the manifest events in reverse-chronological order, ignoring events for
        ///    tables that have already been encountered.
        ///
        /// The manifest levels constructed by each strategy are identical.
        ///
        /// 1. This function implements strategy 1, to validate `ManifestLog.open()`.
        /// 2. `ManifestLog.open()` implements strategy 2.
        ///
        /// (Strategy 2 minimizes the number of ManifestLevel mutations.)
        ///
        /// (Invoked immediately after open() or checkpoint()).
        fn verify_tables_recovered(forest: *const Forest) void {
            const ForestTableIteratorType =
                @import("./forest_table_iterator.zig").ForestTableIteratorType;
            const ForestTableIterator = ForestTableIteratorType(Forest);

            assert(forest.grid.superblock.opened);
            assert(forest.manifest_log.opened);

            if (Forest.Storage != @import("../testing/storage.zig").Storage) return;

            // The manifest log is opened, which means we have all of the manifest blocks.
            // But if the replica is syncing, those blocks might still be writing (and thus not in
            // the TestStorage when we go to retrieve them).
            if (forest.grid.superblock.working.vsr_state.sync_op_max > 0) return;

            // The latest version of each table, keyed by table checksum.
            // Null when the table has been deleted.
            var tables_latest = std.AutoHashMap(u128, struct {
                table: schema.ManifestNode.TableInfo,
                manifest_block: u64,
                manifest_entry: u32,
            }).init(forest.grid.superblock.storage.allocator);
            defer tables_latest.deinit();

            // Replay manifest events in chronological order.
            // Accumulate all tables that belong in the recovered forest's ManifestLevels.
            for (0..forest.manifest_log.log_block_checksums.count) |i| {
                const block_checksum = forest.manifest_log.log_block_checksums.get(i).?;
                const block_address = forest.manifest_log.log_block_addresses.get(i).?;
                assert(block_address > 0);

                const block = forest.grid.superblock.storage.grid_block(block_address).?;
                const block_header = schema.header_from_block(block);
                assert(block_header.address == block_address);
                assert(block_header.checksum == block_checksum);
                assert(block_header.block_type == .manifest);

                const block_schema = schema.ManifestNode.from(block);
                assert(block_schema.entry_count > 0);
                assert(block_schema.entry_count <= schema.ManifestNode.entry_count_max);

                for (block_schema.tables_const(block), 0..) |*table, entry| {
                    if (table.label.event == .remove) {
                        maybe(tables_latest.remove(table.checksum));
                    } else {
                        tables_latest.put(table.checksum, .{
                            .table = table.*,
                            .manifest_block = block_address,
                            .manifest_entry = @intCast(entry),
                        }) catch @panic("oom");
                    }
                }

                if (i > 0) {
                    // Verify the linked-list.
                    const block_previous = schema.ManifestNode.previous(block).?;
                    assert(block_previous.checksum ==
                        forest.manifest_log.log_block_checksums.get(i - 1).?);
                    assert(block_previous.address ==
                        forest.manifest_log.log_block_addresses.get(i - 1).?);
                }
            }

            // Verify that the SuperBlock Manifest's table extents are correct.
            var tables_latest_iterator = tables_latest.valueIterator();
            var table_extent_counts: usize = 0;
            while (tables_latest_iterator.next()) |table| {
                const table_extent = forest.manifest_log.table_extents.get(table.table.address).?;
                assert(table.manifest_block == table_extent.block);
                assert(table.manifest_entry == table_extent.entry);

                table_extent_counts += 1;
            }
            assert(table_extent_counts == forest.manifest_log.table_extents.count());

            // Verify the tables in `tables` are exactly the tables recovered by the Forest.
            var forest_tables_iterator = ForestTableIterator{};
            while (forest_tables_iterator.next(forest)) |forest_table_item| {
                const table_latest = tables_latest.get(forest_table_item.checksum).?;
                assert(table_latest.table.label.level == forest_table_item.label.level);
                assert(std.meta.eql(table_latest.table.key_min, forest_table_item.key_min));
                assert(std.meta.eql(table_latest.table.key_max, forest_table_item.key_max));
                assert(table_latest.table.checksum == forest_table_item.checksum);
                assert(table_latest.table.address == forest_table_item.address);
                assert(table_latest.table.snapshot_min == forest_table_item.snapshot_min);
                assert(table_latest.table.snapshot_max == forest_table_item.snapshot_max);
                assert(table_latest.table.tree_id == forest_table_item.tree_id);

                const table_removed = tables_latest.remove(forest_table_item.checksum);
                assert(table_removed);
            }
            assert(tables_latest.count() == 0);
        }
    };
}
