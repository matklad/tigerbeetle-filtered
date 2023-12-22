//! Compaction moves or merges a table's values from the previous level.
//!
//! Each Compaction is paced to run in an arbitrary amount of beats, by the forest.
//!
//!
//! Compaction overview:
//!
//! 1. Given:
//!
//!   - levels A and B, where A+1=B
//!   - a single table in level A ("table A")
//!   - all tables from level B which intersect table A's key range ("tables B")
//!     (This can include anything between 0 tables and all of level B's tables.)
//!
//! 2. If table A's key range is disjoint from the keys in level B, move table A into level B.
//!    All done! (But if the key ranges intersect, jump to step 3).
//! FIXME: Update
//! 3. Create an iterator from the sort-merge of table A and the concatenation of tables B.
//!    If the same key exists in level A and B, take A's and discard B's. †
//!
//! 4. Write the sort-merge iterator into a sequence of new tables on disk.
//!
//! 5. Update the input tables in the Manifest with their new `snapshot_max` so that they become
//!    invisible to subsequent read transactions.
//!
//! 6. Insert the new level-B tables into the Manifest.
//!
//! † When A's value is a tombstone, there is a special case for garbage collection. When either:
//! * level B is the final level, or
//! * A's key does not exist in B or any deeper level,
//! then the tombstone is omitted from the compacted output, see: `compaction_must_drop_tombstones`.
//!
const std = @import("std");
const mem = std.mem;
const math = std.math;
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const log = std.log.scoped(.compaction);
const tracer = @import("../tracer.zig");

const constants = @import("../constants.zig");

const stdx = @import("../stdx.zig");
const GridType = @import("../vsr/grid.zig").GridType;
const BlockPtr = @import("../vsr/grid.zig").BlockPtr;
const BlockPtrConst = @import("../vsr/grid.zig").BlockPtrConst;
const allocate_block = @import("../vsr/grid.zig").allocate_block;
const TableInfoType = @import("manifest.zig").TreeTableInfoType;
const ManifestType = @import("manifest.zig").ManifestType;
const schema = @import("schema.zig");

/// The upper-bound count of input tables to a single tree's compaction.
///
/// - +1 from level A.
/// - +lsm_growth_factor from level B. The A-input table cannot overlap with an extra B-input table
///   because input table selection is least-overlap. If the input table overlaps on one or both
///   edges, there must be another table with less overlap to select.
pub const compaction_tables_input_max = 1 + constants.lsm_growth_factor;

/// The upper-bound count of output tables from a single tree's compaction.
/// In the "worst" case, no keys are overwritten/merged, and no tombstones are dropped.
pub const compaction_tables_output_max = compaction_tables_input_max;

pub fn CompactionType(
    comptime Table: type,
    comptime Tree: type,
    comptime Storage: type,
) type {
    return struct {
        const Compaction = @This();

        const Grid = GridType(Storage);

        const Manifest = ManifestType(Table, Storage);
        const TableInfo = TableInfoType(Table);
        const TableInfoReference = Manifest.TableInfoReference;
        const CompactionRange = Manifest.CompactionRange;

        const Key = Table.Key;
        const Value = Table.Value;
        const key_from_value = Table.key_from_value;
        const tombstone = Table.tombstone;

        const TableInfoA = union(enum) {
            immutable: []const Value,
            disk: TableInfoReference,
        };

        const CompactionInfo = struct {
            table_info_a: TableInfoA,
            range_b: CompactionRange,
        };

        const Stage = union(enum) {
            /// Not doing anything, no buffers in use.
            idle,
            /// Reading pipeline stage. Given the buffer space we have available, issue as many
            /// reads as possible.
            read,
            /// Merge pipeline stage. Given our input buffers and output buffers, merge as many
            /// values as possible.
            /// FIXME: Interesting aside, we can release our read buffers after the merge step has completed!
            merge,
            /// Write our output buffers to disk.
            write,
            /// We're done!
            exhausted,
        };

        const BarContext = struct {
            tree: *Tree,

            /// `op_min` is the first op/beat of this compaction's half-bar.
            /// `op_min` is used as a snapshot — the compaction's input tables must be visible
            /// to `op_min`.
            ///
            /// After this compaction finishes:
            /// - `op_min + half_bar_beat_count - 1` will be the input tables' snapshot_max.
            /// - `op_min + half_bar_beat_count` will be the output tables' snapshot_min.
            op_min: u64,

            /// Whether this compaction will use the move-table optimization.
            /// Specifically, this field is set to True if the optimal compaction
            /// table in level A can simply be moved to level B.
            move_table: bool,

            table_info_a: TableInfoA,
            range_b: CompactionRange,

            /// Levels may choose to drop tombstones if keys aren't included in the lower levels.
            /// This invariant is always true for the last level as it doesn't have any lower ones.
            drop_tombstones: bool,

            /// Number of beats required to finish this compaction.
            beat_budget: ?u64,

            /// Number of beats we've executed.
            beat_count: u64,

            output_index_blocks: []BlockPtr,

            /// Manifest log appends are queued up until `finish()` is explicitly called to ensure
            /// they are applied deterministically relative to other concurrent compactions.
            manifest_entries: stdx.BoundedArray(struct {
                operation: enum {
                    insert_to_level_b,
                    move_to_level_b,
                },
                table: TableInfo,
            }, manifest_entries_max: {
                // Worst-case manifest updates:
                // See docs/internals/lsm.md "Compaction Table Overlap" for more detail.
                var count = 0;

                count += constants.lsm_growth_factor + 1; // Insert the output tables to level B.
                // (In the move-table case, only a single TableInfo is inserted, and none are updated.)
                break :manifest_entries_max count;
            }) = .{},
        };

        const BeatContext = struct {
            grid_reservation: ?Grid.Reservation,

            input_index_blocks: []BlockPtr,
            input_data_blocks: []BlockPtr,

            output_data_blocks: []BlockPtr,

            grid_reads: []Grid.FatRead,
            grid_writes: []Grid.FatWrite,

            pending_index_reads: usize = 0,
            pending_data_reads: usize = 0,

            pending_writes: usize = 0,
        };

        // Passed by `init`.
        tree_config: Tree.Config,
        level_b: u8,
        grid: *Grid,

        // Allocated during `init`.
        last_keys_in: [2]?Key = .{ null, null },
        table_builder: Table.Builder = .{},

        // Populated by {bar,beat}_setup.
        bar_context: ?BarContext,
        beat_context: ?BeatContext,

        // Used by our next tick helper.
        // blip_next_tick: Grid.NextTick,

        // These point inside either `data_blocks` or `context.table_info_a.immutable`.
        values_in: [2][]const Value,

        pub fn init(tree_config: Tree.Config, grid: *Grid, level_b: u8) !Compaction {
            assert(level_b < constants.lsm_levels);

            return Compaction{
                .tree_config = tree_config,
                .grid = grid,
                .level_b = level_b,

                .bar_context = null,
                .beat_context = null,

                .values_in = .{ &.{}, &.{} },
            };
        }

        pub fn deinit(compaction: *Compaction) void {
            _ = compaction;
        }

        pub fn reset(compaction: *Compaction) void {
            compaction.* = .{
                .tree_config = compaction.tree_config,
                .grid = compaction.grid,
                .level_b = compaction.level_b,

                .bar_context = null,
                .beat_context = null,

                .values_in = .{ &.{}, &.{} },
            };

            // FIXME: Ensure blocks are released...
            compaction.table_builder.reset();
        }

        /// Called per bar
        /// Perform the bar-wise setup, and return information that the forest can use for scheduling.
        /// beat_budget is the number of beats that this compaction will have available to do its work.
        /// A compaction may be done before beat_budget, if eg tables are mostly empty.
        /// Output index blocks are special, and are allocated at a bar level unlike all the other blocks
        /// which are done at a beat level. This is because while we can ensure we fill a data block, index
        /// blocks are too infrequent (one per table) to divide compaction by.
        /// Returns null if there's no compaction work, otherwise returns the compaction work that needs to be done.
        /// move_table is a semi-special case - a non-null value is returned because we still need to do manifest
        /// updates in bar_finish, but we don't need to actually _do_ anything else.
        pub fn bar_setup(compaction: *Compaction, tree: *Tree, op: u64) ?CompactionInfo {
            assert(compaction.bar_context == null);
            assert(compaction.beat_context == null);

            std.log.info("bar_setup running for compaction: {s} into level: {}", .{ compaction.tree_config.name, compaction.level_b });

            // level_b 0 is special; unlike all the others which come from disk, level 0 comes
            // from the immutable table. This means that blip_read will effectively be a noop, and
            // that the minimum input blocks are lowered by one. Don't know if we want to make use
            // of that just yet.
            if (compaction.level_b == 0) {
                // Do not start compaction if the immutable table does not require compaction.
                if (tree.table_immutable.mutability.immutable.flushed) return null;

                const values = tree.table_immutable.values_used();
                const values_count = values.len;
                assert(values_count > 0);

                const range_b = tree.manifest.immutable_table_compaction_range(
                    tree.table_immutable.key_min(),
                    tree.table_immutable.key_max(),
                );

                // +1 to count the immutable table (level A).
                assert(range_b.tables.count() + 1 <= compaction_tables_input_max);
                assert(range_b.key_min <= tree.table_immutable.key_min());
                assert(tree.table_immutable.key_max() <= range_b.key_max);

                // FIXME: Hmm about op_min here
                log.info("{s}: compacting immutable table to level 0 " ++
                    "(snapshot_min={d} compaction.op_min={d} table_count={d} values={d})", .{
                    tree.config.name,
                    tree.table_immutable.mutability.immutable.snapshot_min,
                    op,
                    range_b.tables.count() + 1,
                    values_count,
                });

                compaction.bar_context = .{
                    .tree = tree,
                    .op_min = op,

                    .move_table = false,
                    .table_info_a = .{ .immutable = tree.table_immutable.values_used() },
                    .range_b = range_b,
                    .drop_tombstones = tree.manifest.compaction_must_drop_tombstones(
                        compaction.level_b,
                        range_b,
                    ),

                    // FIXME: Don't like this! How to do it better?
                    .output_index_blocks = undefined,
                    .beat_budget = null,
                    .beat_count = 0,
                };
            } else {
                // Do not start compaction if level A does not require compaction.
                const level_a = compaction.level_b - 1;

                const table_range = tree.manifest.compaction_table(level_a) orelse return null;
                const table_a = table_range.table_a.table_info;
                const range_b = table_range.range_b;

                assert(range_b.tables.count() + 1 <= compaction_tables_input_max);
                assert(table_a.key_min <= table_a.key_max);
                assert(range_b.key_min <= table_a.key_min);
                assert(table_a.key_max <= range_b.key_max);

                log.info("{s}: compacting {d} tables from level {d} to level {d}", .{
                    tree.config.name,
                    range_b.tables.count() + 1,
                    level_a,
                    compaction.level_b,
                });

                const perform_move_table = range_b.tables.empty();
                if (perform_move_table) {
                    compaction.move_table();
                }

                compaction.bar_context = .{
                    .tree = tree,
                    .op_min = op,

                    .move_table = perform_move_table,
                    .table_info_a = .{ .disk = table_range.table_a },
                    .range_b = range_b,
                    .drop_tombstones = tree.manifest.compaction_must_drop_tombstones(
                        compaction.level_b,
                        range_b,
                    ),

                    // FIXME: Don't like this! How to do it better?
                    .output_index_blocks = undefined,
                    .beat_budget = null,
                    .beat_count = 0,
                };
            }

            assert(compaction.bar_context.?.drop_tombstones or compaction.level_b < constants.lsm_levels - 1);

            return .{
                .table_info_a = compaction.bar_context.?.table_info_a,
                .range_b = compaction.bar_context.?.range_b,
            };
        }

        /// Setup the per beat budget, as well as the output index block. Done in a separate step to bar_setup()
        /// since the forest requires information from that step to calculate how it should split the work, and
        /// if there's move table, output_index_blocks must be len 0.
        // Minimum of 1, max lsm_growth_factor+1 of output_index_blocks.
        pub fn bar_setup_budget(compaction: *Compaction, beat_budget: u64, output_index_blocks: []BlockPtr) void {
            assert(compaction.bar_context != null);
            assert(compaction.bar_context.?.beat_budget == null);
            assert(compaction.beat_context == null);

            if (compaction.bar_context.?.move_table) {
                assert(output_index_blocks.len == 0);
                assert(beat_budget == 0);
            } else {
                assert(output_index_blocks.len > 0);
                assert(beat_budget > 0);
            }

            compaction.bar_context.?.beat_budget = beat_budget;
            compaction.bar_context.?.output_index_blocks = output_index_blocks;
        }

        /// Called per beat
        pub fn beat_setup(
            compaction: *Compaction,
            blocks: struct {
                // Actually... All the comments below would be to do _all_ the work required. The max amount to do the work required
                // per beat would then be divided by beat. _however_ the minimums won't change!
                // Minimum of 2, max lsm_growth_factor+1. Replaces index_block_a and index_block_b too.
                // Output index blocks are explicitly handled in bar_setup_budget.
                input_index_blocks: []BlockPtr,
                // Minimum of 2, one from each table. Max would be max possible data blocks in lsm_growth_factor+1 tables.
                input_data_blocks: []BlockPtr,

                // Minimum of 1, max would be max possible data blocks in lsm_growth_factor+1 tables.
                output_data_blocks: []BlockPtr,

                grid_reads: []Grid.FatRead,
                grid_writes: []Grid.FatWrite,
            },
        ) ?void {
            assert(compaction.bar_context != null);
            assert(compaction.beat_context == null);

            const bar_context = compaction.bar_context.?;
            assert(bar_context.beat_budget != null and bar_context.beat_budget.? > 0);
            const beat_budget = bar_context.beat_budget.?;

            // We don't need to assert the maximums, wasted memory, sure, but entirely possible and
            // not harmful.
            assert(blocks.input_index_blocks.len >= 2);
            assert(blocks.input_data_blocks.len >= 2);
            assert(blocks.input_index_blocks.len + blocks.input_data_blocks.len == blocks.grid_reads.len);

            assert(blocks.output_data_blocks.len >= 1);
            assert(bar_context.output_index_blocks.len + blocks.output_data_blocks.len == blocks.grid_writes.len);

            // If we're move_table, the calling code should ensure beat_setup and blip code are never called.
            assert(!bar_context.move_table);

            // Reserve enough blocks to write our output tables in the semi-worst case, where:
            // - no tombstones are dropped,
            // - no values are overwritten,
            // - and we know exact input value counts, so table fullness *is* accounted for.
            //
            // We must reserve before doing any async work so that the block acquisition order
            // is deterministic (relative to other concurrent compactions).
            // We then divide the above by the number of beat counts we're targeting.

            // FIXME: It's a bit more complex to be exactly right. A table will have 1 index block
            // regardless of how many beats we're targeting. We should only divide data blocks?

            // +1 to count the input table from level A.
            // FIXME: Actually take in to account value count from ranges and info.
            const grid_blocks_whole_bar = (bar_context.range_b.tables.count() + 1) * Table.block_count_max;
            const grid_blocks_per_beat = stdx.div_ceil(grid_blocks_whole_bar, beat_budget);

            // TODO The replica must stop accepting requests if it runs out of blocks/capacity,
            // rather than panicking here.
            // (actually, we want to still panic but with something nicer like vsr.fail)
            const grid_reservation = compaction.grid.reserve(grid_blocks_per_beat).?;

            compaction.beat_context = .{
                .grid_reservation = grid_reservation,

                .input_index_blocks = blocks.input_index_blocks,
                .input_data_blocks = blocks.input_data_blocks,
                .output_data_blocks = blocks.output_data_blocks,
                .grid_reads = blocks.grid_reads,
                .grid_writes = blocks.grid_writes,
            };
        }

        /// Perform read IO to fill our input_index_blocks and input_data_blocks with as many blocks
        /// as we can, given their size, and where we are in the amount of work we need to do this beat.
        /// Once we've read in our index blocks, we'll know how many data blocks we have. We can use this to do
        /// more precise pacing than our worst cast in beat_setup(). Specifically, we know exactly how many
        /// input data blocks we'll need to work through, so use that as our pacing metric. This is fixed.
        /// The number of output data blocks / tables will vary based on tombstones and overwites.
        pub fn blip_read(compaction: *Compaction) void {
            // callback: *const fn (*Compaction) void
            // FIXME: Verify the value count matches the number of values we actually compact.
            compaction.blip_read_index();
        }

        fn blip_read_index(compaction: *Compaction) void {
            assert(compaction.bar_context != null);
            assert(compaction.beat_context != null);

            const bar_context = &compaction.bar_context.?;
            const beat_context = &compaction.beat_context.?;

            // index_block_a will always point to input_index_blocks[0] (even though if our source is immutable this isn't needed! future optimization)
            // index_block_b will be the index block of the table we're currently merging with. This will start from the left and move to the right
            // (although we might want to be able to reverse that in future...)

            var read_target: usize = 0;
            switch (bar_context.table_info_a) {
                .disk => |table_ref| {
                    beat_context.grid_reads[read_target].target = compaction;
                    compaction.grid.read_block(
                        .{ .from_local_or_global_storage = blip_read_index_callback },
                        &beat_context.grid_reads[read_target].read,
                        table_ref.table_info.address,
                        table_ref.table_info.checksum,
                        .{ .cache_read = true, .cache_write = true },
                    );
                    beat_context.pending_index_reads += 1;
                    read_target += 1;
                },
                .immutable => {
                    // Immutable values come from the in memory immutable table - no need to do any reads.
                },
            }

            // FIXME: This of course assumes infinite buffer space :)
            for (bar_context.range_b.tables.const_slice()) |table_ref| {
                beat_context.grid_reads[read_target].target = compaction;
                compaction.grid.read_block(
                    .{ .from_local_or_global_storage = blip_read_index_callback },
                    &beat_context.grid_reads[read_target].read,
                    table_ref.table_info.address,
                    table_ref.table_info.checksum,
                    .{ .cache_read = true, .cache_write = true },
                );
                beat_context.pending_index_reads += 1;
                read_target += 1;
            }

            // FIXME: handle pending_index_reads being 0; call our callback via next_tick directly.

            // log.info(
            //     "{s}: Merging table: level_b={}",
            //     .{ compaction.tree_config.name, context.level_b },
            // );
        }

        fn blip_read_index_callback(read: *Grid.Read, block: BlockPtrConst) void {
            const compaction: *Compaction = @alignCast(@ptrCast(@fieldParentPtr(Grid.FatRead, "read", read).target));
            assert(compaction.bar_context != null);
            assert(compaction.beat_context != null);

            const bar_context = &compaction.bar_context.?;
            _ = bar_context;
            const beat_context = &compaction.beat_context.?;
            _ = block;

            // FIXME: Figure out where our read target should go. We can do this by looking at the address and comparing to table_info_a / range_b.

            beat_context.pending_index_reads -= 1;
            if (beat_context.pending_index_reads != 0) return;

            std.log.info("No pending index reads!!", .{});
        }

        fn blip_read_data(compaction: *Compaction) void {
            _ = compaction;
        }

        fn blip_read_data_callback(read: *Grid.Read, block: BlockPtrConst) void {
            const compaction: *Compaction = @alignCast(@ptrCast(@fieldParentPtr(Grid.FatRead, "read", read).target));
            assert(compaction.bar_context != null);
            assert(compaction.beat_context != null);

            const bar_context = &compaction.bar_context.?;
            _ = bar_context;
            const beat_context = &compaction.beat_context.?;
            _ = block;

            beat_context.pending_data_reads -= 1;
            if (beat_context.pending_data_reads != 0) return;
        }

        /// Perform CPU merge work, to transform our input tables to our output tables.
        /// Once this has finished, our read buffers could technically be released, or a
        /// new read started.
        pub fn blip_cpu(compaction: *Compaction) void {
            _ = compaction;
        }

        /// Perform write IO to write our output_index_blocks and output_data_blocks to disk.
        pub fn blip_write(compaction: *Compaction) void {
            _ = compaction;
            // FIXME: From 2023-12-21
            // FIXME: Pace our compaction by input *values* not input blocks. Blocks might be empty, values will be a far better metric.
            // FIXME: Whenever we run and pace compaction, in the one worst case we'll have 9 input tables forming 7 output tables, and the
            // other will be 9 input tables forming 9 output tables. We should assert that we always do this.
            // The other note is that we don't want to hang on to data blocks across beat boundaries, so we'll always end when one is full
            // and not try to be too perfect.
            // FIXME: The big idea is to make compaction pacing explicit and asserted behaviour rather than just an implicit property of the code
        }

        /// Release our IO buffers once all blip iterations are complete.
        pub fn blip_finish(compaction: *Compaction) void {
            _ = compaction;
        }

        fn blip_on_next_tick(next_tick: *Grid.NextTick) void {
            _ = next_tick;
            // const compaction = @fieldParentPtr(Compaction, "blip_next_tick", next_tick);
            // assert(compaction.state == .next_tick);

            // compaction.state = .compacting;
            // compaction.loop_start();
        }

        pub fn beat_finish(compaction: *Compaction) void {
            assert(compaction.bar_context != null);
            assert(compaction.beat_context != null);

            const beat_context = compaction.beat_context.?;

            if (beat_context.grid_reservation) |grid_reservation| {
                std.log.info("forfeiting... {}", .{grid_reservation});
                compaction.grid.forfeit(grid_reservation);
                // We set the whole beat_context to null later.
            } else {
                assert(compaction.bar_context.?.move_table);
            }

            // Our beat is done!
            compaction.beat_context = null;
        }

        /// FIXME: Describe
        pub fn bar_finish(compaction: *Compaction, op: u64, tree: *Tree) void {
            std.log.info("bar_finish running for compaction: {s} into level: {}", .{ compaction.tree_config.name, compaction.level_b });

            // If we're the compaction for immutable -> level 0, we need to swap our mutable / immutable
            // tables too. This needs to happen at the end of the first ever bar, which would normally
            // not have any work to do, so put it before our asserts.
            // FIXME: Do this in a better way
            if (compaction.level_b == 0) {
                // FIXME: Figure out wtf I'm doing with snapshots
                tree.swap_mutable_and_immutable(
                    snapshot_min_for_table_output(op + 1),
                );
            }

            if (compaction.bar_context == null and op + 1 == constants.lsm_batch_multiple) {
                return;
            }

            assert(compaction.beat_context == null);
            assert(compaction.bar_context != null);

            const bar_context = &compaction.bar_context.?;
            assert(bar_context.beat_count >= bar_context.beat_budget.?);

            // BLAAAH deal with this better!
            if (compaction.bar_context == null) {
                return;
            }

            // Each compaction's manifest updates are deferred to the end of the last
            // bar to ensure:
            // - manifest log updates are ordered deterministically relative to one another, and
            // - manifest updates are not visible until after the blocks are all on disk.
            const manifest = &bar_context.tree.manifest;
            const level_b = compaction.level_b;
            const snapshot_max = snapshot_max_for_table_input(bar_context.op_min);

            if (bar_context.move_table) {
                // If no compaction is required, don't update snapshot_max.
            } else {
                // These updates MUST precede insert_table() and move_table() since they use
                // references to modify the ManifestLevel in-place.
                switch (bar_context.table_info_a) {
                    .immutable => {},
                    .disk => |table_info| {
                        manifest.update_table(level_b - 1, snapshot_max, table_info);
                    },
                }
                for (bar_context.range_b.tables.const_slice()) |table| {
                    manifest.update_table(level_b, snapshot_max, table);
                }
            }

            for (bar_context.manifest_entries.slice()) |*entry| {
                switch (entry.operation) {
                    .insert_to_level_b => manifest.insert_table(level_b, &entry.table),
                    .move_to_level_b => manifest.move_table(level_b - 1, level_b, &entry.table),
                }
            }

            // Our bar is done!
            compaction.bar_context = null;
        }

        /// If we can just move the table, don't bother with merging.
        // FIXME: For now, move_table will happen in the prepare step, but we still have to pulse
        // through the (useless) read / merge / write steps before finalizing it.
        fn move_table(compaction: *Compaction) void {
            const bar_context = &compaction.bar_context.?;

            log.info(
                "{s}: Moving table: level_b={}",
                .{ compaction.tree_config.name, compaction.level_b },
            );

            const snapshot_max = snapshot_max_for_table_input(bar_context.op_min);
            const table_a = bar_context.table_info_a.disk.table_info;
            assert(table_a.snapshot_max >= snapshot_max);

            bar_context.manifest_entries.append_assume_capacity(.{
                .operation = .move_to_level_b,
                .table = table_a.*,
            });
        }

        fn on_iterator_init_a(read: *Grid.Read, index_block: BlockPtrConst) void {
            const compaction = @fieldParentPtr(Compaction, "read", read);
            assert(compaction.state == .iterator_init_a);
            assert(compaction.tree_config.id == schema.TableIndex.metadata(index_block).tree_id);

            // `index_block` is only valid for this callback, so copy its contents.
            // TODO(jamii) This copy can be avoided if we bypass the cache.

            // TODO: index_block_a looks like it's used up fully here, no? We shouldn't have to take a copy?
            stdx.copy_disjoint(.exact, u8, compaction.index_block_a, index_block);

            const index_schema_a = schema.TableIndex.from(compaction.index_block_a);
            compaction.iterator_a.start(.{
                .grid = compaction.grid,
                .addresses = index_schema_a.data_addresses_used(compaction.index_block_a),
                .checksums = index_schema_a.data_checksums_used(compaction.index_block_a),
                .direction = .ascending,
            });
            compaction.release_table_blocks(compaction.index_block_a);
            compaction.state = .compacting;
            compaction.loop_start();
        }

        fn loop_start(compaction: *Compaction) void {
            assert(compaction.state == .compacting);

            tracer.start(
                &compaction.iterator_tracer_slot,
                .{ .tree_compaction_iter = .{
                    .tree_name = compaction.tree_config.name,
                    .level_b = compaction.context.level_b,
                } },
                @src(),
            );

            compaction.iterator_check(.a);
        }

        /// If `values_in[index]` is empty and more values are available, read them.
        fn iterator_check(compaction: *Compaction, input_level: void) void {
            assert(compaction.state == .compacting);

            if (compaction.values_in[@intFromEnum(input_level)].len > 0) {
                // Still have values on this input_level, no need to refill.
                compaction.iterator_check_finish(input_level);
            } else if (input_level == .a and compaction.context.table_info_a == .immutable) {
                // Potentially fill our immutable values from the immutable TableMemory.
                // TODO: Currently, this copies the values to compaction.data_blocks[0], but in
                // future we can make it use a KWayMergeIterator.
                if (compaction.context.table_info_a.immutable.len > 0) {
                    var target = Table.data_block_values(compaction.data_blocks[0]);

                    const filled = compaction.fill_immutable_values(target);
                    assert(filled <= target.len);
                    if (filled == 0) assert(Table.usage == .secondary_index);

                    // The immutable table is always considered "Table A", which maps to 0.
                    compaction.values_in[0] = target[0..filled];
                } else {
                    assert(compaction.values_in[0].len == 0);
                }

                compaction.iterator_check_finish(input_level);
            } else {
                compaction.state = .{ .iterator_next = input_level };
                switch (input_level) {
                    .a => compaction.iterator_a.next(iterator_next_a),
                    .b => compaction.iterator_b.next(.{
                        .on_index = on_index_block,
                        .on_data = iterator_next_b,
                    }),
                }
            }
        }

        /// Copies values to `target` from our immutable table input. In the process, merge values
        /// with identical keys (last one wins) and collapse tombstones for secondary indexes.
        /// Return the number of values written to the output and updates immutable table slice to
        /// the non-processed remainder.
        fn fill_immutable_values(compaction: *Compaction, target: []Value) usize {
            var source = compaction.context.table_info_a.immutable;
            assert(source.len > 0);

            if (constants.verify) {
                // The input may have duplicate keys (last one wins), but keys must be
                // non-decreasing.
                // A source length of 1 is always non-decreasing.
                for (source[0 .. source.len - 1], source[1..source.len]) |*value, *value_next| {
                    assert(key_from_value(value) <= key_from_value(value_next));
                }
            }

            var source_index: usize = 0;
            var target_index: usize = 0;
            while (target_index < target.len and source_index < source.len) : (source_index += 1) {
                // The last value in a run of duplicates needs to be the one that ends up in
                // target.
                target[target_index] = source[source_index];

                // If we're at the end of the source, there is no next value, so the next value
                // can't be equal.
                const value_next_equal = source_index + 1 < source.len and
                    key_from_value(&source[source_index]) ==
                    key_from_value(&source[source_index + 1]);

                if (value_next_equal) {
                    if (Table.usage == .secondary_index) {
                        // Secondary index optimization --- cancel out put and remove.
                        // NB: while this prevents redundant tombstones from getting to disk, we
                        // still spend some extra CPU work to sort the entries in memory. Ideally,
                        // we annihilate tombstones immediately, before sorting, but that's tricky
                        // to do with scopes.
                        assert(tombstone(&source[source_index]) !=
                            tombstone(&source[source_index + 1]));
                        source_index += 2;
                        target_index += 0;
                    } else {
                        // The last value in a run of duplicates needs to be the one that ends up in
                        // target.
                        source_index += 1;
                        target_index += 0;
                    }
                } else {
                    source_index += 1;
                    target_index += 1;
                }
            }

            // At this point, source_index and target_index are actually counts.
            // source_index will always be incremented after the final iteration as part of the
            // continue expression.
            // target_index will always be incremented, since either source_index runs out first
            // so value_next_equal is false, or a new value is hit, which will increment it.
            const source_count = source_index;
            const target_count = target_index;

            assert(target_count <= source_count);

            compaction.context.table_info_a.immutable =
                compaction.context.table_info_a.immutable[source_count..];

            if (target_count == 0) {
                assert(Table.usage == .secondary_index);
                return 0;
            }

            if (constants.verify) {
                // Our output must be strictly increasing.
                // An output length of 1 is always strictly increasing.
                for (
                    target[0 .. target_count - 1],
                    target[1..target_count],
                ) |*value, *value_next| {
                    assert(key_from_value(value_next) > key_from_value(value));
                }
            }

            assert(target_count > 0);
            return target_count;
        }

        fn on_index_block(iterator_b: void) void {
            const compaction = @fieldParentPtr(Compaction, "iterator_b", iterator_b);
            assert(std.meta.eql(compaction.state, .{ .iterator_next = .b }));

            // This is super NB:
            compaction.release_table_blocks(compaction.index_block_b);
        }

        // TODO: Support for LSM snapshots would require us to only remove blocks
        // that are invisible.
        fn release_table_blocks(compaction: *Compaction, index_block: BlockPtrConst) void {
            // Release the table's block addresses in the Grid as it will be made invisible.
            // This is safe; compaction.index_block_b holds a copy of the index block for a
            // table in Level B. Additionally, compaction.index_block_a holds
            // a copy of the index block for the Level A table being compacted.

            const grid = compaction.grid;
            const index_schema = schema.TableIndex.from(index_block);
            for (index_schema.data_addresses_used(index_block)) |address| grid.release(address);
            grid.release(Table.block_address(index_block));
        }

        fn iterator_next_a(
            iterator_a: void,
            data_block: ?BlockPtrConst,
        ) void {
            const compaction = @fieldParentPtr(Compaction, "iterator_a", iterator_a);
            assert(std.meta.eql(compaction.state, .{ .iterator_next = .a }));
            compaction.iterator_next(data_block);
        }

        fn iterator_next_b(
            iterator_b: void,
            data_block: ?BlockPtrConst,
        ) void {
            const compaction = @fieldParentPtr(Compaction, "iterator_b", iterator_b);
            assert(std.meta.eql(compaction.state, .{ .iterator_next = .b }));
            compaction.iterator_next(data_block);
        }

        fn iterator_next(compaction: *Compaction, data_block: ?BlockPtrConst) void {
            assert(compaction.state == .iterator_next);
            const input_level = compaction.state.iterator_next;
            const index = @intFromEnum(input_level);

            if (data_block) |block| {
                // `data_block` is only valid for this callback, so copy its contents.
                // TODO(jamii) This copy can be avoided if we bypass the cache.
                stdx.copy_disjoint(.exact, u8, compaction.data_blocks[index], block);
                compaction.values_in[index] =
                    Table.data_block_values_used(compaction.data_blocks[index]);

                // Assert that we're reading data blocks in key order.
                const values_in = compaction.values_in[index];
                assert(values_in.len > 0);
                if (constants.verify) {
                    for (values_in[0 .. values_in.len - 1], values_in[1..]) |*value, *value_next| {
                        assert(key_from_value(value) < key_from_value(value_next));
                    }
                }
                const first_key = key_from_value(&values_in[0]);
                const last_key = key_from_value(&values_in[values_in.len - 1]);
                if (compaction.last_keys_in[index]) |last_key_prev| {
                    assert(last_key_prev < first_key);
                }
                if (values_in.len > 1) {
                    assert(first_key < last_key);
                }
                compaction.last_keys_in[index] = last_key;
            } else {
                // If no more data blocks available, just leave `values_in[index]` empty.
            }

            compaction.state = .compacting;
            compaction.iterator_check_finish(input_level);
        }

        fn iterator_check_finish(compaction: *Compaction, input_level: void) void {
            switch (input_level) {
                .a => compaction.iterator_check(.b),
                .b => compaction.compact(),
            }
        }

        fn compact(compaction: *Compaction) void {
            assert(compaction.state == .compacting);
            assert(compaction.table_builder.value_count < Table.layout.block_value_count_max);

            const values_in = compaction.values_in;

            var tracer_slot: ?tracer.SpanStart = null;
            tracer.start(
                &tracer_slot,
                .{ .tree_compaction_merge = .{
                    .tree_name = compaction.tree_config.name,
                    .level_b = compaction.context.level_b,
                } },
                @src(),
            );

            if (values_in[0].len == 0 and values_in[1].len == 0) {
                compaction.input_state = .exhausted;
            } else if (values_in[0].len == 0) {
                compaction.copy(.b);
            } else if (values_in[1].len == 0) {
                if (compaction.drop_tombstones) {
                    compaction.copy_drop_tombstones();
                } else {
                    compaction.copy(.a);
                }
            } else {
                compaction.merge();
            }

            tracer.end(
                &tracer_slot,
                .{ .tree_compaction_merge = .{
                    .tree_name = compaction.tree_config.name,
                    .level_b = compaction.context.level_b,
                } },
            );

            compaction.write_blocks();
        }

        fn copy(compaction: *Compaction, input_level: void) void {
            assert(compaction.state == .compacting);
            assert(compaction.values_in[@intFromEnum(input_level) +% 1].len == 0);
            assert(compaction.table_builder.value_count < Table.layout.block_value_count_max);

            const values_in = compaction.values_in[@intFromEnum(input_level)];
            const values_out = compaction.table_builder.data_block_values();
            var values_out_index = compaction.table_builder.value_count;

            assert(values_in.len > 0);

            const len = @min(values_in.len, values_out.len - values_out_index);
            assert(len > 0);
            stdx.copy_disjoint(
                .exact,
                Value,
                values_out[values_out_index..][0..len],
                values_in[0..len],
            );

            compaction.values_in[@intFromEnum(input_level)] = values_in[len..];
            compaction.table_builder.value_count += @as(u32, @intCast(len));
        }

        fn copy_drop_tombstones(compaction: *Compaction) void {
            assert(compaction.state == .compacting);
            assert(compaction.values_in[1].len == 0);
            assert(compaction.table_builder.value_count < Table.layout.block_value_count_max);

            // Copy variables locally to ensure a tight loop.
            const values_in_a = compaction.values_in[0];
            const values_out = compaction.table_builder.data_block_values();
            var values_in_a_index: usize = 0;
            var values_out_index = compaction.table_builder.value_count;

            // Merge as many values as possible.
            while (values_in_a_index < values_in_a.len and
                values_out_index < values_out.len)
            {
                const value_a = &values_in_a[values_in_a_index];

                values_in_a_index += 1;
                if (tombstone(value_a)) {
                    assert(Table.usage != .secondary_index);
                    continue;
                }
                values_out[values_out_index] = value_a.*;
                values_out_index += 1;
            }

            // Copy variables back out.
            compaction.values_in[0] = values_in_a[values_in_a_index..];
            compaction.table_builder.value_count = values_out_index;
        }

        fn merge(compaction: *Compaction) void {
            assert(compaction.values_in[0].len > 0);
            assert(compaction.values_in[1].len > 0);
            assert(compaction.table_builder.value_count < Table.layout.block_value_count_max);

            // Copy variables locally to ensure a tight loop.
            const values_in_a = compaction.values_in[0];
            const values_in_b = compaction.values_in[1];
            const values_out = compaction.table_builder.data_block_values();
            var values_in_a_index: usize = 0;
            var values_in_b_index: usize = 0;
            var values_out_index = compaction.table_builder.value_count;

            // Merge as many values as possible.
            while (values_in_a_index < values_in_a.len and
                values_in_b_index < values_in_b.len and
                values_out_index < values_out.len)
            {
                const value_a = &values_in_a[values_in_a_index];
                const value_b = &values_in_b[values_in_b_index];
                switch (std.math.order(key_from_value(value_a), key_from_value(value_b))) {
                    .lt => {
                        values_in_a_index += 1;
                        if (compaction.drop_tombstones and
                            tombstone(value_a))
                        {
                            assert(Table.usage != .secondary_index);
                            continue;
                        }
                        values_out[values_out_index] = value_a.*;
                        values_out_index += 1;
                    },
                    .gt => {
                        values_in_b_index += 1;
                        values_out[values_out_index] = value_b.*;
                        values_out_index += 1;
                    },
                    .eq => {
                        values_in_a_index += 1;
                        values_in_b_index += 1;

                        if (Table.usage == .secondary_index) {
                            // Secondary index optimization --- cancel out put and remove.
                            assert(tombstone(value_a) != tombstone(value_b));
                            continue;
                        } else if (compaction.drop_tombstones) {
                            if (tombstone(value_a)) {
                                continue;
                            }
                        }

                        values_out[values_out_index] = value_a.*;
                        values_out_index += 1;
                    },
                }
            }

            // Copy variables back out.
            compaction.values_in[0] = values_in_a[values_in_a_index..];
            compaction.values_in[1] = values_in_b[values_in_b_index..];
            compaction.table_builder.value_count = values_out_index;
        }

        fn write_blocks(compaction: *Compaction) void {
            assert(compaction.state == .compacting);
            const input_exhausted = compaction.input_state == .exhausted;
            const table_builder = &compaction.table_builder;

            compaction.state = .{ .tables_writing = .{ .pending = 0 } };

            // Flush the data block if needed.
            if (table_builder.data_block_full() or
                table_builder.index_block_full() or
                // If the input is exhausted then we need to flush all blocks before finishing.
                (input_exhausted and !table_builder.data_block_empty()))
            {
                table_builder.data_block_finish(.{
                    .cluster = compaction.grid.superblock.working.cluster,
                    .address = compaction.grid.acquire(compaction.grid_reservation.?),
                    .snapshot_min = snapshot_min_for_table_output(compaction.context.op_min),
                    .tree_id = compaction.tree_config.id,
                });
                std.log.info("{s}: writing data block...", .{compaction.tree_config.name});
                WriteBlock(.data).write_block(compaction);
            }

            // Flush the index block if needed.
            if (table_builder.index_block_full() or
                // If the input is exhausted then we need to flush all blocks before finishing.
                (input_exhausted and !table_builder.index_block_empty()))
            {
                const table = table_builder.index_block_finish(.{
                    .cluster = compaction.grid.superblock.working.cluster,
                    .address = compaction.grid.acquire(compaction.grid_reservation.?),
                    .snapshot_min = snapshot_min_for_table_output(compaction.context.op_min),
                    .tree_id = compaction.tree_config.id,
                });
                // Make this table visible at the end of this half-bar.
                compaction.manifest_entries.append_assume_capacity(.{
                    .operation = .insert_to_level_b,
                    .table = table,
                });
                WriteBlock(.index).write_block(compaction);
            }

            if (compaction.state.tables_writing.pending == 0) {
                compaction.write_finish();
            }
        }

        const WriteBlockField = enum { data, index };
        fn WriteBlock(comptime write_block_field: WriteBlockField) type {
            return struct {
                fn write_block(compaction: *Compaction) void {
                    assert(compaction.state == .tables_writing);

                    const write = switch (write_block_field) {
                        .data => &compaction.write_data_block,
                        .index => &compaction.write_index_block,
                    };
                    const block = switch (write_block_field) {
                        .data => &compaction.table_builder.data_block,
                        .index => &compaction.table_builder.index_block,
                    };
                    compaction.state.tables_writing.pending += 1;
                    compaction.grid.create_block(on_write, write, block);
                }

                fn on_write(write: *Grid.Write) void {
                    const compaction = @fieldParentPtr(
                        Compaction,
                        switch (write_block_field) {
                            .data => "write_data_block",
                            .index => "write_index_block",
                        },
                        write,
                    );
                    assert(compaction.state == .tables_writing);
                    compaction.state.tables_writing.pending -= 1;
                    if (compaction.state.tables_writing.pending == 0) {
                        compaction.write_finish();
                    }
                }
            };
        }

        fn write_finish(compaction: *Compaction) void {
            assert(compaction.state == .tables_writing);
            assert(compaction.state.tables_writing.pending == 0);

            tracer.end(
                &compaction.iterator_tracer_slot,
                .{ .tree_compaction_iter = .{
                    .tree_name = compaction.tree_config.name,
                    .level_b = compaction.context.level_b,
                } },
            );

            switch (compaction.input_state) {
                .remaining => {
                    compaction.state = .next_tick;
                    // compaction.grid.on_next_tick(loop_on_next_tick, &compaction.next_tick);
                },
                .exhausted => {
                    compaction.state = .next_tick;
                    // compaction.grid.on_next_tick(done_on_next_tick, &compaction.next_tick);
                },
            }
        }
    };
}

fn snapshot_max_for_table_input(op_min: u64) u64 {
    return snapshot_min_for_table_output(op_min) - 1;
}

pub fn snapshot_min_for_table_output(op_min: u64) u64 {
    assert(op_min > 0);
    assert(op_min % @divExact(constants.lsm_batch_multiple, 2) == 0);
    return op_min + @divExact(constants.lsm_batch_multiple, 2);
}

/// Returns the first op of the compaction (Compaction.op_min) for a given op/beat.
///
/// After this compaction finishes:
/// - `op_min + half_bar_beat_count - 1` will be the input tables' snapshot_max.
/// - `op_min + half_bar_beat_count` will be the output tables' snapshot_min.
///
/// Each half-bar has a separate op_min (for deriving the output snapshot_min) instead of each full
/// bar because this allows the output tables of the first half-bar's compaction to be prefetched
/// against earlier — hopefully while they are still warm in the cache from being written.
///
///
/// These charts depict the commit/compact ops over a series of
/// commits and compactions (with lsm_batch_multiple=8).
///
/// Legend:
///
///   ┼   full bar (first half-bar start)
///   ┬   half bar (second half-bar start)
///       This is incremented at the end of each compact().
///   .   op is in mutable table (in memory)
///   ,   op is in immutable table (in memory)
///   #   op is on disk
///   ✓   checkpoint() may follow compact()
///
///   0 2 4 6 8 0 2 4 6
///   ┼───┬───┼───┬───┼
///   .       ╷       ╷     init(superblock.commit_min=0)⎤ Compaction is effectively a noop for the
///   ..      ╷       ╷     commit;compact( 1) start/end ⎥ first bar because there are no tables on
///   ...     ╷       ╷     commit;compact( 2) start/end ⎥ disk yet, and no immutable table to
///   ....    ╷       ╷     commit;compact( 3) start/end ⎥ flush.
///   .....   ╷       ╷     commit;compact( 4) start/end ⎥
///   ......  ╷       ╷     commit;compact( 5) start/end ⎥ This applies:
///   ....... ╷       ╷     commit;compact( 6) start/end ⎥ - when the LSM is starting on a freshly
///   ........╷       ╷     commit;compact( 7) start    ⎤⎥   formatted data file, and also
///   ,,,,,,,,.       ╷  ✓         compact( 7)       end⎦⎦ - when the LSM is recovering from a crash
///   ,,,,,,,,.       ╷     commit;compact( 8) start/end     (see below).
///   ,,,,,,,,..      ╷     commit;compact( 9) start/end
///   ,,,,,,,,...     ╷     commit;compact(10) start/end
///   ,,,,,,,,....    ╷     commit;compact(11) start/end
///   ,,,,,,,,.....   ╷     commit;compact(12) start/end
///   ,,,,,,,,......  ╷     commit;compact(13) start/end
///   ,,,,,,,,....... ╷     commit;compact(14) start/end
///   ,,,,,,,,........╷     commit;compact(15) start    ⎤
///   ########,,,,,,,,╷  ✓         compact(15)       end⎦
///   ########,,,,,,,,.     commit;compact(16) start/end
///   ┼───┬───┼───┬───┼
///   0 2 4 6 8 0 2 4 6
///   ┼───┬───┼───┬───┼                                    Recover with a checkpoint taken at op 15.
///   ########        ╷     init(superblock.commit_min=7)  At op 15, ops 8…15 are in memory, so they
///   ########.       ╷     commit        ( 8) start/end ⎤ were dropped by the crash.
///   ########..      ╷     commit        ( 9) start/end ⎥
///   ########...     ╷     commit        (10) start/end ⎥ But compaction is not run for ops 8…15
///   ########....    ╷     commit        (11) start/end ⎥ because it was already performed
///   ########.....   ╷     commit        (12) start/end ⎥ before the checkpoint.
///   ########......  ╷     commit        (13) start/end ⎥
///   ########....... ╷     commit        (14) start/end ⎥ We can begin to compact again at op 16,
///   ########........╷     commit        (15) start    ⎤⎥ because those compactions (if previously
///   ########,,,,,,,,╷  ✓                (15)       end⎦⎦ performed) are not included in the
///   ########,,,,,,,,.     commit;compact(16) start/end   checkpoint.
///   ┼───┬───┼───┬───┼
///   0 2 4 6 8 0 2 4 6
///
/// Notice how in the checkpoint recovery example above, we are careful not to `compact(op)` twice
/// for any op (even if we crash/recover), since that could lead to differences between replicas'
/// storage. The last bar of `commit()`s is always only in memory, so it is safe to repeat.
pub fn compaction_op_min(op: u64) u64 {
    _ = op;
    // return op - op % half_bar_beat_count;
}
