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
const CompactionInterfaceType = @import("compaction.zig").CompactionInterfaceType;
const CompactionBlocks = @import("compaction.zig").CompactionBlocks;

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

    const Grid = GridType(_Storage);
    const CompactionInterface = CompactionInterfaceType(Grid, _tree_infos);

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

        const CompactionPipeline = struct {
            const PipelineInterface = struct {
                pipeline: *CompactionPipeline,
                interface: CompactionInterface,
                current_operation: enum { read, cpu, write } = .read,
            };

            compactions: stdx.BoundedArray(CompactionInterface, (_tree_infos[_tree_infos.len - 1].tree_id - _tree_infos[0].tree_id) * constants.lsm_levels) = .{},
            compaction_idx: usize = 0,
            slots: [3]?PipelineInterface = .{ null, null, null },
            fill_idx: usize = 0,
            running_stages: usize = 0,

            // FIXME: So technically if we want to be able to use our blocks freely, we need as many reads and writes :/
            // We could do a union, just not sure if it's worth it yet.
            compaction_blocks: []BlockPtr,
            compaction_reads: []Grid.FatRead,
            compaction_writes: []Grid.FatWrite,
            compaction_blocks_split: CompactionBlocks = undefined,

            state: enum { draining, filling, full } = .filling,
            input_exhausted: bool = false,

            forest: ?*Forest = null,
            callback: ?Callback = null,

            pub fn init(allocator: mem.Allocator) !CompactionPipeline {
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

                return .{
                    .compaction_blocks = compaction_blocks,
                    .compaction_reads = compaction_reads,
                    .compaction_writes = compaction_writes,
                };
            }

            pub fn deinit(self: *CompactionPipeline, allocator: mem.Allocator) void {
                _ = self;
                _ = allocator;
                // FIXME: Deinit compaction_blocks
            }

            /// Our input and output blocks (excluding index blocks for now) are split two ways. First, equally by pipeline stage
            /// then by table a / table b. FIXME: Currently the split by a / b is equal, but it shouldn't be for max performance.
            /// -------------------------------------------------------------
            /// | Pipeline 0                  | Pipeline 1                  |
            /// | Table A     | Table B       | Table A     | Table B       |
            /// -------------------------------------------------------------
            /// Here's a complicating factor: to ensure the jigsaw blocks line up nicely, this memory actually needs to be managed
            /// by the forest.
            /// Eg, once we've done our final write(1), we know we can use read(0) memory...
            /// This can be called once at the start of every bar.
            fn divide_blocks(self: *CompactionPipeline) CompactionBlocks {
                var minimum_block_count: u64 = 0;
                // We need a minimum of 2 input data blocks; one from each table.
                minimum_block_count += 2;

                // We need a minimum of 1 output data block.
                minimum_block_count += 1;

                // Because we're a 3 stage pipeline, with the middle stage (cpu) having a data dependency on both
                // read and write data blocks, we need to split our memory in the middle. This results in a doubling of
                // what we have so far.
                // FIXME: perhaps read_data_block?? Hmmm input is clearer I think.
                minimum_block_count *= 2;

                // Lastly, reserve our input index blocks. For now, just require we have enough for all tables and pretend like
                // pipelining this isn't a thing.
                // FIXME: This shouldn't do that. The minimum is 2; but we don't really need to hold on to index blocks
                // if we read the data blocks directly. TBC.
                minimum_block_count += 9;

                // FIXME: We can also calculate the optimum number of blocks. Old comment below:
                // // Actually... All the comments below would be to do _all_ the work required. The max amount to do the work required
                // // per beat would then be divided by beat. _however_ the minimums won't change!
                // // Minimum of 2, max lsm_growth_factor+1. Replaces index_block_a and index_block_b too.
                // // Output index blocks are explicitly handled in bar_setup_budget.
                // input_index_blocks: []BlockPtr,
                // // Minimum of 2, one from each table. Max would be max possible data blocks in lsm_growth_factor+1 tables.
                // input_data_blocks: []BlockPtr,
                // // Minimum of 1, max would be max possible data blocks in lsm_growth_factor+1 tables.
                // output_data_blocks: []BlockPtr,

                const blocks = self.compaction_blocks;

                assert(blocks.len >= minimum_block_count);

                const input_index_blocks = blocks[0..9];

                const input_data_pipeline_0_level_a = blocks[9..][0..1];
                const input_data_pipeline_0_level_b = blocks[10..][0..1];
                const input_data_pipeline_1_level_a = blocks[11..][0..1];
                const input_data_pipeline_1_level_b = blocks[12..][0..1];

                const output_data_pipeline_0 = blocks[13..][0..1];
                const output_data_pipeline_1 = blocks[14..][0..1];

                const input_data_blocks = .{ .{ input_data_pipeline_0_level_a, input_data_pipeline_0_level_b }, .{ input_data_pipeline_1_level_a, input_data_pipeline_1_level_b } };
                const output_data_blocks = .{ output_data_pipeline_0, output_data_pipeline_1 };

                return .{
                    .input_index_blocks = input_index_blocks,
                    .input_data_blocks = input_data_blocks,
                    .output_data_blocks = output_data_blocks,
                };
            }

            pub fn beat(self: *CompactionPipeline, forest: *Forest, op: u64, callback: Callback) void {
                const compaction_beat = op % constants.lsm_batch_multiple;

                const first_beat = compaction_beat == 0;

                if (first_beat) {
                    for (self.compactions.slice(), 0..) |*compaction, i| {
                        // FIXME: These blocks need to be disjoint. Any way we can assert that?
                        // constants.lsm_batch_multiple - 1
                        compaction.bar_setup_budget(1, self.compaction_blocks[1000 + i .. 1000 + i + 1]);
                    }

                    // Split up our internal block pool as needed for the compaction pipelines.
                    self.compaction_blocks_split = self.divide_blocks();
                }

                // FIXME: Assert no compactions are running, and the pipeline is empty in a better way
                // MAybe move to a union enum for state.
                assert(self.slots[0] == null and self.slots[1] == null and self.slots[2] == null);
                assert(self.callback == null);
                assert(self.forest == null);

                for (self.compactions.slice()) |*compaction| {
                    // Set up the beat depending on what buffers we have available.
                    compaction.beat_grid_acquire();
                }

                self.callback = callback;
                self.forest = forest;

                if (forest.compaction_pipeline.compactions.count() == 0) {
                    // No compactions - we're done! Likely we're < lsm_batch_multiple but it could just be eg
                    // empty ops pulsed through.
                    maybe(op < constants.lsm_batch_multiple);

                    // FIXME: Next-tick this, move those to the handler.
                    self.callback = null;
                    self.forest = null;
                    callback(forest);
                    return;
                }

                // Everything up to this point has been sync and deterministic. We now enter async-land :)
                // Kick off the pipeline by starting a read. The blip_callback will do the rest wrt filling and
                // draining.
                std.log.info("Firing up pipeline.", .{});
                self.state = .filling;
                self.fill_idx = 1;
                self.slots[0] = .{ .pipeline = self, .interface = self.compactions.slice()[0] };
                self.slots[0].?.interface.beat_blocks_assign(self.compaction_blocks_split, self.compaction_reads, self.compaction_writes);
                self.running_stages += 1;
                self.slots[0].?.interface.blip_read(blip_callback);
            }

            // FIXME: See comments in the interface.. But this sucks, can be messed up easily, and there must be a better way!
            // Maybe a context struct or something?
            fn blip_callback(compaction_interface_opaque: *anyopaque, input_exhausted: ?bool) void {
                const compaction_interface: *CompactionInterface = @ptrCast(@alignCast(compaction_interface_opaque));
                const pipeline = @fieldParentPtr(PipelineInterface, "interface", compaction_interface).pipeline;

                const slot_idx = blk: for (0..3) |i| {
                    if (pipeline.slots[i]) |*slot| {
                        if (&slot.interface == compaction_interface) {
                            break :blk i;
                        }
                    }
                } else @panic("wtf!");

                // FIXME: For now, we have a barrier on all stages... We might want to drop this, or have a more advanced barrier based on memory
                // only.
                pipeline.running_stages -= 1;

                std.log.info("blip_callback: slot {}.", .{slot_idx});

                if (pipeline.running_stages > 0) {
                    return;
                }

                // Fill the next stage first.
                // if (pipeline.state == .filling) {
                //     pipeline.slots[pipeline.fill_idx] = .{ .pipeline = pipeline, .interface = pipeline.compactions.slice()[0] };
                //     std.log.info("... blip_callback: filled {} with read.", .{pipeline.fill_idx});

                //     pipeline.fill_idx += 1;

                //     if (pipeline.fill_idx == 3) {
                //         pipeline.state = .full;
                //     }

                //     // FIXME: So gross.
                //     pipeline.running_stages += 1;
                //     pipeline.slots[pipeline.fill_idx - 1].?.interface.blip_read(blip_callback);
                // }

                // Advanced the current stages, making sure to start our reads and writes before CPU
                var cpu: ?usize = null;
                for (pipeline.slots[0..pipeline.fill_idx], 0..) |*slot, i| {
                    switch (slot.*.?.current_operation) {
                        .read => {
                            std.log.info("... ... blip_callback: read done, input_exhausted: {?}, starting cpu on {}.", .{ input_exhausted, i });
                            cpu = i;

                            assert(input_exhausted == null);

                            if (pipeline.input_exhausted) {
                                // If we hit input_exhausted, it means that we need to discard the results of this read. We don't
                                // have to do anything explicit to discard, we just need to increment our compaction state.

                            }
                        },
                        .cpu => {
                            std.log.info("... ... blip_callback: cpu done, starting write on {}.", .{i});
                            assert(input_exhausted != null);
                            pipeline.input_exhausted = input_exhausted.?;

                            pipeline.running_stages += 1;
                            slot.*.?.current_operation = .write;
                            slot.*.?.interface.blip_write(blip_callback);
                        },
                        .write => {
                            if (pipeline.input_exhausted) {
                                // If we're in the input exhausted state, we have no more reads that can be done, so don't schedule any more
                                std.log.info("... ... blip_callback: write done, NOT starting read on {}.", .{i});
                                pipeline.compaction_idx += 1;

                                if (pipeline.compaction_idx == pipeline.compactions.count()) {
                                    std.log.info("EXHAUSTED!!!!!", .{});
                                    // FIXME: Next-tick this, move those to the handler.
                                    slot.* = null;
                                    const callback = pipeline.callback.?;
                                    const forest = pipeline.forest.?;

                                    // FIXME: This style.
                                    pipeline.callback = null;
                                    pipeline.forest = null;

                                    callback(forest);
                                    return;
                                }

                                // FIXME: Massive hack, hardcoding to get 2 to run. The blocks need to be released by split too.
                                std.log.info("... ... ... because we're moving on to next compaction.", .{});
                                slot.* = .{ .pipeline = pipeline, .interface = pipeline.compactions.slice()[pipeline.compaction_idx] };
                                pipeline.running_stages += 1;
                                slot.*.?.interface.beat_blocks_assign(pipeline.compaction_blocks_split, pipeline.compaction_reads, pipeline.compaction_writes);
                                slot.*.?.interface.blip_read(blip_callback);

                                return;
                            }
                            std.log.info("... ... blip_callback: write done, starting read on {}.", .{i});
                            assert(input_exhausted == null);
                            pipeline.running_stages += 1;
                            slot.*.?.current_operation = .read;
                            slot.*.?.interface.blip_read(blip_callback);
                        },
                    }
                }

                if (cpu) |c| {
                    pipeline.running_stages += 1;
                    pipeline.slots[c].?.current_operation = .cpu;
                    pipeline.slots[c].?.interface.blip_cpu(blip_callback);
                }
            }

            fn beat_end(self: *CompactionPipeline) void {
                // FIXME: Do we do a reverse teardown rateher?
                for (self.compactions.slice()) |*compaction| {
                    compaction.beat_grid_forfeit();
                }
            }
        };

        progress: ?union(enum) {
            open: struct { callback: Callback },
            checkpoint: struct { callback: Callback },
            compact: struct {
                op: u64,
                callback: Callback,
            },
        } = null,

        grid: *Grid,
        grooves: Grooves,
        node_pool: *NodePool,
        manifest_log: ManifestLog,
        manifest_log_progress: enum { idle, compacting, done, skip } = .idle,

        compaction_pipeline: CompactionPipeline,

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

            var compaction_pipeline = try CompactionPipeline.init(allocator);
            errdefer compaction_pipeline.deinit(allocator);

            const scan_buffer_pool = try ScanBufferPool.init(allocator);
            errdefer scan_buffer_pool.deinit(allocator);

            return Forest{
                .grid = grid,
                .grooves = grooves,
                .node_pool = node_pool,
                .manifest_log = manifest_log,

                .compaction_pipeline = compaction_pipeline,

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

                // FIXME: Reset this
                .compaction_pipeline = forest.compaction_pipeline,

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

            // Setup loop, runs only on the first beat of every bar, before any async work is done.
            if (first_beat) {
                std.log.info("===============================================================", .{});
                std.log.info("Bar setup:", .{});
                std.log.info("===============================================================", .{});
                assert(forest.compaction_pipeline.compactions.count() == 0);

                inline for (0..constants.lsm_levels) |level_b| {
                    inline for (tree_id_range.min..tree_id_range.max) |tree_id| {
                        var tree = tree_for_id(forest, tree_id);
                        assert(tree.compactions.len == constants.lsm_levels);

                        var compaction = &tree.compactions[level_b];

                        // This will return how many compactions and stuff this level needs to do...
                        const maybe_info = compaction.bar_setup(tree, op);
                        if (maybe_info) |info| {
                            // FIXME: Assert len?
                            forest.compaction_pipeline.compactions.append_assume_capacity(CompactionInterface.init(info, compaction));
                            std.log.info("Target Level: {}, Tree: {s}@{}: {}", .{ level_b, tree.config.name, op, info });
                        }
                    }
                }
                std.log.info("===============================================================", .{});
            }

            forest.progress = .{ .compact = .{
                .op = op,
                .callback = callback,
            } };

            // Compaction only starts > lsm_batch_multiple because nothing compacts in the first bar.
            assert(op >= constants.lsm_batch_multiple or forest.compaction_pipeline.compactions.count() == 0);

            forest.compaction_pipeline.beat(forest, op, compact_callback);
        }

        // FIXME: This mixes both manifest and non-manifest compaction
        fn compact_callback(forest: *Forest) void {
            assert(forest.progress.? == .compact);
            // assert(forest.manifest_log_progress != .idle);
            forest.verify_table_extents();

            const progress = &forest.progress.?.compact;

            // Call sync finish code.
            forest.compact_end();

            // const half_bar_end =
            //     (progress.op + 1) % @divExact(constants.lsm_batch_multiple, 2) == 0;
            // // On the last beat of the bar, make sure that manifest log compaction is finished.
            // if (half_bar_end and forest.manifest_log_progress == .compacting) return;

            // FIXME
            // inline for (std.meta.fields(Grooves)) |field| {
            //     @field(forest.grooves, field.name).compact_end();
            // }

            // if (half_bar_end) {
            //     switch (forest.manifest_log_progress) {
            //         .idle => unreachable,
            //         .compacting => unreachable,
            //         .done => forest.manifest_log.compact_end(),
            //         .skip => {},
            //     }
            //     forest.manifest_log_progress = .idle;
            // }

            const callback = progress.callback;
            forest.progress = null;
            callback(forest);
        }

        fn compact_end(forest: *Forest) void {
            assert(forest.progress.? == .compact);
            const op = forest.progress.?.compact.op;

            const compaction_beat = op % constants.lsm_batch_multiple;
            const last_beat = compaction_beat == constants.lsm_batch_multiple - 1;

            // Finish all our compactions.
            forest.compaction_pipeline.beat_end();

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
                forest.compaction_pipeline.compactions.clear();
            }

            // Groove sync compaction - must be done after all async work for the beat completes???
            inline for (std.meta.fields(Grooves)) |field| {
                @field(forest.grooves, field.name).compact(op);
            }

            // FIXME - manifest log NB!
            // if (op % @divExact(constants.lsm_batch_multiple, 2) == 0) {
            //     assert(forest.manifest_log_progress == .idle);

            //     forest.manifest_log_progress = .compacting;
            //     // FIXME - manifest log reservation needs to be brought in with the above somehow
            //     // forest.manifest_log.compact(compact_manifest_log_callback, op);
            // } else {
            //     if (op == 1) {
            //         assert(forest.manifest_log_progress == .idle);
            //         forest.manifest_log_progress = .skip;
            //     } else {
            //         assert(forest.manifest_log_progress != .idle);
            //         // FIXME manifest hack
            //         forest.manifest_log_progress = .skip;
            //     }
            // }
        }

        // FIXME manifest log NB!
        // fn compact_manifest_log_callback(manifest_log: *ManifestLog) void {
        //     const forest = @fieldParentPtr(Forest, "manifest_log", manifest_log);
        //     assert(forest.manifest_log_progress == .compacting);

        //     forest.manifest_log_progress = .done;

        //     if (forest.progress) |progress| {
        //         assert(progress == .compact);

        //         forest.compact_callback();
        //     } else {
        //         // The manifest log compaction completed between compaction beats.
        //     }
        // }

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
