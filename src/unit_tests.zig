test {
    _ = @import("aof.zig");
    _ = @import("copyhound.zig");
    _ = @import("ewah.zig");
    _ = @import("fifo.zig");
    _ = @import("flags.zig");
    _ = @import("io.zig");
    _ = @import("repl.zig");
    _ = @import("ring_buffer.zig");
    _ = @import("shell.zig");
    _ = @import("stdx.zig");
    _ = @import("tidy.zig");

    _ = @import("clients/c/test.zig");
    _ = @import("clients/c/tb_client_header_test.zig");
    _ = @import("clients/dotnet/dotnet_bindings.zig");
    _ = @import("clients/go/go_bindings.zig");
    _ = @import("clients/java/java_bindings.zig");
    _ = @import("clients/node/node_bindings.zig");

    _ = @import("lsm/binary_search.zig");
    _ = @import("lsm/cache_map.zig");
    _ = @import("lsm/composite_key.zig");
    _ = @import("lsm/forest.zig");
    _ = @import("lsm/forest_table_iterator.zig");
    _ = @import("lsm/groove.zig");
    _ = @import("lsm/k_way_merge.zig");
    _ = @import("lsm/manifest_level.zig");
    _ = @import("lsm/node_pool.zig");
    _ = @import("lsm/segmented_array.zig");
    _ = @import("lsm/set_associative_cache.zig");
    _ = @import("lsm/table.zig");
    _ = @import("lsm/table_memory.zig");
    _ = @import("lsm/tree.zig");

    _ = @import("state_machine.zig");
    _ = @import("state_machine/auditor.zig");
    _ = @import("state_machine/workload.zig");

    _ = @import("testing/id.zig");
    _ = @import("testing/snaptest.zig");
    _ = @import("testing/storage.zig");
    _ = @import("testing/table.zig");
    _ = @import("testing/tmp_tigerbeetle.zig");

    _ = @import("vsr.zig");
    _ = @import("vsr/client.zig");
    _ = @import("vsr/clock.zig");
    _ = @import("vsr/checksum.zig");
    _ = @import("vsr/grid_blocks_missing.zig");
    _ = @import("vsr/journal.zig");
    _ = @import("vsr/marzullo.zig");
    _ = @import("vsr/replica_format.zig");
    _ = @import("vsr/replica_test.zig");
    _ = @import("vsr/superblock.zig");
    _ = @import("vsr/free_set.zig");
    _ = @import("vsr/superblock_quorums.zig");
    _ = @import("vsr/sync.zig");

    _ = @import("scripts/release.zig");
}
