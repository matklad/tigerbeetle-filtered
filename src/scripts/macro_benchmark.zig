const std = @import("std");

const Shell = @import("../shell.zig");

pub fn main(shell: *Shell, gpa: std.mem.Allocator) !void {
    _ = gpa;

    var timer = try std.time.Timer.start();
    try shell.zig("build install -Drelease", .{});
    const build_time_ms = timer.lap() / std.time.ns_per_ms;

    const executable_size_bytes = (try shell.cwd.statFile("tigerbeetle")).size;

    const run = Run{
        .timestamp = std.time.timestamp(),
        .revision = "todo",
        .measurements = &[_]Measurement{
            .{ .label = "build time", .value = build_time_ms, .unit = "ms" },
            .{ .label = "executable size", .value = executable_size_bytes, .unit = "bytes" },
        },
    };

    try shell.exec("git clone git@github.com:matklad/gitdb --depth 1 gitdb", .{});

    try shell.pushd("./gitdb");
    defer shell.popd();

    {
        const file = try shell.cwd.openFile("./macro-benchmark/data.json", .{
            .mode = .write_only,
        });
        defer file.close();

        try file.seekFromEnd(0);
        try std.json.stringify(run, .{}, file.writer());
        try file.writeAll("\n");
    }

    try shell.exec("git add ./macro-benchmark/data.json", .{});
    try shell.exec("git commit -m 📈", .{});
    try shell.exec("git push", .{});
}

const Measurement = struct {
    label: []const u8,
    value: u64,
    unit: []const u8,
};

const Run = struct {
    timestamp: i64,
    revision: []const u8,
    measurements: []const Measurement,
};
