const std = @import("std");
const assert = std.debug.assert;

pub const Gen = struct {
    const N = 32;

    started: bool = false,
    val: [N]u32 = undefined,
    lim: [N]u32 = undefined,
    len: u8 = 0,
    pos: u8 = 0,

    pub fn done(g: *Gen) bool {
        if (!g.started) {
            g.started = true;
            return false;
        }
        var i = g.len + 1;
        while (i > 0) {
            i -= 1;
            if (g.val[i] < g.lim[i]) {
                g.val[i] += 1;
                g.pos = 0;
                g.len = i + 1;
                return false;
            }
        }
        return true;
    }

    pub fn gen(g: *Gen, bound: u32) u32 {
        if (g.pos == g.len) {
            g.val[g.pos] = 0;
            g.len += 1;
        }
        g.pos += 1;
        g.lim[g.pos - 1] = bound;
        return g.val[g.pos - 1];
    }
};

test "exhaustigen" {
    const n = 5;
    var g = Gen{};

    var total: u32 = 0;
    while (!g.done()) {
        const i = g.gen(n);
        const j = g.gen(i);
        assert(i <= n);
        assert(j <= i);
        total += 1;
    }
    assert(total == @divExact((n + 1) * (n + 2), 2));
}
