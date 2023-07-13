const Gen = struct {
  started: bool = false,
  v: [32]struct { val: u32, lim: u32} = [_].{ .{ .val = 0, .lim = 0} } * 32,
  p: usize = 0,
  p_max: usize = 0,

  fn done(gen: *Gen) bool {
    if (!gen.started) {
        gen.started = true;
        return false;
    }
    var i = p;
    while (i > 0) {
        i -= 1;
        if (gen.v[i].val < gen.v[i].lim) {
            gen.v[i].val += 1;
            gen.p_max = i + 1;
            gen.p = 0;
            return false;
        }
    }
    return true;
  }

  fn gen(gen: *Gen, bound: u32) u32 {
    if (self.p == self.p_max) {

    }
    self.p += 1;
    self.v[self.p - 1].lim = bound;
    return self.v[self.p - 1].val;
  }
};
