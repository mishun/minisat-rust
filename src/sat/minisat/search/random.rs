
pub struct Random {
    seed: f64,
}

impl Random {
    pub fn new(seed: f64) -> Random {
        Random { seed }
    }

    // Returns a random float 0 <= x < 1. Seed must never be 0.
    pub fn drand(&mut self) -> f64 {
        self.seed *= 1389796.0;
        let q = (self.seed / 2147483647.0) as i32;
        self.seed -= (q as f64) * 2147483647.0;
        self.seed / 2147483647.0
    }

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    pub fn irand(&mut self, size: usize) -> usize {
        (self.drand() * (size as f64)) as usize
    }

    pub fn chance(&mut self, p: f64) -> bool {
        self.drand() < p
    }
}
