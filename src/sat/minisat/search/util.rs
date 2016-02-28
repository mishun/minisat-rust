
pub struct Random {
    seed : f64
}

impl Random {
    pub fn new(seed : f64) -> Random {
        Random { seed : seed }
    }

    // Returns a random float 0 <= x < 1. Seed must never be 0.
    pub fn drand(&mut self) -> f64 {
        self.seed *= 1389796.0;
        let q = (self.seed / 2147483647.0) as i32;
        self.seed -= (q as f64) * 2147483647.0;
        self.seed / 2147483647.0
    }

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    pub fn irand(&mut self, size : usize) -> usize {
        (self.drand() * (size as f64)) as usize
    }

    pub fn chance(&mut self, p : f64) -> bool {
        self.drand() < p
    }
}


pub fn luby(y : f64, mut x : u32) -> f64 {
    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    let mut size = 1;
    let mut seq = 0;

    while size < x + 1 {
        seq += 1;
        size = 2 * size + 1;
    }

    while size - 1 != x {
        size = (size - 1) >> 1;
        seq -= 1;
        x = x % size;
    }

    y.powi(seq)
}
