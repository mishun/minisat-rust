
pub fn luby(y: f64, mut x: u32) -> f64 {
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
