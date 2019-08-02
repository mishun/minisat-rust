use std::process;
use std::fs::File;
use std::io::Read;

#[cfg(not(target_os = "linux"))]
pub fn mem_used_peak() -> Option<usize> {
    None
}

#[cfg(target_os = "linux")]
pub fn mem_used_peak() -> Option<usize> {
    let mut buf = String::new();
    let mut stats = File::open(&format!("/proc/{}/status", process::id())).expect("Couldn't open /proc/../status");
    stats.read_to_string(&mut buf).expect("Couldn't read from /proc/../status");
    let line = buf.lines()
                  .filter(|line| line.starts_with("VmPeak:"))
                  .next().expect("Couldn't find VmPeak in /proc/../status");
    let mem_kb: String = line.chars().filter(|c| c.is_digit(10)).collect();
    let mem_kb: usize = mem_kb.parse().unwrap();

    Some(mem_kb)
}
