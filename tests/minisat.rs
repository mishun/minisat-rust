extern crate tempfile;
extern crate minisat_rust;

use std::{io, fs, path, process};
use std::io::{Read, Seek};
use minisat_rust::sat::{dimacs, minisat, Solver, TotalResult};


#[test]
#[ignore]
fn compare_with_minisat() {
    walk().expect("IO Error");
}


fn walk() -> io::Result<()> {
    for _entry in try!(fs::read_dir("./tests/cnf")) {
        let entry = try!(_entry);
        if try!(entry.file_type()).is_file() {
            try!(test_file(entry.path().as_path()));
        }
    }

    Ok(())
}


fn test_file(path : &path::Path) -> io::Result<()> {
    let (minisat_result, stdout) = {
        let out_file = try!(tempfile::NamedTempFile::new());
        let out = try!(process::Command::new("minisat").arg(path).arg(out_file.path()).output());
        assert!(out.status.code() == Some(10) || out.status.code() == Some(20), "minisat error code on {}", path.display());

        let output = {
            let mut buf = String::new();
            try!(try!(out_file.reopen()).read_to_string(&mut buf));
            buf
        };

        assert!(!output.is_empty());

        let stdout : Vec<String> = {
            let mut buf = String::new();
            try!(io::Cursor::new(out.stdout).read_to_string(&mut buf));
            buf.lines().map(|line| line.to_string()).collect()
        };

        let len = stdout.len();
        assert!(len > 10);
        assert!(stdout[len - 1] == "UNSATISFIABLE" || stdout[len - 1] == "SATISFIABLE");

        (output, stdout)
    };

    let opts = Default::default();
    let mut solver = minisat::simp::SimpSolver::new(opts);

    let backward_subst =
        match dimacs::parseFile(path, &mut solver, false) {
            Ok(bs) => { bs }
            Err(e) => { panic!("Error parsing {}: {}", path.display(), e) }
        };

    let mut output = try!(tempfile::tempfile());
    let res =
        if !solver.preprocess() {
            TotalResult::UnSAT
        } else {
            solver.solve()
        };
    try!(dimacs::writeResult(&mut output, res, &backward_subst));

    let stats = solver.stats();
    let base = stdout.len() - 9;
    assert!(stats.restarts     == parse_stats(&stdout[base + 0], &["restarts"]), "Number of restarts on {}", path.display());
    assert!(stats.conflicts    == parse_stats(&stdout[base + 1], &["conflicts"]), "Number of conflicts on {}", path.display());
    assert!(stats.decisions    == parse_stats(&stdout[base + 2], &["decisions"]), "Number of decisions on {}", path.display());
    assert!(stats.propagations == parse_stats(&stdout[base + 3], &["propagations"]), "Number of propagations on {}", path.display());
    assert!(stats.tot_literals == parse_stats(&stdout[base + 4], &["conflict", "literals"]), "Number of conflict literals on {}", path.display());

    let result = {
        try!(output.seek(io::SeekFrom::Start(0)));
        let mut buf = String::new();
        try!(output.read_to_string(&mut buf));
        buf
    };

    assert!(minisat_result == result, "Result difference on {}", path.display());
    Ok(())
}


fn parse_stats(line : &String, header : &[&str]) -> u64 {
    let mut it = line.split(' ').filter(|s| !s.is_empty());
    for &word in header.iter() {
        assert_eq!(it.next(), Some(word));
    }
    assert_eq!(it.next(), Some(":"));
    it.next().and_then(|s| s.parse().ok()).unwrap()
}
