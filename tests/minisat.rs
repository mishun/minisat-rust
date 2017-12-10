extern crate minisat_rust;
extern crate tempfile;
extern crate time;

use std::{fs, io, path, process};
use std::io::{Read, Seek};
use minisat_rust::sat::{dimacs, minisat, SolveRes, Solver, Stats};
use minisat_rust::sat::minisat::budget::Budget;


#[test]
#[ignore]
fn compare_with_minisat() {
    walk().expect("IO Error");
}


fn walk() -> io::Result<()> {
    let mut sat = 0;
    let mut unsat = 0;

    for _entry in fs::read_dir("./tests/cnf")? {
        let entry = _entry?;
        if entry.file_type()?.is_file() {
            let ref path = entry.path();
            let outcome = test_file(path.as_path())?;
            if outcome {
                sat += 1;
            } else {
                unsat += 1;
            }
        }
    }

    println!("Done ({} sat, {} unsat)", sat, unsat);
    Ok(())
}


fn test_file(path: &path::Path) -> io::Result<bool> {
    let (minisat_result, stdout, minisat_time) = {
        let out_file = tempfile::NamedTempFile::new()?;
        let start_time = time::precise_time_s();
        let out = process::Command::new("minisat")
            .arg(path)
            .arg(out_file.path())
            .output()?;
        let end_time = time::precise_time_s();
        assert!(
            out.status.code() == Some(10) || out.status.code() == Some(20),
            "minisat error code on {}",
            path.display()
        );

        let output = {
            let mut buf = String::new();
            out_file.reopen()?.read_to_string(&mut buf)?;
            buf
        };

        assert!(!output.is_empty());

        let stdout: Vec<String> = {
            let mut buf = String::new();
            io::Cursor::new(out.stdout).read_to_string(&mut buf)?;
            buf.lines().map(|line| line.to_string()).collect()
        };

        let len = stdout.len();
        assert!(len > 10);

        (output, stdout, end_time - start_time)
    };

    let start_time = time::precise_time_s();
    let mut solver = minisat::SimpSolver::new(Default::default());

    let backward_subst = match dimacs::parse_file(path, &mut solver, false) {
        Ok(bs) => bs,
        Err(e) => panic!("Error parsing {}: {}", path.display(), e),
    };

    let res = {
        let mut budget = Budget::new();
        budget.off();
        if !solver.preprocess(&budget) {
            SolveRes::UnSAT(Default::default())
        } else {
            solver.solve_limited(&budget, &[])
        }
    };

    let my_time = time::precise_time_s() - start_time;

    let outcome = match res {
        SolveRes::SAT(_, ref stats) => {
            assert!(
                stdout.last().unwrap() == "SATISFIABLE",
                "Different outcomes"
            );
            test_stats(path, stats, &stdout);
            true
        }

        SolveRes::UnSAT(ref stats) => {
            assert!(
                stdout.last().unwrap() == "UNSATISFIABLE",
                "Different outcomes"
            );
            test_stats(path, stats, &stdout);
            false
        }

        _ => panic!("Unexpected result"),
    };

    let result = {
        let mut output = tempfile::tempfile()?;
        dimacs::write_result(&mut output, res, &backward_subst)?;
        output.seek(io::SeekFrom::Start(0))?;
        let mut buf = String::new();
        output.read_to_string(&mut buf)?;
        buf
    };

    assert!(
        minisat_result == result,
        "Result difference on {}",
        path.display()
    );

    println!(
        "ok ({:>5}):\t{:40}\t{:8.5}\t{:8.5}\t{:.2}",
        if outcome { "SAT" } else { "UNSAT" },
        path.display(),
        minisat_time,
        my_time,
        my_time / minisat_time
    );
    Ok(outcome)
}


fn test_stats(path: &path::Path, stats: &Stats, stdout: &Vec<String>) {
    let base = stdout.len() - 9;
    assert!(
        stats.restarts == parse_stats(&stdout[base + 0], &["restarts"]),
        "Number of restarts on {}\n{:?}",
        path.display(),
        stats
    );
    assert!(
        stats.conflicts == parse_stats(&stdout[base + 1], &["conflicts"]),
        "Number of conflicts on {}\n{:?}",
        path.display(),
        stats
    );
    assert!(
        stats.decisions == parse_stats(&stdout[base + 2], &["decisions"]),
        "Number of decisions on {}\n{:?}",
        path.display(),
        stats
    );
    assert!(
        stats.propagations == parse_stats(&stdout[base + 3], &["propagations"]),
        "Number of propagations on {}\n{:?}",
        path.display(),
        stats
    );
    assert!(
        stats.tot_literals == parse_stats(&stdout[base + 4], &["conflict", "literals"]),
        "Number of conflict literals on {}\n{:?}",
        path.display(),
        stats
    );
}

fn parse_stats(line: &String, header: &[&str]) -> u64 {
    let mut it = line.split(' ').filter(|s| !s.is_empty());
    for &word in header.iter() {
        assert_eq!(it.next(), Some(word));
    }
    assert_eq!(it.next(), Some(":"));
    it.next().and_then(|s| s.parse().ok()).unwrap()
}
