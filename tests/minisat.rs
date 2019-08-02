
use tempfile;
use time;

use std::{fs, io, path, process};
use std::io::{Read, Seek};
use minisat_rust::sat::{dimacs, minisat, SolveRes, Solver, Stats};
use minisat_rust::sat::minisat::budget::Budget;


// TODO: come up with something better?
#[test]
fn compare_with_minisat_easy_0of4() {
    walk("./tests/cnf", 4, 0).expect("IO Error");
}

#[test]
fn compare_with_minisat_easy_1of4() {
    walk("./tests/cnf", 4, 1).expect("IO Error");
}

#[test]
fn compare_with_minisat_easy_2of4() {
    walk("./tests/cnf", 4, 2).expect("IO Error");
}

#[test]
fn compare_with_minisat_easy_3of4() {
    walk("./tests/cnf", 4, 3).expect("IO Error");
}


#[test]
#[ignore]
fn compare_with_minisat_hard() {
    walk("./tests/cnf-hard", 1, 0).expect("IO Error");
}


fn walk(dir_path: &str, bins: usize, bin: usize) -> io::Result<()> {
    let paths = {
        let mut paths = Vec::new();
        for _entry in fs::read_dir(dir_path)? {
            let entry = _entry?;
            if entry.file_type()?.is_file() {
                let path = entry.path();
                paths.push(path);
            }
        }
        paths.sort();
        paths
    };

    let mut sat = 0u64;
    let mut unsat = 0u64;
    for (_, path) in paths.iter().enumerate().filter(|(i, _)| i % bins == bin) {
        let outcome = test_file(path.as_path())?;
        if outcome {
            sat += 1;
        } else {
            unsat += 1;
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
            assert_eq!(stdout.last().unwrap(), "SATISFIABLE", "Different outcomes");
            test_stats(path, stats, &stdout);
            true
        }

        SolveRes::UnSAT(ref stats) => {
            assert_eq!(
                stdout.last().unwrap(),
                "UNSATISFIABLE",
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

    assert_eq!(
        minisat_result,
        result,
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
    assert_eq!(
        stats.restarts,
        parse_stats(&stdout[base + 0], &["restarts"]),
        "Number of restarts on {}\n{:?}",
        path.display(),
        stats
    );
    assert_eq!(
        stats.conflicts,
        parse_stats(&stdout[base + 1], &["conflicts"]),
        "Number of conflicts on {}\n{:?}",
        path.display(),
        stats
    );
    assert_eq!(
        stats.decisions,
        parse_stats(&stdout[base + 2], &["decisions"]),
        "Number of decisions on {}\n{:?}",
        path.display(),
        stats
    );
    assert_eq!(
        stats.propagations,
        parse_stats(&stdout[base + 3], &["propagations"]),
        "Number of propagations on {}\n{:?}",
        path.display(),
        stats
    );
    assert_eq!(
        stats.tot_literals,
        parse_stats(&stdout[base + 4], &["conflict", "literals"]),
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
