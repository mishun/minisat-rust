extern crate tempfile;
extern crate minisat_rust;

use std::io::{self, Read};
use std::fs;
use std::path;
use std::process;
use minisat_rust::*;


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
    let target = try!(run_minisat(path));
    let test = try!(run_me(path));
    assert!(target == test, "Difference on file {:?}\nExpected:\n{}\nGot:\n{}", path, target, test);
    Ok(())
}


fn run_minisat(cnf_path : &path::Path) -> io::Result<String> {
    let result = try!(tempfile::NamedTempFile::new());
    try!(process::Command::new("minisat")
            .arg(cnf_path)
            .arg(result.path())
            .output()
    );

    let mut buf = String::new();
    try!(try!(result.reopen()).read_to_string(&mut buf));
    Ok(buf)
}


fn run_me(cnf_path : &path::Path) -> io::Result<String> {
    let result = try!(tempfile::NamedTempFile::new());

    let opts =
        MainOptions {
            strict      : false,
            pre         : true,
            solve       : true,
            in_path     : cnf_path.to_path_buf(),
            out_path    : Some(result.path().to_path_buf()),
            dimacs_path : None
        };

    try!(solve(opts, SolverOptions::Simp(Default::default())));

    let mut buf = String::new();
    try!(try!(result.reopen()).read_to_string(&mut buf));
    Ok(buf)
}
