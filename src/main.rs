#![allow(non_snake_case)]
#![allow(dead_code)]

extern crate getopts;
extern crate time;

use std::io;
use std::io::{Read, Write};
use std::fs::File;
use minisat::solver::{Solver, CoreSolver};
use minisat::dimacs::{parse_DIMACS};
use minisat::lbool::{LBool};

mod minisat;


fn print_usage(opts: getopts::Options, program: &str) {
    let brief = format!("USAGE: {} [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n", program);
    println!("{}", opts.usage(&brief));
}

fn main() {
    let args : Vec<String> = std::env::args().collect();
    let program = args[0].clone();

    let mut opts = getopts::Options::new();
    opts.optopt("", "verb", "Verbosity level (0=silent, 1=some, 2=more)", "<VERB>");
    opts.optflag("h", "help", "Print this help menu");
    opts.optflag("", "strict", "Validate DIMACS header during parsing");

    let matches =
        match opts.parse(&args[1..]) {
            Ok(m)  => { m }
            Err(f) => { panic!(f.to_string()) }
        };

    if matches.opt_present("h") {
        print_usage(opts, &program);
        return;
    }

    let verbosity = matches.opt_str("verb").and_then(|s| { s.parse().ok() }).unwrap_or(1);
    let strict = matches.opt_present("strict");
    let (in_path, out_path) = {
        let left = matches.free;
        match left.len() {
            1 => { (left[0].clone(), None) }
            2 => { (left[0].clone(), Some(left[1].clone())) }
            _ => { print_usage(opts, &program); return; }
        }
    };

    let mut s = CoreSolver::new(verbosity);
    solveFile(&mut s, verbosity, strict, in_path, out_path).unwrap_or_else(|err| {
        panic!(format!("Error: {}", err));
    });
}


fn resToString(ret : LBool) -> &'static str {
    match () {
        _ if ret.isTrue()  => { "SATISFIABLE" }
        _ if ret.isFalse() => { "UNSATISFIABLE" }
        _                  => { "INDETERMINATE" }
    }
}

fn solveFile<S : Solver>(solver : &mut S, verbosity : i32, strict : bool, in_path : String, out_path : Option<String>) -> io::Result<()> {
    let initial_time = time::precise_time_s();

    if verbosity > 0 {
        println!("============================[ Problem Statistics ]=============================");
        println!("|                                                                             |");
    }

    {
        let in_file = try!(File::open(in_path));
        let reader = io::BufReader::new(in_file);
        try!(parse_DIMACS(reader.chars(), solver, strict));
    }

    if verbosity > 0 {
        println!("|  Number of variables:  {:12}                                         |", solver.nVars());
        println!("|  Number of clauses:    {:12}                                         |", solver.nClauses());
    }

    let parsed_time = time::precise_time_s();
    if verbosity > 0 {
        println!("|  Parse time:           {:12.2} s                                       |", parsed_time - initial_time);
        println!("|                                                                             |");
    }

    if !solver.simplify() {
        if verbosity > 0 {
            println!("===============================================================================");
            println!("Solved by unit propagation");
            solver.printStats();
        }
        println!("UNSATISFIABLE");
    } else {
        let ret = solver.solveLimited(&[]);
        solver.printStats();

        println!("{}", resToString(ret));
        match out_path {
            None       => {}
            Some(path) => {
                let mut out = try!(File::create(path));
                match () {
                    _ if ret.isTrue()  => {
                        try!(writeln!(&mut out, "SAT"));
                        let model = solver.getModel();
                        for i in 0 .. solver.nVars() {
                        let val = model[i];
                            if !val.isUndef() {
                                if i > 0 { try!(write!(&mut out, " ")); }
                                try!(write!(&mut out, "{}{}", if val.isTrue() { "" } else { "-" }, i + 1));
                            }
                        }
                        try!(writeln!(&mut out, " 0"));
                    }

                    _ if ret.isFalse() => { try!(writeln!(&mut out, "UNSAT")); }
                    _                  => { try!(writeln!(&mut out, "INDET")); }
                }
            }
        }
    }

    Ok(())
}
