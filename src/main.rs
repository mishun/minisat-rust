#![allow(non_snake_case)]
#![allow(dead_code)]

extern crate getopts;
extern crate time;
extern crate vec_map;
#[macro_use]
extern crate log;
extern crate env_logger;

use std::default::Default;
use std::io;
use std::io::{Write};
use std::fs::File;
use log::{LogRecord, LogLevelFilter};
use env_logger::LogBuilder;
use minisat::solver;
use minisat::solver::Solver;
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
    opts.optflag("", "core", "Use core solver");

    let matches =
        match opts.parse(&args[1..]) {
            Ok(m)  => { m }
            Err(f) => { panic!(f.to_string()) }
        };

    if matches.opt_present("h") {
        print_usage(opts, &program);
        return;
    }

    {
        let verbosity = matches.opt_str("verb").and_then(|s| { s.parse().ok() }).unwrap_or(1);
        let mut builder = LogBuilder::new();
        builder.format(|record: &LogRecord| { format!("{}", record.args()) });
        builder.filter(None,
            match verbosity {
                    1 => { LogLevelFilter::Info }
                    2 => { LogLevelFilter::Trace }
                    _ => { LogLevelFilter::Off }
            });
        builder.init().unwrap();
    }

    let strict = matches.opt_present("strict");
    let core = matches.opt_present("core");
    let (in_path, out_path) = {
        let left = matches.free;
        match left.len() {
            1 => { (left[0].clone(), None) }
            2 => { (left[0].clone(), Some(left[1].clone())) }
            _ => { print_usage(opts, &program); return; }
        }
    };

    (if core { solveFile(strict, in_path, out_path) } else { simpSolveFile(strict, in_path, out_path) }).unwrap_or_else(|err| {
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

fn solveFile(strict : bool, in_path : String, out_path : Option<String>) -> io::Result<()> {
    let mut solver = solver::CoreSolver::new(Default::default());
    let initial_time = time::precise_time_s();

    info!("============================[ Problem Statistics ]=============================");
    info!("|                                                                             |");

    {
        let in_file = try!(File::open(in_path));
        try!(parse_DIMACS(&mut io::BufReader::new(in_file), &mut solver, strict));
    }

    info!("|  Number of variables:  {:12}                                         |", solver.nVars());
    info!("|  Number of clauses:    {:12}                                         |", solver.nClauses());

    let parsed_time = time::precise_time_s();
    info!("|  Parse time:           {:12.2} s                                       |", parsed_time - initial_time);
    info!("|                                                                             |");

    if !solver.simplify() {
        info!("===============================================================================");
        info!("Solved by unit propagation");
        solver.printStats();
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

fn simpSolveFile(strict : bool, in_path : String, _ : Option<String>) -> io::Result<()> {
    let mut solver = solver::simp::SimpSolver::new(Default::default(), Default::default());
    let initial_time = time::precise_time_s();

    info!("============================[ Problem Statistics ]=============================");
    info!("|                                                                             |");

    {
        let in_file = try!(File::open(in_path));
        try!(parse_DIMACS(&mut io::BufReader::new(in_file), &mut solver, strict));
    }

    info!("|  Number of variables:  {:12}                                         |", solver.nVars());
    info!("|  Number of clauses:    {:12}                                         |", solver.nClauses());

    let parsed_time = time::precise_time_s();
    info!("|  Parse time:           {:12.2} s                                       |", parsed_time - initial_time);

    let elim_res = solver.eliminate(true);
    let simplified_time = time::precise_time_s();

    info!("|  Simplification time:  {:12.2} s                                       |", simplified_time - parsed_time);
    info!("|                                                                             |");

    if !elim_res {
        //if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);

        info!("===============================================================================");
        info!("Solved by simplification");
        solver.printStats();
        info!("");

        println!("UNSATISFIABLE");
    } else {
        let ret = solver.solveLimited(&[], true, false);
        solver.printStats();
        println!("{}", resToString(ret));
    }

    Ok(())
}
