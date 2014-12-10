#![allow(non_snake_case)]
#![allow(dead_code)]

extern crate getopts;
extern crate time;

use std::io;
use minisat::solver::{Solver, CoreSolver};
use minisat::dimacs::{parse_DIMACS};
use minisat::lbool::{LBool};

mod minisat;


fn print_usage(opts : &[getopts::OptGroup]) {
    let program = std::os::args()[0].clone();
    let brief = format!("USAGE: {} [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n", program);
    println!("{}", getopts::usage(brief.as_slice(), opts));
}

fn main() {
    let opts =
        [ getopts::optopt("", "verb", "Verbosity level (0=silent, 1=some, 2=more)", "<VERB>")
        , getopts::optflag("h", "help", "Print this help menu")
        , getopts::optflag("", "strict", "Validate DIMACS header during parsing")
        ];

    let matches =
        match getopts::getopts(std::os::args().tail(), &opts) {
            Ok(m)  => { m }
            Err(f) => { panic!(f.to_string()) }
        };

    if matches.opt_present("h") {
        print_usage(&opts);
        return;
    }

    let verbosity = matches.opt_str("verb").and_then(|s| { from_str::<int>(s.as_slice()) }).unwrap_or(1);
    let mut s = CoreSolver::new(verbosity);
    solveFile(&mut s, &matches, &opts);
}


fn resToString(ret : LBool) -> &'static str {
    match () {
        _ if ret.isTrue()  => { "SATISFIABLE" }
        _ if ret.isFalse() => { "UNSATISFIABLE" }
        _                  => { "INDETERMINATE" }
    }
}

fn solveFile<S : Solver>(s : &mut S, matches : &getopts::Matches, opts : &[getopts::OptGroup]) {
    let verbosity = matches.opt_str("verb").and_then(|s| { from_str::<int>(s.as_slice()) }).unwrap_or(1);
    let (in_path, out_path) =
        match matches.free.as_slice() {
            [ref inf]           => { (inf.clone(), None) }
            [ref inf, ref outf] => { (inf.clone(), Some(outf.clone())) }
            _                   => { print_usage(opts); return; }
        };

    let initial_time = time::precise_time_s();

    if verbosity > 0 {
        println!("============================[ Problem Statistics ]=============================");
        println!("|                                                                             |");
    }

    {
        let mut reader = io::BufferedReader::new(io::File::open(&Path::new(in_path.clone())));
        parse_DIMACS(&mut reader, s, matches.opt_present("strict")).unwrap_or_else(|err| {
            panic!(format!("Failed to parse DIMACS file: {}", err));
        })
    }

    if verbosity > 0 {
        println!("|  Number of variables:  {:12}                                         |", s.nVars());
        println!("|  Number of clauses:    {:12}                                         |", s.nClauses());
    }

    let parsed_time = time::precise_time_s();
    if verbosity > 0 {
        println!("|  Parse time:           {:12.2} s                                       |", parsed_time - initial_time);
        println!("|                                                                             |");
    }

    if !s.simplify() {
        if verbosity > 0 {
            println!("===============================================================================");
            println!("Solved by unit propagation");
            s.printStats();
        }
        println!("UNSATISFIABLE");
        return;
    }

    let ret = s.solveLimited(&[]);
    s.printStats();

    println!("{}", resToString(ret));
    out_path.map_or((), |out_path| {
        writeResult(&out_path, ret, s).unwrap_or_else(|err| {
            panic!("failed to open output file: {}", err);
        })
    });
}

fn writeResult<S : Solver>(path : &String, ret : LBool, s : &S) -> io::IoResult<()> {
    let mut out = try!(io::File::open_mode(&Path::new(path), io::Open, io::Write));
    match () {
        _ if ret.isTrue()  => {
            try!(writeln!(&mut out, "SAT"));
            let model = s.getModel();
            for i in range(0, s.nVars()) {
                let val = model[i];
                if !val.isUndef() {
                    if i > 0 { try!(write!(&mut out, " ")); }
                    try!(write!(&mut out, "{}{}", if val.isTrue() { "" } else { "-" }, i + 1));
                }
            }
            writeln!(&mut out, " 0")
        }

        _ if ret.isFalse() => { writeln!(&mut out, "UNSAT") }
        _                  => { writeln!(&mut out, "INDET") }
    }
}
