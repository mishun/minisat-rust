#![allow(non_snake_case)]
#![allow(dead_code)]

extern crate getopts;
extern crate time;

use std::io;
use minisat::core_solver::{Solver, CoreSolver};
use minisat::dimacs::{parse_DIMACS};
use minisat::lbool::{LBool};

mod minisat;


fn main() {
    let (in_path, out_path, verbosity, validate_DIMACS) = {
        let opts =
            [ getopts::optopt("", "verb", "Verbosity level (0=silent, 1=some, 2=more)", "<VERB>")
            , getopts::optflag("h", "help", "Print this help menu")
            , getopts::optflag("", "strict", "Validate DIMACS header during parsing")
            ];

        let print_usage = || {
            let program = std::os::args()[0].clone();
            let brief = format!("USAGE: {} [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n", program);
            println!("{}", getopts::usage(brief.as_slice(), &opts));
        };

        let matches =
            match getopts::getopts(std::os::args().tail(), &opts) {
                Ok(m)  => { m }
                Err(f) => { panic!(f.to_string()) }
            };

        if matches.opt_present("h") { print_usage(); return; };

        let (inf, outf) : (String, Option<String>) =
            match matches.free.as_slice() {
                [ref inf]           => { (inf.clone(), None) }
                [ref inf, ref outf] => { (inf.clone(), Some(outf.clone())) }
                _                   => { print_usage(); return; }
            };

        let verb = matches.opt_str("verb").and_then(|s| { from_str::<int>(s.as_slice()) }).unwrap_or(1);
        (inf, outf, verb, matches.opt_present("strict"))
    };

    let mut s = CoreSolver::new(verbosity);
    let initial_time = time::precise_time_s();

    if verbosity > 0 {
        println!("============================[ Problem Statistics ]=============================");
        println!("|                                                                             |");
    }

    {
        let mut reader = io::BufferedReader::new(io::File::open(&Path::new(in_path.clone())));
        parse_DIMACS(&mut reader, &mut s, validate_DIMACS).unwrap_or_else(|err| {
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
            s.stats.print();
            println!("");
        }
        println!("UNSATISFIABLE");
        return;
    }

    let ret = s.solveLimited(&[]);
    if verbosity > 0 {
        s.stats.print();
        println!("");
    }

    println!("{}",
        match () {
            _ if ret.isTrue()  => { "SATISFIABLE" }
            _ if ret.isFalse() => { "UNSATISFIABLE" }
            _                  => { "INDETERMINATE" }
        });

    out_path.map_or((), |out_path| {
        writeResult(&out_path, ret, &s).unwrap_or_else(|err| {
            let _ = writeln!(&mut io::stderr(), "failed to open output file: {}", err);
        })
    });
}


fn writeResult(path : &String, ret : LBool, s : &CoreSolver) -> io::IoResult<()> {
    let mut out = try!(io::File::open_mode(&Path::new(path), io::Open, io::Write));
    match () {
        _ if ret.isTrue()  => {
            try!(writeln!(&mut out, "SAT"));
            for i in range(0, s.nVars()) {
                let val = s.model[i];
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
