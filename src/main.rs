#![allow(non_snake_case)]
#![allow(dead_code)]

extern crate getopts;
extern crate time;
use std::io::{File, BufferedReader, Open, Write};
use minisat::core_solver::{Solver, CoreSolver};
use minisat::dimacs::{parse_DIMACS};

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
        let mut reader = BufferedReader::new(File::open(&Path::new(in_path.clone())));
        if !parse_DIMACS(&mut reader, &mut s, validate_DIMACS) { panic!("Failed to parse DIMACS file!"); }
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
        if ret.isTrue() { "SATISFIABLE" }
        else if ret.isFalse() { "UNSATISFIABLE" }
        else { "INDETERMINATE" } );

    match out_path {
        None           => (),
        Some(out_path) => {
            match File::open_mode(&Path::new(out_path), Open, Write) {
                Err(err) => {
                    let msg = format!("failed to open output file: {}", err);
                    assert!(std::io::stderr().write_line(msg.as_slice()).is_ok());
                }
                Ok(file) => {
                    let mut out = file;
                    if ret.isTrue() {
                        assert!(out.write_line("SAT").is_ok());
                        for i in range(0, s.nVars()) {
                            let val = s.model[i];
                            if !val.isUndef() {
                                let msg = format!("{}{}{}", if i == 0 { "" } else { " " }, if val.isTrue() { "" } else { "-" }, i + 1);
                                assert!(out.write_str(msg.as_slice()).is_ok());
                            }
                        }
                        assert!(out.write_line(" 0").is_ok());
                    } else if ret.isFalse() {
                        assert!(out.write_line("UNSAT").is_ok());
                    } else {
                        assert!(out.write_line("INDET").is_ok());
                    };
                }
            };
        }
    };
}

