#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

extern crate time;
extern crate vec_map;
#[macro_use] extern crate log;
extern crate flate2;

use std::{fs, path};
use std::io::{self, Write};
use sat::{minisat, dimacs, TotalResult, Solver};

pub mod sat;


pub enum SolverOptions {
    Core(minisat::Settings),
    Simp(minisat::simp::Settings)
}

pub struct MainOptions {
    pub strict      : bool,
    pub pre         : bool,
    pub solve       : bool,
    pub in_path     : path::PathBuf,
    pub out_path    : Option<path::PathBuf>,
    pub dimacs_path : Option<path::PathBuf>
}


pub fn solve(main_opts : MainOptions, solver_opts : SolverOptions) -> io::Result<()> {
    match solver_opts {
        SolverOptions::Core(opts) => {
            let solver = minisat::CoreSolver::new(opts);
            solveWith(solver, main_opts)
        }

        SolverOptions::Simp(opts) => {
            let mut solver = minisat::simp::SimpSolver::new(opts);
            if !main_opts.pre { solver.eliminate(true); }
            solveWith(solver, main_opts)
        }
    }
}


pub fn solveWith<S : Solver>(mut solver : S, options : MainOptions) -> io::Result<()> {
    let initial_time = time::precise_time_s();

    info!("============================[ Problem Statistics ]=============================");
    info!("|                                                                             |");

    let backward_subst = try!(dimacs::parseFile(&options.in_path, &mut solver, options.strict));

    info!("|  Number of variables:  {:12}                                         |", solver.nVars());
    info!("|  Number of clauses:    {:12}                                         |", solver.nClauses());

    let parsed_time = time::precise_time_s();
    info!("|  Parse time:           {:12.2} s                                       |", parsed_time - initial_time);

    let elim_res = solver.preprocess();
    {
        let simplified_time = time::precise_time_s();
        info!("|  Simplification time:  {:12.2} s                                       |", simplified_time - parsed_time);
    }

    info!("|                                                                             |");

    let result =
        if !elim_res {
            info!("===============================================================================");
            info!("Solved by simplification");
            solver.printStats();
            info!("");
            TotalResult::UnSAT
        } else {
            let result =
                if options.solve {
                    solver.solve()
                } else {
                    info!("===============================================================================");
                    TotalResult::Interrupted
                };

            if let TotalResult::Interrupted = result {
                if let Some(path) = options.dimacs_path {
                    let mut out = try!(fs::File::create(path));
                    try!(dimacs::write(&mut out, &solver));
                }
            }

            solver.printStats();
            result
        };

    println!("{}",
        match result {
            TotalResult::SAT(_)      => { "SATISFIABLE" }
            TotalResult::UnSAT       => { "UNSATISFIABLE" }
            TotalResult::Interrupted => { "INDETERMINATE" }
        });

    if let Some(path) = options.out_path {
        let mut file = try!(fs::File::create(path));
        match result {
            TotalResult::UnSAT          => { try!(writeln!(file, "UNSAT")); }
            TotalResult::Interrupted    => { try!(writeln!(file, "INDET")); }
            TotalResult::SAT(ref model) => {
                try!(writeln!(file, "SAT"));
                try!(dimacs::writeModel(&mut file, &backward_subst, &model));
            }
        }
    }

    if let TotalResult::SAT(ref model) = result {
        assert!(try!(dimacs::validateModelFile(&options.in_path, &backward_subst, &model)), "SELF-CHECK FAILED!");
    }

    Ok(())
}
