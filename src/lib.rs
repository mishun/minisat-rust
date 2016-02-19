#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

extern crate time;
extern crate vec_map;
#[macro_use] extern crate log;
extern crate flate2;

use std::{io, fs, path};
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

            result
        };

    {
        let cpu_time = time::precise_time_s() - initial_time;
        let stats = solver.stats();

        info!("restarts              : {:<12}", stats.restarts);
        info!("conflicts             : {:<12}   ({:.0} /sec)", stats.conflicts, (stats.conflicts as f64) / cpu_time);

        info!("decisions             : {:<12}   ({:4.2} % random) ({:.0} /sec)",
            stats.decisions,
            (stats.rnd_decisions as f64) * 100.0 / (stats.decisions as f64),
            (stats.decisions as f64) / cpu_time
        );

        info!("propagations          : {:<12}   ({:.0} /sec)",  stats.propagations, (stats.propagations as f64) / cpu_time);

        info!("conflict literals     : {:<12}   ({:4.2} % deleted)",
            stats.tot_literals,
            (stats.del_literals as f64) * 100.0 / (stats.tot_literals as f64)
        );

        info!("Memory used           : {:.2} MB", 0.0);
        info!("CPU time              : {} s", cpu_time);
        info!("");
    }

    match result {
        TotalResult::UnSAT       => {
            println!("UNSATISFIABLE");
        }

        TotalResult::Interrupted => {
            println!("INDETERMINATE");
        }

        TotalResult::SAT(ref model)  => {
            println!("SATISFIABLE");
            assert!(try!(dimacs::validateModelFile(&options.in_path, &backward_subst, &model)), "SELF-CHECK FAILED");
        }
    }

    if let Some(path) = options.out_path {
        try!(dimacs::writeResult(try!(fs::File::create(path)), result, &backward_subst));
    }

    Ok(())
}
