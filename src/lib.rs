
#[macro_use]
extern crate log;
use time;

use std::{fs, io, path};
use crate::sat::*;
use crate::sat::minisat::budget::Budget;

pub mod sat;
pub(crate) mod util;


pub enum SolverOptions {
    Core(minisat::CoreSettings),
    Simp(minisat::SimpSettings),
}

pub struct MainOptions {
    pub strict: bool,
    pub pre: bool,
    pub solve: bool,
    pub in_path: path::PathBuf,
    pub out_path: Option<path::PathBuf>,
    pub dimacs_path: Option<path::PathBuf>,
}


pub fn solve(main_opts: MainOptions, solver_opts: SolverOptions) -> io::Result<()> {
    match solver_opts {
        SolverOptions::Core(opts) => {
            let solver = minisat::CoreSolver::new(opts);
            solve_with(solver, main_opts)
        }

        SolverOptions::Simp(opts) => {
            let mut solver = minisat::SimpSolver::new(opts);
            if !main_opts.pre {
                solver.preprocess(&Budget::new());
            }
            solve_with(solver, main_opts)
        }
    }
}


pub fn solve_with<S: Solver>(mut solver: S, options: MainOptions) -> io::Result<()> {
    info!("============================[ Problem Statistics ]=============================");
    info!("|                                                                             |");

    let initial_time = time::precise_time_s();
    let backward_subst = dimacs::parse_file(&options.in_path, &mut solver, options.strict)?;
    let parse_end_time = time::precise_time_s();

    info!("|  Number of variables:  {:12}                                         |", solver.n_vars());
    info!("|  Number of clauses:    {:12}                                         |", solver.n_clauses());

    {
        let parse_time = parse_end_time - initial_time;
        info!("|  Parse time:           {:12.2} s                                       |", parse_time);
    }

    let mut budget = Budget::new();
    budget.off();

    let elim_res = solver.preprocess(&budget);

    {
        let simplify_time = time::precise_time_s() - parse_end_time;
        info!("|  Simplification time:  {:12.2} s                                       |", simplify_time);
    }

    info!("|                                                                             |");

    let result = if !elim_res {
        info!("===============================================================================");
        info!("Solved by simplification");
        SolveRes::UnSAT(Stats::default())
    } else {
        let result =
            if options.solve {
                solver.solve_limited(&budget, &[])
            } else {
                info!("===============================================================================");
                SolveRes::Interrupted(0.0, solver)
            };

        //            if let TotalResult::Interrupted = result {
        //                if let Some(path) = options.dimacs_path {
        //                    let mut out = try!(fs::File::create(path));
        //                    try!(dimacs::write(&mut out, &solver));
        //                }
        //            }

        result
    };

    let cpu_time = time::precise_time_s() - initial_time;
    let mem_used = util::mem_used_peak();
    match result {
        SolveRes::UnSAT(ref stats) => {
            print_stats(stats, cpu_time, mem_used);
            println!("UNSATISFIABLE");
        }

        SolveRes::Interrupted(_, ref s) => {
            print_stats(&s.stats(), cpu_time, mem_used);
            println!("INDETERMINATE");
        }

        SolveRes::SAT(ref model, ref stats) => {
            print_stats(stats, cpu_time, mem_used);
            println!("SATISFIABLE");
            assert!(
                dimacs::validate_model_file(&options.in_path, &backward_subst, &model)?,
                "SELF-CHECK FAILED"
            );
        }
    }

    if let Some(path) = options.out_path {
        dimacs::write_result(fs::File::create(path)?, result, &backward_subst)?;
    }

    Ok(())
}

fn print_stats(stats: &Stats, cpu_time: f64, mem_used: Option<usize>) {
    info!("restarts              : {:<12}", stats.restarts);

    {
        let confl_per_s = (stats.conflicts as f64) / cpu_time;
        info!("conflicts             : {:<12}   ({:.0} /sec)", stats.conflicts, confl_per_s);
    }

    {
        let rnd_percent = (stats.rnd_decisions as f64) * 100.0 / (stats.decisions as f64);
        let decisions_per_s = (stats.decisions as f64) / cpu_time;
        info!("decisions             : {:<12}   ({:4.2} % random) ({:.0} /sec)", stats.decisions, rnd_percent, decisions_per_s);
    }

    {
        let props_per_s = (stats.propagations as f64) / cpu_time;
        info!("propagations          : {:<12}   ({:.0} /sec)", stats.propagations, props_per_s);
    }

    {
        let del_percent = (stats.del_literals as f64) * 100.0 / ((stats.del_literals + stats.tot_literals) as f64);
        info!("conflict literals     : {:<12}   ({:4.2} % deleted)", stats.tot_literals, del_percent);
    }

    if let Some(mem_used) = mem_used {
        info!("Memory used           : {:.2} MB", mem_used);
    }
    info!("CPU time              : {} s", cpu_time);
    info!("");
}
