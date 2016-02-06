#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

extern crate time;
extern crate vec_map;
#[macro_use] extern crate log;
extern crate env_logger;
#[macro_use] extern crate clap;

use std::fs;
use std::io;
use minisat::{TotalResult, Solver};
use minisat::formula::index_map::VarMap;
use minisat::decision_heuristic::PhaseSaving;
use minisat::conflict::CCMinMode;
use minisat::solver;
use minisat::dimacs;

mod minisat;


struct MainOptions {
    strict      : bool,
    pre         : bool,
    solve       : bool,
    in_path     : String,
    out_path    : Option<String>,
    dimacs_path : Option<String>
}

fn main() {
    let ls012 = ["0", "1", "2"];
    let matches =
        clap::App::new("minisat-rust")
        .version(&crate_version!()[..])
        .about("Minisat reimplementation in Rust")

        .arg(clap::Arg::with_name("verb").long("verb").takes_value(true).possible_values(&ls012).help("Verbosity level (0=silent, 1=some, 2=more)"))
        .arg(clap::Arg::with_name("core").long("core").help("Use core solver"))
        .arg(clap::Arg::with_name("strict").long("strict").help("Validate DIMACS header during parsing"))
        .arg(clap::Arg::with_name("pre").long("pre").help("Completely turn on/off any preprocessing"))
        .arg(clap::Arg::with_name("no-pre").long("no-pre").conflicts_with("pre"))
        .arg(clap::Arg::with_name("solve").long("solve").help("Completely turn on/off solving after preprocessing"))
        .arg(clap::Arg::with_name("no-solve").long("no-solve").conflicts_with("solve"))
        .arg(clap::Arg::with_name("dimacs").long("dimacs").takes_value(true).requires("no-solve").help("If given, stop after preprocessing and write the result to this file"))
        .arg(clap::Arg::with_name("input").required(true))
        .arg(clap::Arg::with_name("output").required(false))

        .arg(clap::Arg::with_name("var-decay").long("var-decay").takes_value(true).help("The variable activity decay factor"))
        .arg(clap::Arg::with_name("cla-decay").long("cla-decay").takes_value(true).help("The clause activity decay factor"))
        .arg(clap::Arg::with_name("rnd-freq").long("rnd-freq").takes_value(true).help("The frequency with which the decision heuristic tries to choose a random variable"))
        .arg(clap::Arg::with_name("rnd-seed").long("rnd-seed").takes_value(true).help("Used by the random variable selection"))
        .arg(clap::Arg::with_name("ccmin-mode").long("ccmin-mode").takes_value(true).possible_values(&ls012).help("Controls conflict clause minimization (0=none, 1=basic, 2=deep)"))
        .arg(clap::Arg::with_name("phase-saving").long("phase-saving").takes_value(true).possible_values(&ls012).help("Controls the level of phase saving (0=none, 1=limited, 2=full)"))
        .arg(clap::Arg::with_name("rnd-init").long("rnd-init").help("Randomize the initial activity"))
        .arg(clap::Arg::with_name("no-rnd-init").long("no-rnd-init").conflicts_with("rnd-init"))
        .arg(clap::Arg::with_name("luby").long("luby").help("Use the Luby restart sequence"))
        .arg(clap::Arg::with_name("no-luby").long("no-luby").conflicts_with("luby"))
        .arg(clap::Arg::with_name("rfirst").long("rfirst").takes_value(true).help("The base restart interval"))
        .arg(clap::Arg::with_name("rinc").long("rinc").takes_value(true).help("Restart interval increase factor"))
        .arg(clap::Arg::with_name("gc-frac").long("gc-frac").takes_value(true).help("The fraction of wasted memory allowed before a garbage collection is triggered"))
        .arg(clap::Arg::with_name("min-learnts").long("min-learnts").takes_value(true).help("Minimum learnt clause limit"))
        .arg(clap::Arg::with_name("rcheck").long("rcheck").help("Check if a clause is already implied. (costly)"))
        .arg(clap::Arg::with_name("no-rcheck").long("no-rcheck").conflicts_with("rcheck"))

        .arg(clap::Arg::with_name("asymm").long("asymm").conflicts_with("core").help("Shrink clauses by asymmetric branching"))
        .arg(clap::Arg::with_name("no-asymm").long("no-asymm").conflicts_with("asymm").conflicts_with("core"))
        .arg(clap::Arg::with_name("elim").long("elim").conflicts_with("core").help("Perform variable elimination"))
        .arg(clap::Arg::with_name("no-elim").long("no-elim").conflicts_with("elim").conflicts_with("core"))
        .arg(clap::Arg::with_name("grow").long("grow").takes_value(true).conflicts_with("core").help("Allow a variable elimination step to grow by a number of clauses"))
        .arg(clap::Arg::with_name("cl-lim").long("cl-lim").takes_value(true).conflicts_with("core").help("Variables are not eliminated if it produces a resolvent with a length above this limit. -1 means no limit"))
        .arg(clap::Arg::with_name("sub-lim").long("sub-lim").takes_value(true).conflicts_with("core").help("Do not check if subsumption against a clause larger than this. -1 means no limit."))
        .arg(clap::Arg::with_name("simp-gc-frac").long("simp-gc-frac").takes_value(true).conflicts_with("core").help("The fraction of wasted memory allowed before a garbage collection is triggered during simplification."))

        .get_matches();

    {
        let mut builder = env_logger::LogBuilder::new();
        builder.format(|record: &log::LogRecord| { format!("{}", record.args()) });
        builder.filter(None,
            matches.value_of("verb").map(|v| {
                match v {
                    "1" => { log::LogLevelFilter::Info }
                    "2" => { log::LogLevelFilter::Trace }
                    _   => { log::LogLevelFilter::Off }
                }
            }).unwrap_or(log::LogLevelFilter::Info));
        builder.init().unwrap();
    }

    let core_options = {
        let mut s = solver::Settings::default();

        for x in matches.value_of("var-decay").and_then(|s| s.parse().ok()).iter() {
            if 0.0 < *x && *x < 1.0 { s.heur.var_decay = *x; }
        }

        for x in matches.value_of("cla-decay").and_then(|s| s.parse().ok()).iter() {
            if 0.0 < *x && *x < 1.0 { s.db.clause_decay = *x; }
        }

        for x in matches.value_of("rnd-freq").and_then(|s| s.parse().ok()).iter() {
            if 0.0 <= *x && *x <= 1.0 { s.heur.random_var_freq = *x; }
        }

        for x in matches.value_of("rnd-seed").and_then(|s| s.parse().ok()).iter() {
            if 0.0 < *x { s.heur.random_seed = *x; }
        }

        for x in matches.value_of("ccmin-mode").iter() {
            match *x {
                "0" => { s.ccmin_mode = CCMinMode::None; }
                "1" => { s.ccmin_mode = CCMinMode::Basic; }
                "2" => { s.ccmin_mode = CCMinMode::Deep; }
                _   => {}
            }
        }

        for x in matches.value_of("phase_saving").iter() {
            match *x {
                "0" => { s.heur.phase_saving = PhaseSaving::None; }
                "1" => { s.heur.phase_saving = PhaseSaving::Limited; }
                "2" => { s.heur.phase_saving = PhaseSaving::Full; }
                _   => {}
            }
        }

        if matches.is_present("rnd-init") { s.heur.rnd_init_act = true; }
        if matches.is_present("no-rnd-init") { s.heur.rnd_init_act = false; }

        if matches.is_present("luby") { s.restart.luby_restart = true; }
        if matches.is_present("no-luby") { s.restart.luby_restart = false; }

        for x in matches.value_of("rfirst").and_then(|s| s.parse().ok()).iter() {
            if 0.0 < *x { s.restart.restart_first = *x; }
        }

        for x in matches.value_of("rinc").and_then(|s| s.parse().ok()).iter() {
            if 1.0 < *x { s.restart.restart_inc = *x; }
        }

        for x in matches.value_of("gc-frac").and_then(|s| s.parse().ok()).iter() {
            if 0.0 < *x && *x <= 1.0 { s.core.garbage_frac = *x; }
        }

        for x in matches.value_of("min-learnts").and_then(|s| s.parse().ok()).iter() {
            if 0 <= *x { s.learnt.min_learnts_lim = *x; }
        }

        if matches.is_present("rcheck") { s.core.use_rcheck = true; }
        if matches.is_present("no-rcheck") { s.core.use_rcheck = false; }

        s
    };

    let options =
        MainOptions {
            strict      : matches.is_present("strict"),
            pre         : !matches.is_present("no-pre"),
            solve       : !matches.is_present("no-solve"),
            in_path     : matches.value_of("input").unwrap().to_string(),
            out_path    : matches.value_of("output").map(|x| x.to_string()),
            dimacs_path : matches.value_of("dimacs").map(|x| x.to_string())
        };

    if matches.is_present("core") {
        let solver = solver::CoreSolver::new(core_options);
        solveFileCore(solver, options).expect("Error");
    } else {
        let simp_options = {
            let mut s = solver::simp::Settings::default();
            s.core = core_options;

            if matches.is_present("asymm") { s.simp.use_asymm = true; }
            if matches.is_present("no-asymm") { s.simp.use_asymm = false; }

            if matches.is_present("elim") { s.simp.use_elim = true; }
            if matches.is_present("no-elim") { s.simp.use_elim = false; }

            for x in matches.value_of("grow").and_then(|s| s.parse().ok()).iter() {
                s.simp.grow = *x;
            }

            for x in matches.value_of("cl-lim").and_then(|s| s.parse().ok()).iter() {
                if -1 <= *x { s.simp.clause_lim = *x; }
            }

            for x in matches.value_of("sub-lim").and_then(|s| s.parse().ok()).iter() {
                if -1 <= *x { s.simp.subsumption_lim = *x; }
            }

            for x in matches.value_of("simp-gc-frac").and_then(|s| s.parse().ok()).iter() {
                if 0.0 < *x && *x <= 1.0 { s.simp.simp_garbage_frac = *x; }
            }

            s
        };

        let solver = solver::simp::SimpSolver::new(simp_options);
        solveFileSimp(solver, options).expect("Error");
    }
}

fn solveFileCore(mut solver : solver::CoreSolver, options : MainOptions) -> io::Result<()> {
    let initial_time = time::precise_time_s();

    info!("============================[ Problem Statistics ]=============================");
    info!("|                                                                             |");

    let backward_subst = {
        let in_file = try!(fs::File::open(options.in_path.clone()));
        try!(dimacs::parse(&mut io::BufReader::new(in_file), &mut solver, options.strict))
    };

    info!("|  Number of variables:  {:12}                                         |", solver.nVars());
    info!("|  Number of clauses:    {:12}                                         |", solver.nClauses());

    let parsed_time = time::precise_time_s();
    info!("|  Parse time:           {:12.2} s                                       |", parsed_time - initial_time);
    info!("|                                                                             |");

    let result =
        if !solver.simplify() {
            info!("===============================================================================");
            info!("Solved by unit propagation");
            solver.printStats();
            TotalResult::UnSAT
        } else {
            let result = solver.solve();
            solver.printStats();
            result
        };

    printOutcome(&result);
    if let Some(path) = options.out_path {
        let mut out = try!(fs::File::create(path));
        try!(writeResultTo(&mut out, &backward_subst, &result));
    }

    if let TotalResult::SAT(ref model) = result {
        let in_file = try!(fs::File::open(options.in_path));
        let ok = try!(dimacs::validateModel(&mut io::BufReader::new(in_file), &backward_subst, &model));
        if !ok {
            println!("SELF-CHECK FAILED!!!");
        }
    }

    Ok(())
}

fn solveFileSimp(mut solver : solver::simp::SimpSolver, options : MainOptions) -> io::Result<()> {
    if !options.pre { solver.eliminate(true); }
    let initial_time = time::precise_time_s();

    info!("============================[ Problem Statistics ]=============================");
    info!("|                                                                             |");

    let backward_subst = {
        let in_file = try!(fs::File::open(options.in_path.clone()));
        try!(dimacs::parse(&mut io::BufReader::new(in_file), &mut solver, options.strict))
    };

    info!("|  Number of variables:  {:12}                                         |", solver.nVars());
    info!("|  Number of clauses:    {:12}                                         |", solver.nClauses());

    let parsed_time = time::precise_time_s();
    info!("|  Parse time:           {:12.2} s                                       |", parsed_time - initial_time);

    let elim_res = solver.eliminate(true);

    let simplified_time = time::precise_time_s();
    info!("|  Simplification time:  {:12.2} s                                       |", simplified_time - parsed_time);
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

    printOutcome(&result);
    if let Some(path) = options.out_path {
        let mut out = try!(fs::File::create(path));
        try!(writeResultTo(&mut out, &backward_subst, &result));
    }

    if let TotalResult::SAT(ref model) = result {
        let in_file = try!(fs::File::open(options.in_path));
        let ok = try!(dimacs::validateModel(&mut io::BufReader::new(in_file), &backward_subst, &model));
        if !ok {
            println!("SELF-CHECK FAILED!!!");
        }
    }

    Ok(())
}

fn printOutcome(ret : &TotalResult) {
    println!("{}",
        match *ret {
            TotalResult::SAT(_)      => { "SATISFIABLE" }
            TotalResult::UnSAT       => { "UNSATISFIABLE" }
            TotalResult::Interrupted => { "INDETERMINATE" }
        });
}

fn writeResultTo<W : io::Write>(stream : &mut W, backward_subst : &VarMap<i32>, ret : &TotalResult) -> io::Result<()> {
    match *ret {
        TotalResult::UnSAT          => { try!(writeln!(stream, "UNSAT")); Ok(()) }
        TotalResult::Interrupted    => { try!(writeln!(stream, "INDET")); Ok(()) }
        TotalResult::SAT(ref model) => {
            try!(writeln!(stream, "SAT"));
            dimacs::writeModel(stream, backward_subst, &model)
        }
    }
}

