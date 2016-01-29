#![allow(non_snake_case)]

extern crate time;
extern crate vec_map;
#[macro_use] extern crate log;
extern crate env_logger;
#[macro_use] extern crate clap;

use std::default::Default;
use std::io;
use std::io::Write;
use std::fs::File;
use minisat::lbool::LBool;
use minisat::decision_heuristic::PhaseSaving;
use minisat::conflict::CCMinMode;
use minisat::solver;
use minisat::solver::Solver;
use minisat::dimacs;

mod minisat;


fn main() {
    let ls012 = ["0", "1", "2"];
    let matches =
        clap::App::new("minisat-rust")
        .version(&crate_version!()[..])
        .about("Minisat reimplementation in Rust")

        .arg(clap::Arg::with_name("core").long("core"))

        .arg(clap::Arg::with_name("verb").long("verb").takes_value(true).possible_values(&ls012).help("Verbosity level (0=silent, 1=some, 2=more)"))
        .arg(clap::Arg::with_name("strict").long("strict").help("Validate DIMACS header during parsing"))
        .arg(clap::Arg::with_name("pre").long("pre").help("Completely turn on/off any preprocessing"))
        .arg(clap::Arg::with_name("no-pre").long("no-pre").conflicts_with("pre"))
        .arg(clap::Arg::with_name("solve").long("solve").help("Completely turn on/off solving after preprocessing"))
        .arg(clap::Arg::with_name("no-solve").long("no-solve").conflicts_with("solve"))
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

        .arg(clap::Arg::with_name("asymm").long("asymm").help("Shrink clauses by asymmetric branching"))
        .arg(clap::Arg::with_name("no-asymm").long("no-asymm").conflicts_with("asymm"))
        .arg(clap::Arg::with_name("rcheck").long("rcheck").help("Check if a clause is already implied. (costly)"))
        .arg(clap::Arg::with_name("no-rcheck").long("no-rcheck").conflicts_with("rcheck"))
        .arg(clap::Arg::with_name("elim").long("elim").help("Perform variable elimination"))
        .arg(clap::Arg::with_name("no-elim").long("no-elim").conflicts_with("elim"))
        .arg(clap::Arg::with_name("grow").long("grow").takes_value(true).help("Allow a variable elimination step to grow by a number of clauses"))
        .arg(clap::Arg::with_name("cl-lim").long("cl-lim").takes_value(true).help("Variables are not eliminated if it produces a resolvent with a length above this limit. -1 means no limit"))
        .arg(clap::Arg::with_name("sub-lim").long("sub-lim").takes_value(true).help("Do not check if subsumption against a clause larger than this. -1 means no limit."))
        .arg(clap::Arg::with_name("simp-gc-frac").long("simp-gc-frac").takes_value(true).help("The fraction of wasted memory allowed before a garbage collection is triggered during simplification."))

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
        let mut s : solver::Settings = Default::default();

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

        if matches.is_present("luby") { s.core.luby_restart = true; }
        if matches.is_present("no-luby") { s.core.luby_restart = false; }

        for x in matches.value_of("rfirst").and_then(|s| s.parse().ok()).iter() {
            if 0 < *x { s.core.restart_first = *x; }
        }

        for x in matches.value_of("rinc").and_then(|s| s.parse().ok()).iter() {
            if 1.0 < *x { s.core.restart_inc = *x; }
        }

        for x in matches.value_of("gc-frac").and_then(|s| s.parse().ok()).iter() {
            if 0.0 < *x && *x <= 1.0 { s.core.garbage_frac = *x; }
        }

        for x in matches.value_of("min-learnts").and_then(|s| s.parse().ok()).iter() {
            if 0 <= *x { s.core.min_learnts_lim = *x; }
        }

        s
    };

    let simp_options = {
        let mut s : solver::simp::SimpSettings = Default::default();

        if matches.is_present("asymm") { s.use_asymm = true; }
        if matches.is_present("no-asymm") { s.use_asymm = false; }

        if matches.is_present("rcheck") { s.use_rcheck = true; }
        if matches.is_present("no-rcheck") { s.use_rcheck = false; }

        if matches.is_present("elim") { s.use_elim = true; }
        if matches.is_present("no-elim") { s.use_elim = false; }

        for x in matches.value_of("grow").and_then(|s| s.parse().ok()).iter() {
            s.grow = *x;
        }

        for x in matches.value_of("cl-lim").and_then(|s| s.parse().ok()).iter() {
            if -1 <= *x { s.clause_lim = *x; }
        }

        for x in matches.value_of("sub-lim").and_then(|s| s.parse().ok()).iter() {
            if -1 <= *x { s.subsumption_lim = *x; }
        }

        for x in matches.value_of("simp-gc-frac").and_then(|s| s.parse().ok()).iter() {
            if 0.0 < *x && *x <= 1.0 { s.simp_garbage_frac = *x; }
        }

        s
    };

    let strict = matches.is_present("strict");
    let in_path = matches.value_of("input").unwrap().to_string();
    let out_path = matches.value_of("output").map(|x| x.to_string());

    if matches.is_present("core") {
        solveFile(solver::CoreSolver::new(core_options), strict, in_path, out_path).expect("Error");
    } else {
        simpSolveFile(solver::simp::SimpSolver::new(core_options, simp_options), strict, in_path, out_path).expect("Error");
    }
}

fn resToString(ret : LBool) -> &'static str {
    match () {
        _ if ret.isTrue()  => { "SATISFIABLE" }
        _ if ret.isFalse() => { "UNSATISFIABLE" }
        _                  => { "INDETERMINATE" }
    }
}

fn solveFile(mut solver : solver::CoreSolver, strict : bool, in_path : String, out_path : Option<String>) -> io::Result<()> {
    let initial_time = time::precise_time_s();

    info!("============================[ Problem Statistics ]=============================");
    info!("|                                                                             |");

    {
        let in_file = try!(File::open(in_path));
        try!(dimacs::parse(&mut io::BufReader::new(in_file), &mut solver, strict));
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

fn simpSolveFile(mut solver : solver::simp::SimpSolver, strict : bool, in_path : String, _ : Option<String>) -> io::Result<()> {
    let initial_time = time::precise_time_s();

    info!("============================[ Problem Statistics ]=============================");
    info!("|                                                                             |");

    {
        let in_file = try!(File::open(in_path));
        try!(dimacs::parse(&mut io::BufReader::new(in_file), &mut solver, strict));
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
