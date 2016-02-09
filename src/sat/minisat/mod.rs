extern crate time;
use std::default::Default;
use sat::{PartialResult, TotalResult, Solver};
use sat::formula::{Var, Lit, LitMap};
use sat::formula::clause::*;
use sat::formula::assignment::*;
use self::clause_db::*;
use self::conflict::{AnalyzeContext, Seen, Conflict};
pub use self::conflict::CCMinMode;
use self::decision_heuristic::{DecisionHeuristicSettings, DecisionHeuristic};
pub use self::decision_heuristic::PhaseSaving;

mod budget;
mod clause_db;
mod conflict;
mod decision_heuristic;
pub mod simp;
mod util;
mod watches;


pub struct Settings {
    pub heur       : DecisionHeuristicSettings,
    pub db         : ClauseDBSettings,
    pub ccmin_mode : CCMinMode,
    pub restart    : RestartStrategy,
    pub learnt     : LearningStrategySettings,
    pub core       : CoreSettings
}

impl Default for Settings {
    fn default() -> Settings {
        Settings { heur       : Default::default()
                 , db         : Default::default()
                 , ccmin_mode : CCMinMode::Deep
                 , restart    : Default::default()
                 , learnt     : Default::default()
                 , core       : Default::default()
                 }
    }
}


pub struct RestartStrategy {
    pub luby_restart  : bool,
    pub restart_first : f64,   // The initial restart limit.
    pub restart_inc   : f64    // The factor with which the restart limit is multiplied in each restart.
}

impl RestartStrategy {
    pub fn conflictsToGo(&self, restarts : u32) -> u64 {
        let rest_base =
            if self.luby_restart {
                util::luby(self.restart_inc, restarts)
            } else {
                self.restart_inc.powi(restarts as i32)
            };

        (rest_base * self.restart_first) as u64
    }
}

impl Default for RestartStrategy {
    fn default() -> RestartStrategy {
        RestartStrategy { luby_restart      : true
                        , restart_first     : 100.0
                        , restart_inc       : 2.0
                        }
    }
}


pub struct LearningStrategySettings {
    pub min_learnts_lim         : i32,  // Minimum number to set the learnts limit to.
    pub size_factor             : f64,  // The intitial limit for learnt clauses is a factor of the original clauses.
    pub size_inc                : f64,  // The limit for learnt clauses is multiplied with this factor each restart.
    pub size_adjust_start_confl : i32,
    pub size_adjust_inc         : f64
}

impl Default for LearningStrategySettings {
    fn default() -> LearningStrategySettings {
        LearningStrategySettings { min_learnts_lim         : 0
                                 , size_factor             : 1.0 / 3.0
                                 , size_inc                : 1.1
                                 , size_adjust_start_confl : 100
                                 , size_adjust_inc         : 1.5
                                 }
    }
}

pub struct LearningStrategy {
    settings          : LearningStrategySettings,
    max_learnts       : f64,
    size_adjust_confl : f64,
    size_adjust_cnt   : i32
}

impl LearningStrategy {
    pub fn new(settings : LearningStrategySettings) -> LearningStrategy {
        LearningStrategy { settings          : settings
                         , max_learnts       : 0.0
                         , size_adjust_confl : 0.0
                         , size_adjust_cnt   : 0
                         }
    }

    pub fn reset(&mut self, clauses : usize) {
        self.max_learnts = ((clauses as f64) * self.settings.size_factor).max(self.settings.min_learnts_lim as f64);
        self.size_adjust_confl = self.settings.size_adjust_start_confl as f64;
        self.size_adjust_cnt   = self.settings.size_adjust_start_confl;
    }

    pub fn bump(&mut self) -> bool {
        self.size_adjust_cnt -= 1;
        if self.size_adjust_cnt == 0 {
            self.size_adjust_confl *= self.settings.size_adjust_inc;
            self.size_adjust_cnt = self.size_adjust_confl as i32;
            self.max_learnts *= self.settings.size_inc;
            true
        } else {
            false
        }
    }

    pub fn border(&self) -> usize {
        self.max_learnts as usize
    }
}


struct SimplifyGuard {
    simpDB_assigns : Option<usize>, // Number of top-level assignments since last execution of 'simplify()'.
    simpDB_props   : u64
}

impl SimplifyGuard {
    pub fn new() -> SimplifyGuard {
        SimplifyGuard { simpDB_assigns : None
                      , simpDB_props   : 0
                      }
    }

    pub fn skip(&self, assigns : usize, propagations : u64) -> bool {
        Some(assigns) == self.simpDB_assigns || propagations < self.simpDB_props
    }

    pub fn setNext(&mut self, assigns : usize, propagations : u64, prop_limit : u64) {
        self.simpDB_assigns = Some(assigns);
        self.simpDB_props   = propagations + prop_limit;
    }
}


enum SearchResult { UnSAT, SAT, Interrupted(f64), AssumpsConfl(LitMap<()>) }


pub struct CoreSettings {
    pub garbage_frac : f64,  // The fraction of wasted memory allowed before a garbage collection is triggered.
    pub use_rcheck   : bool, // Check if a clause is already implied. Prett costly, and subsumes subsumptions :)
}

impl Default for CoreSettings {
    fn default() -> CoreSettings {
        CoreSettings { garbage_frac : 0.20
                     , use_rcheck   : false
                     }
    }
}


#[derive(Default)]
struct Stats {
    solves       : u64,
    starts       : u64,
    decisions    : u64,
    conflicts    : u64,
    start_time   : f64
}

impl Stats {
    pub fn new() -> Stats {
        Stats { start_time : time::precise_time_s(), ..Default::default() }
    }
}


pub struct CoreSolver {
    settings      : CoreSettings,
    restart       : RestartStrategy,
    stats         : Stats,                  // Statistics: (read-only member variable)
    db            : ClauseDB,
    assigns       : Assignment,             // The current assignments.
    watches       : watches::Watches,       // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    heur          : DecisionHeuristic,
    ok            : bool,                   // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    simp          : SimplifyGuard,
    released_vars : Vec<Var>,
    analyze       : AnalyzeContext,
    learnt        : LearningStrategy,
    budget        : budget::Budget
}

impl Solver for CoreSolver {
    fn nVars(&self) -> usize {
        self.assigns.numberOfVars()
    }

    fn nClauses(&self) -> usize {
        self.db.num_clauses
    }

    fn newVar(&mut self, upol : Option<bool>, dvar : bool) -> Var {
        let v = self.assigns.newVar();
        self.watches.initVar(v);
        self.heur.initVar(v, upol, dvar);
        self.analyze.initVar(v);
        v
    }

    fn addClause(&mut self, clause : &[Lit]) -> bool {
        match self.addClause_(clause) {
            AddClause::UnSAT => { false }
            _                => { true }
        }
    }

    fn solve(&mut self) -> TotalResult {
        self.budget.off();
        match self.solveLimited(&[]) {
            PartialResult::UnSAT          => { TotalResult::UnSAT }
            PartialResult::SAT(model)     => { TotalResult::SAT(model) }
            PartialResult::Interrupted(_) => { TotalResult::Interrupted }
            // _                             => { panic!("Impossible happened") }
        }
    }

    fn printStats(&self) {
        let cpu_time = time::precise_time_s() - self.stats.start_time;

        info!("restarts              : {:<12}", self.stats.starts);
        info!("conflicts             : {:<12}   ({:.0} /sec)",
            self.stats.conflicts,
            (self.stats.conflicts as f64) / cpu_time);

        info!("decisions             : {:<12}   ({:4.2} % random) ({:.0} /sec)",
            self.stats.decisions,
            (self.heur.rnd_decisions as f64) * 100.0 / (self.stats.decisions as f64),
            (self.stats.decisions as f64) / cpu_time);

        info!("propagations          : {:<12}   ({:.0} /sec)",
            self.watches.propagations,
            (self.watches.propagations as f64) / cpu_time);

        info!("conflict literals     : {:<12}   ({:4.2} % deleted)",
            self.analyze.tot_literals,
            ((self.analyze.max_literals - self.analyze.tot_literals) as f64) * 100.0 / (self.analyze.max_literals as f64));

        info!("Memory used           : {:.2} MB", 0.0);
        info!("CPU time              : {} s", cpu_time);
        info!("");
    }
}

enum AddClause { UnSAT, Consumed, Added(ClauseRef) }

impl CoreSolver {
    pub fn new(settings : Settings) -> CoreSolver {
        CoreSolver { settings      : settings.core
                   , restart       : settings.restart
                   , stats         : Stats::new()
                   , db            : ClauseDB::new(settings.db)
                   , assigns       : Assignment::new()
                   , watches       : watches::Watches::new()
                   , heur          : DecisionHeuristic::new(settings.heur)
                   , simp          : SimplifyGuard::new()
                   , ok            : true
                   , released_vars : Vec::new()
                   , analyze       : AnalyzeContext::new(settings.ccmin_mode)
                   , learnt        : LearningStrategy::new(settings.learnt)
                   , budget        : budget::Budget::new()
                   }
    }

    fn addClause_(&mut self, clause : &[Lit]) -> AddClause {
        assert!(self.assigns.isGroundLevel());
        if !self.ok { return AddClause::UnSAT; }

        // TODO: it should be here to work identical to original MiniSat. Probably not the best place.
        if self.settings.use_rcheck && isImplied(self, &clause) {
            return AddClause::Consumed;
        }

        let ps = {
            let mut ps = clause.to_vec();

            // Check if clause is satisfied and remove false/duplicate literals:
            ps.sort();
            ps.dedup();
            ps.retain(|lit| { !self.assigns.isUnsat(*lit) });

            {
                let mut prev = None;
                for lit in ps.iter() {
                    if self.assigns.isSat(*lit) || prev == Some(!*lit) {
                        return AddClause::Consumed;
                    }
                    prev = Some(*lit);
                }
            }

            ps.into_boxed_slice()
        };

        match ps.len() {
            0 => {
                self.ok = false;
                AddClause::UnSAT
            }

            1 => {
                self.assigns.assignLit(ps[0], None);
                match self.watches.propagate(&mut self.db.ca, &mut self.assigns) {
                    None    => { AddClause::Consumed }
                    Some(_) => { self.ok = false; AddClause::UnSAT }
                }
            }

            _ => {
                let (c, cr) = self.db.addClause(ps);
                self.watches.watchClause(c, cr);
                AddClause::Added(cr)
            }
        }
    }

    // Description:
    //   Simplify the clause database according to the current top-level assigment. Currently, the only
    //   thing done here is the removal of satisfied clauses, but more things can be put here.
    pub fn simplify(&mut self) -> bool {
        assert!(self.assigns.isGroundLevel());
        if !self.ok { return false; }

        if let Some(_) = self.watches.propagate(&mut self.db.ca, &mut self.assigns) {
            self.ok = false;
            return false;
        }

        if self.simp.skip(self.assigns.numberOfAssigns(), self.watches.propagations) {
            return true;
        }

        self.db.removeSatisfied(&mut self.assigns, &mut self.watches);

        // TODO: why if?
        if self.db.settings.remove_satisfied {
            // Remove all released variables from the trail:
            for v in self.released_vars.iter() {
                assert!(self.analyze.seen[v] == Seen::Undef);
                self.analyze.seen[v] = Seen::Source;
            }

            {
                let seen = &self.analyze.seen;
                self.assigns.retainAssignments(|l| { seen[&l.var()] == Seen::Undef });
            }

            for v in self.released_vars.iter() {
                self.analyze.seen[v] = Seen::Undef;
            }

            // Released variables are now ready to be reused:
            for v in self.released_vars.iter() {
                self.assigns.freeVar(*v);
            }
            self.released_vars.clear();
        }

        if self.db.ca.checkGarbage(self.settings.garbage_frac) {
            self.garbageCollect();
        }

        self.heur.rebuildOrderHeap(&self.assigns);

        self.simp.setNext(self.assigns.numberOfAssigns(), self.watches.propagations, self.db.clauses_literals + self.db.learnts_literals); // (shouldn't depend on stats really, but it will do for now)

        true
    }

    // Revert to the state at given level (keeping all assignment at 'level' but not beyond).
    fn cancelUntil(&mut self, target_level : DecisionLevel) {
        let ref mut heur = self.heur;
        let top_level = self.assigns.decisionLevel();
        self.assigns.rewindUntilLevel(target_level, |level, lit| { heur.cancel(lit, level == top_level); });
    }

    pub fn solveLimited(&mut self, assumptions : &[Lit]) -> PartialResult {
        if !self.ok { return PartialResult::UnSAT; }

        self.stats.solves += 1;
        self.learnt.reset(self.db.num_clauses);

        info!("============================[ Search Statistics ]==============================");
        info!("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |");
        info!("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |");
        info!("===============================================================================");

        let result = self.searchLoop(assumptions);
        self.cancelUntil(GroundLevel);

        info!("===============================================================================");
        result
    }

    fn searchLoop(&mut self, assumptions : &[Lit]) -> PartialResult {
        let mut curr_restarts = 0;
        loop {
            let conflicts_to_go = self.restart.conflictsToGo(curr_restarts);
            curr_restarts += 1;

            match self.search(conflicts_to_go, assumptions) {
                SearchResult::SAT             => {
                    return PartialResult::SAT(extractModel(&self.assigns));
                }

                SearchResult::UnSAT           => {
                    self.ok = false;
                    return PartialResult::UnSAT;
                }

                SearchResult::AssumpsConfl(_) => { // TODO: implement
                    return PartialResult::UnSAT;
                }

                SearchResult::Interrupted(c)  => {
                    if !self.budget.within(self.stats.conflicts, self.watches.propagations) {
                        return PartialResult::Interrupted(c);
                    }
                }
            }
        }
    }

    // Description:
    //   Search for a model the specified number of conflicts. 
    //   NOTE! Use negative value for 'nof_conflicts' indicate infinity.
    // 
    // Output:
    //   'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
    //   all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
    //   if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
    fn search(&mut self, nof_conflicts : u64, assumptions : &[Lit]) -> SearchResult {
        assert!(self.ok);
        self.stats.starts += 1;

        let mut conflictC = 0;
        loop {
            match self.watches.propagate(&mut self.db.ca, &mut self.assigns) {
                Some(confl) => {
                    self.stats.conflicts += 1;
                    conflictC += 1;

                    match self.analyze.analyze(&mut self.db, &mut self.heur, &self.assigns, confl) {
                        Conflict::Ground => {
                            return SearchResult::UnSAT;
                        }

                        Conflict::Unit(level, unit) => {
                            self.cancelUntil(level);
                            self.assigns.assignLit(unit, None);
                        }

                        Conflict::Learned(level, lit, clause) => {
                            self.cancelUntil(level);
                            let (c, cr) = self.db.learnClause(clause);
                            self.watches.watchClause(c, cr);
                            self.assigns.assignLit(lit, Some(cr));
                        }
                    }


                    self.heur.decayActivity();
                    self.db.decayActivity();

                    if self.learnt.bump() {
                        info!("| {:9} | {:7} {:8} {:8} | {:8} {:8} {:6.0} | {:6.3} % |",
                               self.stats.conflicts,
                               self.heur.dec_vars - self.assigns.numberOfGroundAssigns(),
                               self.nClauses(),
                               self.db.clauses_literals,
                               self.learnt.border(),
                               self.db.num_learnts,
                               (self.db.learnts_literals as f64) / (self.db.num_learnts as f64),
                               progressEstimate(&self.assigns) * 100.0);
                    }
                }

                None        => {
                    if conflictC >= nof_conflicts || !self.budget.within(self.stats.conflicts, self.watches.propagations) {
                        // Reached bound on number of conflicts:
                        let progress_estimate = progressEstimate(&self.assigns);
                        self.cancelUntil(GroundLevel);
                        return SearchResult::Interrupted(progress_estimate);
                    }

                    // Simplify the set of problem clauses:
                    if self.assigns.isGroundLevel() && !self.simplify() {
                        return SearchResult::UnSAT;
                    }

                    if self.db.needReduce(self.assigns.numberOfAssigns() + self.learnt.border()) {
                        // Reduce the set of learnt clauses:
                        self.db.reduce(&mut self.assigns, &mut self.watches);
                        if self.db.ca.checkGarbage(self.settings.garbage_frac) {
                            self.garbageCollect();
                        }
                    }

                    let mut next = None;
                    while self.assigns.decisionLevel().offset() < assumptions.len() {
                        // Perform user provided assumption:
                        let p = assumptions[self.assigns.decisionLevel().offset()];
                        match self.assigns.ofLit(p) {
                            LitVal::True  => {
                                // Dummy decision level:
                                self.assigns.newDecisionLevel();
                            }
                            LitVal::False => {
                                let conflict = self.analyze.analyzeFinal(&self.db.ca, &self.assigns, !p);
                                return SearchResult::AssumpsConfl(conflict);
                            }
                            LitVal::Undef => {
                                next = Some(p);
                                break;
                            }
                        }
                    }

                    if let None = next {
                        // New variable decision:
                        self.stats.decisions += 1;
                        match self.heur.pickBranchLit(&self.assigns) {
                            Some(n) => { next = Some(n) }
                            None    => { return SearchResult::SAT; } // Model found:
                        };
                    }

                    // Increase decision level and enqueue 'next'
                    self.assigns.newDecisionLevel();
                    self.assigns.assignLit(next.unwrap(), None);
                }
            }
        }
    }

    fn garbageCollect(&mut self) {
        // Initialize the next region to a size corresponding to the estimated utilization degree. This
        // is not precise but should avoid some unnecessary reallocations for the new region:

        let to = ClauseAllocator::newForGC(&self.db.ca);
        self.relocAll(to);
    }

    fn relocAll(&mut self, mut to : ClauseAllocator) {
        self.watches.relocGC(&mut self.db.ca, &mut to);
        self.assigns.relocGC(&mut self.db.ca, &mut to);
        self.db.relocGC(to);
    }
}


fn isImplied(core : &mut CoreSolver, c : &[Lit]) -> bool {
    assert!(core.assigns.isGroundLevel());

    core.assigns.newDecisionLevel();
    for lit in c.iter() {
        match core.assigns.ofLit(*lit) {
            LitVal::True  => { core.cancelUntil(GroundLevel); return true; }
            LitVal::Undef => { core.assigns.assignLit(!*lit, None); }
            LitVal::False => {}
        }
    }

    let result = core.watches.propagate(&mut core.db.ca, &mut core.assigns).is_some();
    core.cancelUntil(GroundLevel);
    return result;
}
