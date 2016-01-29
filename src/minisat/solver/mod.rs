extern crate time;

use std::default::Default;
use std::sync::atomic;
use super::util;
use super::index_map::IndexMap;
use super::literal::{Var, Lit};
use super::lbool::LBool;
use super::clause::*;
use super::propagation_trail::{DecisionLevel, PropagationTrail};
use super::assignment::*;
use super::watches::*;
use super::decision_heuristic::*;
use super::conflict::*;
use super::clause_db::*;

pub mod simp;


pub trait Solver {
    fn nVars(&self) -> usize;
    fn nClauses(&self) -> usize;
    fn newVar(&mut self, upol : LBool, dvar : bool) -> Var;
    fn addClause(&mut self, clause : &[Lit]) -> bool;
    fn getModel(&self) -> &Vec<LBool>;
    fn printStats(&self);
}



pub struct Settings {
    pub heur       : DecisionHeuristicSettings,
    pub db         : ClauseDBSettings,
    pub ccmin_mode : CCMinMode,
    pub core       : CoreSettings
}

impl Default for Settings {
    fn default() -> Settings {
        Settings { heur       : Default::default()
                 , db         : Default::default()
                 , ccmin_mode : CCMinMode::Deep
                 , core       : Default::default()
                 }
    }
}


pub struct CoreSettings {
    pub luby_restart      : bool,
    pub garbage_frac      : f64,         // The fraction of wasted memory allowed before a garbage collection is triggered.
    pub min_learnts_lim   : i32,         // Minimum number to set the learnts limit to.
    pub restart_first     : i32,         // The initial restart limit.                                                                (default 100)
    pub restart_inc       : f64,         // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
    pub learntsize_factor : f64,         // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
    pub learntsize_inc    : f64,         // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)

    pub learntsize_adjust_start_confl : i32,
    pub learntsize_adjust_inc : f64
}

impl Default for CoreSettings {
    fn default() -> CoreSettings {
        CoreSettings { luby_restart      : true
                     , garbage_frac      : 0.20
                     , min_learnts_lim   : 0
                     , restart_first     : 100
                     , restart_inc       : 2.0
                     , learntsize_factor : 1.0 / 3.0
                     , learntsize_inc    : 1.1

                     , learntsize_adjust_start_confl : 100
                     , learntsize_adjust_inc : 1.5
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


// Resource contraints:
struct Budget {
    conflict_budget    : i64, // -1 means no budget.
    propagation_budget : i64, // -1 means no budget.
    asynch_interrupt   : atomic::AtomicBool
}

impl Budget {
    pub fn new() -> Budget {
        Budget { conflict_budget    : -1
               , propagation_budget : -1
               , asynch_interrupt   : atomic::AtomicBool::new(false)
               }
    }

    pub fn within(&self, conflicts : u64, propagations : u64) -> bool {
        !self.asynch_interrupt.load(atomic::Ordering::Relaxed) &&
            (self.conflict_budget    < 0 || conflicts < self.conflict_budget as u64) &&
            (self.propagation_budget < 0 || propagations < self.propagation_budget as u64)
    }

    pub fn interrupted(&self) -> bool {
        self.asynch_interrupt.load(atomic::Ordering::Relaxed)
    }

    pub fn off(&mut self) {
        self.conflict_budget = -1;
        self.propagation_budget = -1;
    }
}


pub struct CoreSolver {
    settings           : CoreSettings,

    model              : Vec<LBool>,             // If problem is satisfiable, this vector contains the model (if any).
    conflict           : IndexMap<Lit, ()>,

    stats              : Stats,   // Statistics: (read-only member variable)

    // Solver state:
    db                 : ClauseDB,
    trail              : PropagationTrail<Lit>,       // Assignment stack; stores all assigments made in the order they were made.
    assumptions        : Vec<Lit>,                    // Current set of assumptions provided to solve by the user.
    assigns            : Assignment,                  // The current assignments.
    watches            : Watches,                     // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    heur               : DecisionHeuristic,

    ok                 : bool,          // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    simpDB_assigns     : Option<usize>, // Number of top-level assignments since last execution of 'simplify()'.
    simpDB_props       : i64,           // Remaining number of propagations that must be made before next execution of 'simplify()'.
    progress_estimate  : f64,           // Set by 'search()'.

    released_vars      : Vec<Var>,

    analyze : AnalyzeContext,

    max_learnts             : f64,
    learntsize_adjust_confl : f64,
    learntsize_adjust_cnt   : i32,

    budget : Budget
}

impl Solver for CoreSolver {
    fn nVars(&self) -> usize {
        self.assigns.nVars()
    }

    fn nClauses(&self) -> usize {
        self.db.num_clauses
    }

    fn newVar(&mut self, upol : LBool, dvar : bool) -> Var {
        let v = self.assigns.newVar(VarData { reason : None, level : 0 });
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

    fn getModel(&self) -> &Vec<LBool> {
        &self.model
    }

    fn printStats(&self) {
        let cpu_time = time::precise_time_s() - self.stats.start_time;
        //double mem_used = memUsedPeak();
        info!("restarts              : {:12}", self.stats.starts);
        info!("conflicts             : {:12}   ({:.0} / sec)",
            self.stats.conflicts,
            (self.stats.conflicts as f64) / cpu_time);

        info!("decisions             : {:12}   ({:4.2} % random) ({:.0} / sec)",
            self.stats.decisions,
            (self.heur.rnd_decisions as f64) * 100.0 / (self.stats.decisions as f64),
            (self.stats.decisions as f64) / cpu_time);

        info!("propagations          : {:12}   ({:.0} / sec)",
            self.watches.propagations,
            (self.watches.propagations as f64) / cpu_time);

        info!("conflict literals     : {:12}   ({:4.2} % deleted)",
            self.analyze.tot_literals,
            ((self.analyze.max_literals - self.analyze.tot_literals) as f64) * 100.0 / (self.analyze.max_literals as f64));

        //if (mem_used != 0) printf("Memory used           : %.2f MB\n", mem_used);
        info!("CPU time              : {} s", cpu_time);
        info!("");
    }
}

enum AddClause { UnSAT, Consumed, Added(ClauseRef) }

impl CoreSolver {
    pub fn new(settings : Settings) -> CoreSolver {
        CoreSolver {
            settings : settings.core,

            model : Vec::new(),
            conflict : IndexMap::new(),

            stats : Stats::new(),

            db    : ClauseDB::new(settings.db),
            trail : PropagationTrail::new(),
            assumptions : Vec::new(),

            assigns : Assignment::new(),
            watches : Watches::new(),
            heur    : DecisionHeuristic::new(settings.heur),

            ok : true,
            simpDB_assigns : None,
            simpDB_props : 0,
            progress_estimate : 0.0,

            released_vars : Vec::new(),

            analyze : AnalyzeContext::new(settings.ccmin_mode),

            max_learnts : 0.0,
            learntsize_adjust_confl : 0.0,
            learntsize_adjust_cnt : 0,

            budget : Budget::new()
        }
    }

    fn addClause_(&mut self, clause : &[Lit]) -> AddClause {
        assert!(self.trail.isGroundLevel());
        if !self.ok { return AddClause::UnSAT; }

        let mut ps = clause.to_vec();

        // Check if clause is satisfied and remove false/duplicate literals:
        ps.sort();
        ps.dedup();
        ps.retain(|lit| { !self.assigns.unsat(*lit) });

        {
            let mut prev = None;
            for lit in ps.iter() {
                if self.assigns.sat(*lit) || prev == Some(!*lit) {
                    return AddClause::Consumed;
                }
                prev = Some(*lit);
            }
        }

        match ps.len() {
            0 => {
                self.ok = false;
                AddClause::UnSAT
            }

            1 => {
                self.uncheckedEnqueue(ps[0], None);
                match self.propagate() {
                    None    => { AddClause::Consumed }
                    Some(_) => { self.ok = false; AddClause::UnSAT }
                }
            }

            _ => {
                let cr = self.db.addClause(&ps);
                self.db.attachClause(&mut self.watches, cr);
                AddClause::Added(cr)
            }
        }
    }

    pub fn solve(&mut self, assumps : &[Lit]) -> bool {
        self.budget.off();
        self.solveLimited(assumps).isTrue()
    }

    pub fn solveLimited(&mut self, assumps : &[Lit]) -> LBool {
        self.assumptions = assumps.to_vec();
        self.solve_()
    }

    //_________________________________________________________________________________________________
    //
    // simplify : [void]  ->  [bool]
    //
    // Description:
    //   Simplify the clause database according to the current top-level assigment. Currently, the only
    //   thing done here is the removal of satisfied clauses, but more things can be put here.
    //_______________________________________________________________________________________________@
    pub fn simplify(&mut self) -> bool {
        assert!(self.trail.isGroundLevel());
        if !self.ok { return false; }

        if let Some(_) = self.propagate() {
            self.ok = false;
            return false;
        }

        if Some(self.trail.totalSize()) == self.simpDB_assigns || self.simpDB_props > 0 {
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
                self.trail.retain(|l| { seen[&l.var()] == Seen::Undef });
            }

            for v in self.released_vars.iter() {
                self.analyze.seen[v] = Seen::Undef;
            }

            // Released variables are now ready to be reused:
            for v in self.released_vars.iter() { self.assigns.freeVar(v); }
            self.released_vars.clear();
        }

        if self.db.ca.checkGarbage(self.settings.garbage_frac) {
            self.garbageCollect();
        }

        self.heur.rebuildOrderHeap(&self.assigns);

        self.simpDB_assigns = Some(self.trail.totalSize());
        self.simpDB_props   = (self.db.clauses_literals + self.db.learnts_literals) as i64; // (shouldn't depend on stats really, but it will do for now)

        true
    }

    // Revert to the state at given level (keeping all assignment at 'level' but not beyond).
    fn cancelUntil(&mut self, target_level : DecisionLevel) {
        let ref mut assigns = self.assigns;
        let ref mut heur = self.heur;

        let top_level = self.trail.decisionLevel();
        self.trail.cancelUntil(target_level,
            |level, lit| {
                let x = lit.var();
                assigns.cancel(x);
                heur.cancel(lit, level == top_level);
            });
    }

    fn solve_(&mut self) -> LBool {
        self.model.clear();
        self.conflict.clear();
        if !self.ok { return LBool::False() }
        self.stats.solves += 1;

        self.max_learnts = (self.nClauses() as f64 * self.settings.learntsize_factor).max(self.settings.min_learnts_lim as f64);
        self.learntsize_adjust_confl = self.settings.learntsize_adjust_start_confl as f64;
        self.learntsize_adjust_cnt   = self.settings.learntsize_adjust_start_confl;
        let mut status = LBool::Undef();

        info!("============================[ Search Statistics ]==============================");
        info!("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |");
        info!("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |");
        info!("===============================================================================");

        // Search:
        {
            let mut curr_restarts = 0;
            while status.isUndef() {
                let rest_base =
                    match self.settings.luby_restart {
                        true  => { util::luby(self.settings.restart_inc, curr_restarts) }
                        false => { self.settings.restart_inc.powi(curr_restarts as i32) }
                    };
                let conflicts_to_go = rest_base * (self.settings.restart_first as f64);
                status = self.search(conflicts_to_go as usize);
                if !self.budget.within(self.stats.conflicts, self.watches.propagations) { break; }
                curr_restarts += 1;
            }
        }

        info!("===============================================================================");

        if status.isTrue() {
            let vars = self.nVars();
            self.model.resize(vars, LBool::Undef());
            for i in 0 .. vars {
                self.model[i] = self.assigns.ofVar(Var::new(i));
            }
        } else if status.isFalse() && self.conflict.is_empty() {
            self.ok = false;
        }

        self.cancelUntil(0);
        status
    }

    //_________________________________________________________________________________________________
    //
    // search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
    // 
    // Description:
    //   Search for a model the specified number of conflicts. 
    //   NOTE! Use negative value for 'nof_conflicts' indicate infinity.
    // 
    // Output:
    //   'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
    //   all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
    //   if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
    //_______________________________________________________________________________________________@
    fn search(&mut self, nof_conflicts : usize) -> LBool {
        assert!(self.ok);
        self.stats.starts += 1;

        let mut conflictC = 0;
        loop {
            match self.propagate() {
                Some(confl) => {
                    self.stats.conflicts += 1;
                    conflictC += 1;
                    if self.trail.isGroundLevel() { return LBool::False() }

                    let (backtrack_level, learnt_clause) = self.analyze.analyze(&mut self.db, &mut self.heur, &self.assigns, &self.trail, confl);
                    self.cancelUntil(backtrack_level);
                    match learnt_clause.len() {
                        1 => { self.uncheckedEnqueue(learnt_clause[0], None) }
                        _ => {
                            let cr = self.db.learnClause(&learnt_clause);
                            self.db.attachClause(&mut self.watches, cr);
                            self.uncheckedEnqueue(learnt_clause[0], Some(cr));
                        }
                    }

                    self.heur.decayActivity();
                    self.db.decayActivity();

                    self.learntsize_adjust_cnt -= 1;
                    if self.learntsize_adjust_cnt == 0 {
                        self.learntsize_adjust_confl *= self.settings.learntsize_adjust_inc;
                        self.learntsize_adjust_cnt = self.learntsize_adjust_confl as i32;
                        self.max_learnts *= self.settings.learntsize_inc;

                        info!("| {:9} | {:7} {:8} {:8} | {:8} {:8} {:6.0} | {:6.3} % |",
                               self.stats.conflicts,
                               self.heur.dec_vars - self.trail.levelSize(0),
                               self.nClauses(),
                               self.db.clauses_literals,
                               self.max_learnts as u64,
                               self.db.num_learnts,
                               (self.db.learnts_literals as f64) / (self.db.num_learnts as f64),
                               progressEstimate(self.assigns.nVars(), &self.trail) * 100.0);
                    }
                }

                None        => {
                    if conflictC >= nof_conflicts || !self.budget.within(self.stats.conflicts, self.watches.propagations) {
                        // Reached bound on number of conflicts:
                        self.progress_estimate = progressEstimate(self.assigns.nVars(), &self.trail);
                        self.cancelUntil(0);
                        return LBool::Undef();
                    }

                    // Simplify the set of problem clauses:
                    if self.trail.isGroundLevel() && !self.simplify() {
                        return LBool::False();
                    }

                    if self.db.needReduce(self.trail.totalSize() + (self.max_learnts as usize)) {
                        // Reduce the set of learnt clauses:
                        self.db.reduce(&mut self.assigns, &mut self.watches);
                        if self.db.ca.checkGarbage(self.settings.garbage_frac) {
                            self.garbageCollect();
                        }
                    }

                    let mut next = None;
                    while self.trail.decisionLevel() < self.assumptions.len() {
                        // Perform user provided assumption:
                        let p = self.assumptions[self.trail.decisionLevel()];
                        match self.assigns.ofLit(p) {
                            v if v.isTrue()  => {
                                // Dummy decision level:
                                self.trail.newDecisionLevel();
                            }
                            v if v.isFalse() => {
                                self.conflict = self.analyze.analyzeFinal(&self.db, &self.assigns, &self.trail, !p);
                                return LBool::False();
                            }
                            _                => {
                                next = Some(p);
                                break;
                            }
                        }
                    }

                    match next {
                        Some(_) => {}
                        None    => {
                            // New variable decision:
                            self.stats.decisions += 1;
                            match self.heur.pickBranchLit(&self.assigns) {
                                Some(n) => { next = Some(n) }
                                None    => {
                                    // Model found:
                                    return LBool::True();
                                }
                            };
                        }
                    };

                    // Increase decision level and enqueue 'next'
                    self.trail.newDecisionLevel();
                    self.uncheckedEnqueue(next.unwrap(), None);
                }
            }
        }
    }

    fn propagate(&mut self) -> Option<ClauseRef> {
        let (confl, num_props) = self.watches.propagate(&mut self.trail, &mut self.assigns, &mut self.db.ca);
        self.simpDB_props -= num_props as i64;
        confl
    }

    fn uncheckedEnqueue(&mut self, p : Lit, from : Option<ClauseRef>) {
        self.assigns.assignLit(p, VarData { level : self.trail.decisionLevel(), reason : from });
        self.trail.push(p);
    }

    // NOTE: enqueue does not set the ok flag! (only public methods do)
    fn enqueue(&mut self, p : Lit, from : Option<ClauseRef>) -> bool {
        let val = self.assigns.ofLit(p);
        if val.isUndef() {
            self.uncheckedEnqueue(p, from);
            true
        } else {
            val.isTrue()
        }
    }

    fn garbageCollect(&mut self) {
        // Initialize the next region to a size corresponding to the estimated utilization degree. This
        // is not precise but should avoid some unnecessary reallocations for the new region:

        let to = ClauseAllocator::newForGC(&self.db.ca);
        self.relocAll(to);
    }

    fn relocAll(&mut self, mut to : ClauseAllocator) {

        // All watchers:
        self.watches.relocGC(&mut self.db.ca, &mut to);

        // All reasons:
        for l in self.trail.trail.iter() {
            let v = l.var();

            // Note: it is not safe to call 'locked()' on a relocated clause. This is why we keep
            // 'dangling' reasons here. It is safe and does not hurt.
            match self.assigns.vardata[&v].reason {
                Some(mut cr) if self.db.ca[cr].reloced() || isLocked(&self.db.ca, &self.assigns, cr) => {
                    assert!(!self.db.ca[cr].is_deleted());
                    cr = self.db.ca.relocTo(&mut to, cr);
                    self.assigns.vardata[&v].reason = Some(cr);
                }

                _ => {}
            }
        }

        self.db.relocGC(to);
    }
}


fn progressEstimate(vars : usize, trail : &PropagationTrail<Lit>) -> f64 {
    let F = 1.0 / (vars as f64);
    let mut progress = 0.0;
    for i in 0 .. trail.decisionLevel() + 1 {
        progress += F.powi(i as i32) * (trail.levelSize(i) as f64);
    }
    progress * F
}
