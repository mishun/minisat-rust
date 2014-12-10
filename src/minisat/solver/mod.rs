extern crate time;

use std::default::{Default};
use std::num::{Float, FloatMath};
use super::lbool::{LBool};
use super::literal::{Var, Lit};
use super::clause::{Clause, ClauseRef, ClauseAllocator};
use super::index_map::{IndexMap};
use super::random::{Random};
use super::watches::{Watches, Watcher};
use super::activity_queue::{ActivityQueue};
use super::assignment::{Assignment};
use super::propagation_trail::{PropagationTrail};

pub mod simp;


pub trait Solver {
    fn nVars(&self) -> uint;
    fn nClauses(&self) -> uint;
    fn newVar(&mut self, upol : LBool, dvar : bool) -> Var;
    fn addClause(&mut self, clause : &[Lit]) -> bool;
    fn simplify(&mut self) -> bool;
    fn solve(&mut self, assumps : &[Lit]) -> bool;
    fn solveLimited(&mut self, assumps : &[Lit]) -> LBool;
    fn getModel(&self) -> &Vec<LBool>;
    fn printStats(&self);
}


#[deriving(Default)]
struct Stats {
    solves : u64,
    starts : u64,
    decisions : u64,
    rnd_decisions : u64,
    propagations : u64,
    conflicts : u64,
    dec_vars : u64,
    num_clauses : u64,
    num_learnts : u64,
    clauses_literals : u64,
    learnts_literals : u64,
    max_literals : u64,
    tot_literals : u64,
    start_time : f64,
}

impl Stats {
    fn new() -> Stats {
        Stats { start_time : time::precise_time_s(), ..Default::default() }
    }

    pub fn print(&self) {
        let cpu_time = time::precise_time_s() - self.start_time;
        //double mem_used = memUsedPeak();
        println!("restarts              : {:12}", self.starts);
        println!("conflicts             : {:12}   ({:.0} / sec)", self.conflicts, self.conflicts as f64 / cpu_time);

        println!("decisions             : {:12}   ({:4.2} % random) ({:.0} / sec)",
            self.decisions,
            self.rnd_decisions as f64 * 100.0 / self.decisions as f64,
            self.decisions as f64 / cpu_time
        );

        println!("propagations          : {:12}   ({:.0} / sec)", self.propagations, self.propagations as f64 / cpu_time);

        println!("conflict literals     : {:12}   ({:4.2} % deleted)",
            self.tot_literals,
            (self.max_literals - self.tot_literals) as f64 * 100.0 / self.max_literals as f64
        );

        //if (mem_used != 0) printf("Memory used           : %.2f MB\n", mem_used);
        println!("CPU time              : {} s", cpu_time);
    }
}


struct CoreSettings {
    verbosity         : int,
    var_decay         : f64,
    clause_decay      : f64,
    random_var_freq   : f64,
    luby_restart      : bool,
    ccmin_mode        : int,    // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
    phase_saving      : int,    // Controls the level of phase saving (0=none, 1=limited, 2=full).
    rnd_pol           : bool,   // Use random polarities for branching heuristics.
    rnd_init_act      : bool,   // Initialize variable activities with a small random value.
    garbage_frac      : f64,    // The fraction of wasted memory allowed before a garbage collection is triggered.
    min_learnts_lim   : int,    // Minimum number to set the learnts limit to.
    restart_first     : int,    // The initial restart limit.                                                                (default 100)
    restart_inc       : f64,    // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
    learntsize_factor : f64,    // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
    learntsize_inc    : f64,    // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)
    remove_satisfied  : bool,   // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

    learntsize_adjust_start_confl : int,
    learntsize_adjust_inc : f64,
}

impl Default for CoreSettings {
    fn default() -> CoreSettings {
        CoreSettings {
            verbosity         : 0,
            var_decay         : 0.95,
            clause_decay      : 0.999,
            random_var_freq   : 0.0,
            luby_restart      : true,
            ccmin_mode        : 2,
            phase_saving      : 2,
            rnd_pol           : false,
            rnd_init_act      : false,
            garbage_frac      : 0.20,
            min_learnts_lim   : 0,
            restart_first     : 100,
            restart_inc       : 2.0,
            learntsize_factor : 1.0 / 3.0,
            learntsize_inc    : 1.1,
            remove_satisfied  : true,

            learntsize_adjust_start_confl : 100,
            learntsize_adjust_inc : 1.5,
        }
    }
}


struct VarData {
    reason : Option<ClauseRef>,
    level  : uint,
}


pub struct CoreSolver {
    set : CoreSettings,

    model : Vec<LBool>,             // If problem is satisfiable, this vector contains the model (if any).
    conflict : IndexMap<Lit, ()>,

    rand : Random,
    stats : Stats,   // Statistics: (read-only member variable)

    // Solver state:
    clauses : Vec<ClauseRef>,    // List of problem clauses.
    learnts : Vec<ClauseRef>,    // List of learnt clauses.
    trail   : PropagationTrail<Lit>,            // Assignment stack; stores all assigments made in the order they were made.
    assumptions : Vec<Lit>,      // Current set of assumptions provided to solve by the user.

    assigns  : Assignment,        // The current assignments.
    polarity : IndexMap<Var, bool>,         // The preferred polarity of each variable.
    user_pol : IndexMap<Var, LBool>,        // The users preferred polarity of each variable.
    decision : IndexMap<Var, bool>,         // Declares if a variable is eligible for selection in the decision heuristic.
    vardata  : IndexMap<Var, VarData>,      // Stores reason and level for each variable.
    watches  : Watches,                     // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    activity_queue : ActivityQueue<Var>,    // A priority queue of variables ordered with respect to the variable activity.

    ok : bool,               // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    cla_inc : f64,           // Amount to bump next clause with.
    var_inc : f64,           // Amount to bump next variable with.
    simpDB_assigns : int,    // Number of top-level assignments since last execution of 'simplify()'.
    simpDB_props : i64,      // Remaining number of propagations that must be made before next execution of 'simplify()'.
    progress_estimate : f64, // Set by 'search()'.
    ca : ClauseAllocator,

    released_vars : Vec<Var>,

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, exept 'seen' wich is used in several places.
    seen : IndexMap<Var, u8>,
    analyze_toclear : Vec<Lit>,

    max_learnts : f64,
    learntsize_adjust_confl : f64,
    learntsize_adjust_cnt : int,

    // Resource contraints:
    conflict_budget : i64,    // -1 means no budget.
    propagation_budget : i64, // -1 means no budget.
    asynch_interrupt : bool,
}

impl Solver for CoreSolver {
    fn nVars(&self) -> uint {
        self.assigns.nVars()
    }

    fn nClauses(&self) -> uint {
        self.stats.num_clauses as uint
    }

    fn newVar(&mut self, upol : LBool, dvar : bool) -> Var {
        let v = self.assigns.newVar();
        self.watches.initVar(v);
        self.vardata.insert(&v, VarData { reason : None, level : 0 });
        self.activity_queue.setActivity(&v, if self.set.rnd_init_act { self.rand.drand() * 0.00001 } else { 0.0 });
        self.seen.insert(&v, 0);
        self.polarity.insert(&v, true);
        self.user_pol.insert(&v, upol);
        self.decision.insert(&v, false);
        self.setDecisionVar(v, dvar);
        v
    }

    fn addClause(&mut self, clause : &[Lit]) -> bool {
        assert!(self.trail.isGroundLevel());
        if !self.ok { return false; }

        let mut ps = Vec::new();
        ps.push_all(clause);

        // Check if clause is satisfied and remove false/duplicate literals:
        ps.sort();
        ps.dedup();
        ps.retain(|lit| { !self.assigns.unsat(*lit) });
        {
            let mut prev = None;
            for lit in ps.iter() {
                 if self.assigns.sat(*lit) || prev == Some(!*lit) {
                     return true;
                 }
                 prev = Some(*lit);
            }
        }

        match ps.len() {
            0 => {
                self.ok = false;
                false
            }
            1 => {
                self.uncheckedEnqueue(ps[0], None);
                self.ok = self.propagate().is_none();
                self.ok
            }
            _ => {
                let cr = self.ca.alloc(&ps, false);
                self.attachClause(cr);
                self.clauses.push(cr);
                true
            }
        }
    }

    //_________________________________________________________________________________________________
    //
    // simplify : [void]  ->  [bool]
    //
    // Description:
    //   Simplify the clause database according to the current top-level assigment. Currently, the only
    //   thing done here is the removal of satisfied clauses, but more things can be put here.
    //_______________________________________________________________________________________________@
    fn simplify(&mut self) -> bool {
        assert!(self.trail.isGroundLevel());
        if !self.ok { return false; }

        if self.propagate().is_some() {
            self.ok = false;
            return false;
        }

        if self.nAssigns() as int == self.simpDB_assigns || self.simpDB_props > 0 {
            return true;
        }

        // Remove satisfied clauses:
        removeSatisfied(&mut self.ca, &mut self.watches, &mut self.stats, &mut self.vardata, &self.assigns, &mut self.learnts);

        // TODO: what todo in if 'remove_satisfied' is false?
        if self.set.remove_satisfied {       // Can be turned off.
            removeSatisfied(&mut self.ca, &mut self.watches, &mut self.stats, &mut self.vardata, &self.assigns, &mut self.clauses);

            // Remove all released variables from the trail:
            for v in self.released_vars.iter() {
                assert!(self.seen[*v] == 0);
                self.seen[*v] = 1;
            }

            {
                let seen = &self.seen;
                self.trail.retain(|l| { seen[l.var()] == 0 });
            }

            for v in self.released_vars.iter() {
                self.seen[*v] = 0;
            }

            // Released variables are now ready to be reused:
            for v in self.released_vars.iter() { self.assigns.freeVar(v); }
            self.released_vars.clear();
        }

        self.checkGarbageDef();
        self.rebuildOrderHeap();

        self.simpDB_assigns = self.nAssigns() as int;
        self.simpDB_props   = (self.stats.clauses_literals + self.stats.learnts_literals) as i64;   // (shouldn't depend on stats really, but it will do for now)

        true
    }

    fn solve(&mut self, assumps : &[Lit]) -> bool {
        self.budgetOff();
        self.solveLimited(assumps).isTrue()
    }

    fn solveLimited(&mut self, assumps : &[Lit]) -> LBool {
        self.assumptions.clear();
        self.assumptions.push_all(assumps);
        self.solve_()
    }

    fn getModel(&self) -> &Vec<LBool> {
        &self.model
    }

    fn printStats(&self) {
        if self.set.verbosity > 0 {
            self.stats.print();
            println!("");
        }
    }
}

impl CoreSolver {
    pub fn new(verbosity : int) -> CoreSolver {
        CoreSolver {
            set : CoreSettings { verbosity : verbosity, ..Default::default() },

            model : Vec::new(),
            conflict : IndexMap::new(),

            rand : Random::new(91648253.0),

            stats : Stats::new(),

            clauses : Vec::new(),
            learnts : Vec::new(),
            trail : PropagationTrail::new(),
            assumptions : Vec::new(),

            assigns : Assignment::new(),
            polarity : IndexMap::new(),
            user_pol : IndexMap::new(),
            decision : IndexMap::new(),
            vardata : IndexMap::new(),
            watches : Watches::new(),
            activity_queue : ActivityQueue::new(),

            ok : true,
            cla_inc : 1.0,
            var_inc : 1.0,
            simpDB_assigns : -1,
            simpDB_props : 0,
            progress_estimate : 0.0,
            ca : ClauseAllocator::new(),

            released_vars : Vec::new(),

            seen : IndexMap::new(),
            analyze_toclear : Vec::new(),

            max_learnts : 0.0,
            learntsize_adjust_confl : 0.0,
            learntsize_adjust_cnt : 0,

            conflict_budget : -1,
            propagation_budget : -1,
            asynch_interrupt : false,
        }
    }

    pub fn nLearnts(&self) -> uint {
        self.stats.num_learnts as uint
    }

    pub fn nAssigns(&self) -> uint {
        self.trail.totalSize()
    }

    // Revert to the state at given level (keeping all assignment at 'level' but not beyond).
    fn cancelUntil(&mut self, level : uint) {
        if self.trail.decisionLevel() > level {
            let level_lim = self.trail.lim[level];
            for c in range(level_lim, self.trail.totalSize()).rev() {
                let lit = self.trail[c];
                let x = lit.var();
                self.assigns.cancel(x);
                if self.set.phase_saving > 1 || (self.set.phase_saving == 1 && c > *self.trail.lim.last().unwrap()) {
                    self.polarity[x] = lit.sign();
                }
                self.insertVarOrder(x);
            }

            self.trail.qhead = level_lim;
            self.trail.trail.truncate(level_lim);
            self.trail.lim.truncate(level);
        }
    }

    fn setDecisionVar(&mut self, v : Var, b : bool) {
        if b && !self.decision[v] {
            self.stats.dec_vars += 1;
        } else if !b && self.decision[v] {
            self.stats.dec_vars -= 1;
        }

        self.decision[v] = b;
        self.insertVarOrder(v);
    }

    fn solve_(&mut self) -> LBool {
        self.model.clear();
        self.conflict.clear();
        if !self.ok { return LBool::False() }
        self.stats.solves += 1;

        self.max_learnts = (self.nClauses() as f64 * self.set.learntsize_factor).max(self.set.min_learnts_lim as f64);
        self.learntsize_adjust_confl = self.set.learntsize_adjust_start_confl as f64;
        self.learntsize_adjust_cnt   = self.set.learntsize_adjust_start_confl;
        let mut status = LBool::Undef();

        if self.set.verbosity >= 1 {
            println!("============================[ Search Statistics ]==============================");
            println!("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |");
            println!("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |");
            println!("===============================================================================");
        }

        // Search:
        {
            let mut curr_restarts = 0;
            while status.isUndef() {
                let rest_base =
                    match self.set.luby_restart {
                        true  => { luby(self.set.restart_inc, curr_restarts) }
                        false => { self.set.restart_inc.powi(curr_restarts as i32) }
                    };
                let conflicts_to_go = rest_base * self.set.restart_first as f64;
                status = self.search(conflicts_to_go as uint);
                if !self.withinBudget() { break; }
                curr_restarts += 1;
            }
        }

        if self.set.verbosity >= 1 {
            println!("===============================================================================");
        }

        if status.isTrue() {
            let vars = self.nVars();
            self.model.grow(vars, LBool::Undef());
            for i in range(0, vars) {
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
    fn search(&mut self, nof_conflicts : uint) -> LBool {
        assert!(self.ok);
        self.stats.starts += 1;

        let mut conflictC = 0u;
        loop {
            match self.propagate() {
                Some(confl) => {
                    self.stats.conflicts += 1;
                    conflictC += 1;
                    if self.trail.isGroundLevel() { return LBool::False() }

                    let (backtrack_level, learnt_clause) = self.analyze(confl);
                    self.cancelUntil(backtrack_level);
                    match learnt_clause.len() {
                        1 => { self.uncheckedEnqueue(learnt_clause[0], None) }
                        _ => {
                            let cr = self.ca.alloc(&learnt_clause, true);
                            self.learnts.push(cr);
                            self.attachClause(cr);
                            claBumpActivity(&mut self.ca, &mut self.learnts, &mut self.cla_inc, cr);
                            self.uncheckedEnqueue(learnt_clause[0], Some(cr));
                        }
                    }

                    self.varDecayActivity();
                    self.claDecayActivity();

                    self.learntsize_adjust_cnt -= 1;
                    if self.learntsize_adjust_cnt == 0 {
                        self.learntsize_adjust_confl *= self.set.learntsize_adjust_inc;
                        self.learntsize_adjust_cnt = self.learntsize_adjust_confl as int;
                        self.max_learnts *= self.set.learntsize_inc;

                        if self.set.verbosity >= 1 {
                            println!("| {:9} | {:7} {:8} {:8} | {:8} {:8} {:6.0} | {:6.3} % |",
                                   self.stats.conflicts,
                                   self.stats.dec_vars as uint - self.trail.levelSize(0),
                                   self.nClauses(),
                                   self.stats.clauses_literals,
                                   self.max_learnts as u64,
                                   self.nLearnts(),
                                   self.stats.learnts_literals as f64 / self.nLearnts() as f64,
                                   self.progressEstimate() * 100.0);
                        }
                    }
                }

                None        => {
                    if conflictC >= nof_conflicts || !self.withinBudget() {
                        // Reached bound on number of conflicts:
                        self.progress_estimate = self.progressEstimate();
                        self.cancelUntil(0);
                        return LBool::Undef();
                    }

                    // Simplify the set of problem clauses:
                    if self.trail.isGroundLevel() && !self.simplify() {
                        return LBool::False();
                    }

                    if self.learnts.len() >= self.max_learnts as uint + self.nAssigns() {
                        // Reduce the set of learnt clauses:
                        self.reduceDB();
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
                                self.conflict = self.analyzeFinal(!p);
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
                            match self.pickBranchLit() {
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


    //_________________________________________________________________________________________________
    //
    // propagate : [void]  ->  [Clause*]
    //
    // Description:
    //   Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
    //   otherwise CRef_Undef.
    // 
    //   Post-conditions:
    //     * the propagation queue is empty, even if there was a conflict.
    //_______________________________________________________________________________________________@
    fn propagate(&mut self) -> Option<ClauseRef> {
        let mut confl = None;
        let mut num_props = 0;

        loop {
            let p = match self.trail.dequeue() { Some(p) => p, None => break }; // 'p' is enqueued fact to propagate.
            self.watches.lookup(&self.ca, p);
            num_props += 1;

            let mut i = 0;
            let mut j = 0;
            while i < self.watches[p].len() {
                let blocker = self.watches[p][i].blocker;
                if self.assigns.sat(blocker) {
                    self.watches[p][j] = self.watches[p][i].clone();
                    i += 1;
                    j += 1;
                    continue;
                }

                let false_lit = !p;
                let cr = self.watches[p][i].cref;
                let (new_watch, first) = {
                    let c = &mut self.ca[cr];
                    if c[0] == false_lit {
                        c[0] = c[1];
                        c[1] = false_lit;
                    }
                    assert!(c[1] == false_lit);
                    i += 1;

                    // If 0th watch is true, then clause is already satisfied.
                    let first = c[0];
                    if first != blocker && self.assigns.sat(first) {
                        self.watches[p][j] = Watcher { cref : cr, blocker : first };
                        j += 1;
                        continue;
                    }

                    // Look for new watch:
                    let mut new_watch = None;
                    for k in range(2, c.len()) {
                        if !self.assigns.unsat(c[k]) {
                            new_watch = Some(k);
                            break;
                        }
                    }
                    (new_watch, first)
                };

                match new_watch {
                    Some(k) => {
                        let c = &mut self.ca[cr];
                        c[1] = c[k];
                        c[k] = false_lit;
                        self.watches[!c[1]].push(Watcher { cref : cr, blocker : first });
                    }

                    // Did not find watch -- clause is unit under assignment:
                    None => {
                        self.watches[p][j] = Watcher { cref : cr, blocker : first };
                        j += 1;
                        if self.assigns.unsat(first) {
                            confl = Some(cr);
                            self.trail.dequeueAll();

                            // Copy the remaining watches:
                            while i < self.watches[p].len() {
                                self.watches[p][j] = self.watches[p][i].clone();
                                j += 1;
                                i += 1;
                            }
                        } else {
                            self.uncheckedEnqueue(first, Some(cr));
                        }
                    }
                }
            }
            self.watches[p].truncate(j);
        }

        self.stats.propagations += num_props;
        self.simpDB_props -= num_props as i64;
        confl
    }

    //_________________________________________________________________________________________________
    //
    // reduceDB : ()  ->  [void]
    //
    // Description:
    //   Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
    //   clauses are clauses that are reason to some assignment. Binary clauses are never removed.
    //_______________________________________________________________________________________________@
    fn reduceDB(&mut self) {
        {
            let ca = &self.ca;
            self.learnts.sort_by(|rx, ry| {
                let ref x = ca[*rx];
                let ref y = ca[*ry];
                if x.len() > 2 && (y.len() == 2 || x.activity() < y.activity()) {
                    Less
                } else {
                    Greater
                }
            });
        }

        // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
        // and clauses with activity smaller than 'extra_lim':
        let extra_lim = self.cla_inc / self.learnts.len() as f64; // Remove any clause below this activity
        {
            let mut j = 0;
            for i in range(0, self.learnts.len()) {
                let cr = self.learnts[i];
                let remove = {
                    let c = &self.ca[cr];
                    c.len() > 2 && !isLocked(&self.ca, &self.assigns, &self.vardata, cr)
                                && (i < self.learnts.len() / 2 || c.activity() < extra_lim)
                };
                if remove {
                    removeClause(&mut self.ca, &mut self.watches, &mut self.stats, &mut self.vardata, &self.assigns, cr);
                } else {
                    self.learnts[j] = cr;
                    j += 1;
                }
            }
            self.learnts.truncate(j);
        }

        self.checkGarbageDef();
    }

    fn rebuildOrderHeap(&mut self) {
        let mut tmp = Vec::new();
        for vi in range(0, self.nVars()) {
            let v = Var::new(vi);
            if self.decision[v] && self.assigns.undef(v) {
                tmp.push(v);
            }
        }
        self.activity_queue.heapifyFrom(tmp);
    }


    fn pickBranchLit(&mut self) -> Option<Lit> {
        let mut next : Option<Var> = None;

        // Random decision:
        if self.rand.chance(self.set.random_var_freq) && !self.activity_queue.is_empty() {
            let v = self.activity_queue[self.rand.irand(self.activity_queue.len())];
            if self.assigns.undef(v) && self.decision[v] {
                self.stats.rnd_decisions += 1;
            }
            next = Some(v);
        }

        // Activity based decision:
        while next.is_none() || !self.assigns.undef(next.unwrap()) || !self.decision[next.unwrap()] {
            next = self.activity_queue.pop();
            if next.is_none() { break; }
        }

        // Choose polarity based on different polarity modes (global or per-variable):
        next.map(|v| {
            if !self.user_pol[v].isUndef() {
                Lit::new(v, self.user_pol[v].isTrue())
            } else if self.set.rnd_pol {
                Lit::new(v, self.rand.chance(0.5))
            } else {
                Lit::new(v, self.polarity[v])
            }
        })
    }

    //_________________________________________________________________________________________________
    //
    // analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
    //
    // Description:
    //   Analyze conflict and produce a reason clause.
    //
    //   Pre-conditions:
    //     * 'out_learnt' is assumed to be cleared.
    //     * Current decision level must be greater than root level.
    //
    //   Post-conditions:
    //     * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
    //     * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
    //       rest of literals. There may be others from the same level though.
    //
    //_______________________________________________________________________________________________@
    fn analyze(&mut self, confl_param : ClauseRef) -> (uint, Vec<Lit>) {
        // Generate conflict clause:
        let mut out_learnt = Vec::new();

        let mut pathC = 0i;
        let mut p = None;
        let mut index = self.trail.totalSize() - 1;
        let mut confl = Some(confl_param);

        loop {
            assert!(confl.is_some()); // (otherwise should be UIP)
            claBumpActivity(&mut self.ca, &mut self.learnts, &mut self.cla_inc, confl.unwrap());

            let c = &self.ca[confl.unwrap()];

            for j in range(match p { None => 0, Some(_) => 1 }, c.len()) {
                let q = c[j];
                let v = q.var();

                if self.seen[v] == 0 && self.vardata[v].level > 0 {
                    varBumpActivity(&mut self.activity_queue, &mut self.var_inc, v);

                    self.seen[v] = 1;
                    if self.vardata[v].level >= self.trail.decisionLevel() {
                        pathC += 1;
                    } else {
                        out_learnt.push(q);
                    }
                }
            }

            // Select next clause to look at:
            loop {
                let s = self.seen[self.trail[index].var()];
                index -= 1;
                if s != 0 { break; }
            }
            let pl = self.trail[index + 1];
            confl = self.vardata[pl.var()].reason;
            self.seen[pl.var()] = 0;
            p = Some(pl);

            pathC -= 1;
            if pathC <= 0 { break; }
        };

        out_learnt.insert(0, !p.unwrap());


        // Simplify conflict clause:
        self.analyze_toclear = out_learnt.clone();
        {
            let mut j;
            match self.set.ccmin_mode {
                2 => {
                    j = 1;
                    for i in range(1, out_learnt.len()) {
                        let l = out_learnt[i];
                        if self.vardata[l.var()].reason.is_none() || !self.litRedundant(l) {
                            out_learnt[j] = out_learnt[i];
                            j += 1;
                        }
                    }
                }

                1 => {
                    j = 1;
                    for i in range(1, out_learnt.len()) {
                        let x = out_learnt[i].var();
                        match self.vardata[x].reason {
                            None     => { out_learnt[j] = out_learnt[i]; j += 1; }
                            Some(cr) => {
                                let c = &self.ca[cr];
                                for k in range(1, c.len()) {
                                    let y = c[k].var();
                                    if self.seen[y] == 0 && self.vardata[y].level > 0 {
                                        out_learnt[j] = out_learnt[i];
                                        j += 1;
                                        break;
                                    }
                                }
                            }
                        }
                    }
                }

                _ => { j = out_learnt.len(); }
            }

            self.stats.max_literals += out_learnt.len() as u64;
            out_learnt.truncate(j);
            self.stats.tot_literals += out_learnt.len() as u64;
        }

        // Find correct backtrack level:
        let out_btlevel =
            if out_learnt.len() == 1 {
                0
            } else {
                // Find the first literal assigned at the next-highest level:
                let mut max_i = 1;
                for i in range(2, out_learnt.len()) {
                    if self.vardata[out_learnt[i].var()].level > self.vardata[out_learnt[max_i].var()].level {
                        max_i = i;
                    }
                }

                // Swap-in this literal at index 1:
                let p             = out_learnt[max_i];
                out_learnt[max_i] = out_learnt[1];
                out_learnt[1]     = p;
                self.vardata[p.var()].level
            };

        for l in self.analyze_toclear.iter() {
            self.seen[l.var()] = 0;    // ('seen[]' is now cleared)
        }

        (out_btlevel, out_learnt)
    }

    // Check if 'p' can be removed from a conflict clause.
    fn litRedundant(&mut self, mut p : Lit) -> bool {
        let seen_undef = 0;
        let seen_source = 1;
        let seen_removable = 2;
        let seen_failed = 3;

        assert!(self.seen[p.var()] == seen_undef || self.seen[p.var()] == seen_source);

        let mut stack = Vec::new();
        let mut i = 0;
        loop {
            i += 1;

            assert!(self.vardata[p.var()].reason.is_some());
            let c = &self.ca[self.vardata[p.var()].reason.unwrap()];

            if i < c.len() {
                // Checking 'p'-parents 'l':
                let l = c[i];

                // Variable at level 0 or previously removable:
                if self.vardata[l.var()].level == 0 || self.seen[l.var()] == seen_source || self.seen[l.var()] == seen_removable {
                    continue;
                }

                // Check variable can not be removed for some local reason:
                if self.vardata[l.var()].reason.is_none() || self.seen[l.var()] == seen_failed {
                    stack.push((0, p));
                    for &(_, l) in stack.iter() {
                        if self.seen[l.var()] == seen_undef {
                            self.seen[l.var()] = seen_failed;
                            self.analyze_toclear.push(l);
                        }
                    }
                    return false;
                }

                // Recursively check 'l':
                stack.push((i, p));
                i  = 0;
                p  = l;
            } else {
                // Finished with current element 'p' and reason 'c':
                if self.seen[p.var()] == seen_undef {
                    self.seen[p.var()] = seen_removable;
                    self.analyze_toclear.push(p);
                }

                match stack.pop() {
                    None           => { break; } // Terminate with success if stack is empty:
                    Some((ni, nl)) => {
                        // Continue with top element on stack:
                        i = ni;
                        p = nl;
                    }
                }
            }
        }

        true
    }


    //_________________________________________________________________________________________________
    //
    // analyzeFinal : (p : Lit)  ->  [void]
    //
    // Description:
    //   Specialized analysis procedure to express the final conflict in terms of assumptions.
    //   Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
    //   stores the result in 'out_conflict'.
    //_______________________________________________________________________________________________@
    fn analyzeFinal(&mut self, p : Lit) -> IndexMap<Lit, ()> {
        let mut out_conflict = IndexMap::new();
        out_conflict.insert(&p, ());

        if !self.trail.isGroundLevel() {
            self.seen[p.var()] = 1;
            for i in range(self.trail.lim[0], self.trail.totalSize()).rev() {
                let x = self.trail[i].var();
                if self.seen[x] != 0 {
                    match self.vardata[x].reason {
                        None     => {
                            assert!(self.vardata[x].level > 0);
                            out_conflict.insert(&!self.trail[i], ());
                        }

                        Some(cr) => {
                            let c = &self.ca[cr];
                            for j in range(1, c.len()) {
                                let v = c[j].var();
                                if self.vardata[v].level > 0 {
                                    self.seen[v] = 1;
                                }
                            }
                        }
                    }
                }
            }
            self.seen[p.var()] = 0;
        }

        out_conflict
    }


    pub fn implies(&mut self, assumps : &Vec<Lit>, out : &mut Vec<Lit>) -> bool {
        self.trail.newDecisionLevel();

        for a in assumps.iter() {
            let val = self.assigns.ofLit(*a);
            if val.isFalse() {
                self.cancelUntil(0);
                return false;
            } else if val.isUndef() {
                self.uncheckedEnqueue(*a, None);
            }
        }

        let trail_before = self.trail.totalSize();
        let ret = match self.propagate() {
            Some(_) => { false }
            None    => {
                out.clear();
                for j in range(trail_before, self.trail.totalSize()) {
                    out.push(self.trail[j]);
                }
                true
            }
        };

        self.cancelUntil(0);
        ret
    }


    fn budgetOff(&mut self) {
        self.conflict_budget = -1;
        self.propagation_budget = -1;
    }

    fn withinBudget(&self) -> bool {
        !self.asynch_interrupt &&
            (self.conflict_budget    < 0 || self.stats.conflicts < self.conflict_budget as u64) &&
            (self.propagation_budget < 0 || self.stats.propagations < self.propagation_budget as u64)
    }

    fn varDecayActivity(&mut self) {
        self.var_inc *= 1.0 / self.set.var_decay
    }

    fn claDecayActivity(&mut self) {
        self.cla_inc *= 1.0 / self.set.clause_decay
    }

    // Insert a variable in the decision order priority queue.
    fn insertVarOrder(&mut self, x : Var) {
        if self.decision[x] {
            self.activity_queue.insert(x);
        }
    }

    fn uncheckedEnqueue(&mut self, p : Lit, from : Option<ClauseRef>) {
        self.assigns.assignLit(p);
        self.vardata[p.var()] = VarData { level : self.trail.decisionLevel(), reason : from };
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

    fn progressEstimate(&self) -> f64 {
        let F = 1.0 / self.nVars() as f64;
        let mut progress = 0.0;
        for i in range(0, self.trail.decisionLevel() + 1) {
            progress += F.powi(i as i32) * self.trail.levelSize(i) as f64;
        }
        progress * F
    }


    fn checkGarbageDef(&mut self) {
        let gf = self.set.garbage_frac;
        self.checkGarbage(gf);
    }

    fn checkGarbage(&mut self, gf : f64) {
        if self.ca.wasted() as f64 > self.ca.size() as f64 * gf {
            self.garbageCollect();
        }
    }

    fn garbageCollect(&mut self) {
        // Initialize the next region to a size corresponding to the estimated utilization degree. This
        // is not precise but should avoid some unnecessary reallocations for the new region:

        let mut to = ClauseAllocator::new(); //self.ca.size() - self.ca.wasted());
        self.relocAll(&mut to);
        if self.set.verbosity >= 2 {
            println!("|  Garbage collection:   {:12} bytes ({:5} clauses) => {:12} bytes  ({:5} clauses)            |",
                self.ca.size(), self.ca.numberOfClauses(), to.size(), to.numberOfClauses());
        }
        self.ca = to;
    }

    fn relocAll(&mut self, to : &mut ClauseAllocator) {

        // All watchers:
        self.watches.cleanAll(&self.ca);
        for vi in range(0, self.nVars()) {
            for s in [false, true].iter() {
                let p = Lit::new(Var::new(vi), *s);
                let ws = &mut self.watches[p];
                for w in ws.iter_mut() {
                    self.ca.reloc(to, &mut w.cref);
                }
            }
        }

        // All reasons:
        for l in self.trail.trail.iter() {
            let v = l.var();

            // Note: it is not safe to call 'locked()' on a relocated clause. This is why we keep
            // 'dangling' reasons here. It is safe and does not hurt.
            match self.vardata[v].reason {
                Some(mut cr) if self.ca[cr].reloced() || isLocked(&self.ca, &self.assigns, &self.vardata, cr) => {
                    assert!(self.ca[cr].mark() != 1);
                    self.ca.reloc(to, &mut cr);
                    self.vardata[v].reason = Some(cr);
                }

                _ => {}
            }
        }

        // All learnt:
        {
            let mut j = 0;
            for i in range(0, self.learnts.len()) {
                if self.ca[self.learnts[i]].mark() != 1 {
                    self.ca.reloc(to, &mut self.learnts[i]);
                    self.learnts[j] = self.learnts[i];
                    j += 1;
                }
            }
            self.learnts.truncate(j);
        }

        // All original:
        {
            let mut j = 0;
            for i in range(0, self.clauses.len()) {
                if self.ca[self.clauses[i]].mark() != 1 {
                    self.ca.reloc(to, &mut self.clauses[i]);
                    self.clauses[j] = self.clauses[i];
                    j += 1;
                }
            }
            self.clauses.truncate(j);
        }
    }


    fn attachClause(&mut self, cr : ClauseRef) {
        let ref c = self.ca[cr];
        assert!(c.len() > 1);

        self.watches[!c[0]].push(Watcher { cref : cr, blocker : c[1] });
        self.watches[!c[1]].push(Watcher { cref : cr, blocker : c[0] });

        if c.learnt() {
            self.stats.num_learnts += 1;
            self.stats.learnts_literals += c.len() as u64;
        }
        else {
            self.stats.num_clauses += 1;
            self.stats.clauses_literals += c.len() as u64;
        }
    }
}


pub fn luby(y : f64, mut x : uint) -> f64 {
    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    let mut size = 1;
    let mut seq = 0;

    while size < x + 1 {
        seq += 1;
        size = 2 * size + 1;
    }

    while size - 1 != x {
        size = (size - 1) >> 1;
        seq -= 1;
        x = x % size;
    }

    y.powi(seq)
}


fn isLocked(ca : &ClauseAllocator, assigns : &Assignment, vardata : &IndexMap<Var, VarData>, cr : ClauseRef) -> bool {
    let lit = ca[cr][0];
    if !assigns.sat(lit) { return false; }
    match vardata[lit.var()].reason {
        Some(r) if cr == r => { true }
        _                  => { false }
    }
}


// Returns TRUE if a clause is satisfied in the current state.
fn satisfiedWith(c : &Clause, s : &Assignment) -> bool {
    for i in range(0, c.len()) {
        if s.sat(c[i]) {
            return true;
        }
    }
    false
}

fn removeSatisfied(ca : &mut ClauseAllocator, watches : &mut Watches, stats : &mut Stats, vardata : &mut IndexMap<Var, VarData>, assigns : &Assignment, cs : &mut Vec<ClauseRef>) {
    let mut j = 0;
    for i in range(0, cs.len()) {
        let cr = cs[i];
        if satisfiedWith(&ca[cr], assigns) {
            removeClause(ca, watches, stats, vardata, assigns, cr);
        } else {
            // Trim clause:
            let c = &mut ca[cr];
            assert!(assigns.undef(c[0].var()) && assigns.undef(c[1].var()));

            c.retainSuffix(2, |lit| !assigns.unsat(*lit));

            cs[j] = cr;
            j += 1;
        }
    }
    cs.truncate(j);
}


fn removeClause(ca : &mut ClauseAllocator, watches : &mut Watches, stats : &mut Stats, vardata : &mut IndexMap<Var, VarData>, assigns : &Assignment, cr : ClauseRef) {
    detachClause(ca, stats, watches, cr, false);
    {
        // Don't leave pointers to free'd memory!
        if isLocked(ca, assigns, vardata, cr) {
            vardata[ca[cr][0].var()].reason = None;
        }

        ca[cr].setMark(1);
    }
    ca.free(cr);
}

fn detachClause(ca : &ClauseAllocator, stats : &mut Stats, watches : &mut Watches, cr : ClauseRef, strict : bool) {
    let ref c = ca[cr];
    assert!(c.len() > 1);
    
    // Strict or lazy detaching:
    if strict {
        watches[!c[0]].retain(|w| w.cref != cr);
        watches[!c[1]].retain(|w| w.cref != cr);
    } else {
        watches.smudge(!c[0]);
        watches.smudge(!c[1]);
    }

    if c.learnt() {
        stats.num_learnts -= 1;
        stats.learnts_literals -= c.len() as u64;
    } else {
        stats.num_clauses -= 1;
        stats.clauses_literals -= c.len() as u64;
    }
}

fn varBumpActivity(q : &mut ActivityQueue<Var>, var_inc : &mut f64, v : Var) {
    let new = q.getActivity(&v) + *var_inc;
    if new > 1e100 {
        *var_inc *= 1e-100;
        q.scaleActivity(1e-100);
        q.setActivity(&v, new * 1e-100);
    } else {
        q.setActivity(&v, new);
    }
}

fn claBumpActivity(ca : &mut ClauseAllocator, learnts : &mut Vec<ClauseRef>, cla_inc : &mut f64, cr : ClauseRef) {
    let new = {
            let c = &mut ca[cr];
            if !c.learnt() { return; }

            let new = c.activity() + *cla_inc;
            c.setActivity(new);
            new
        };

    if new > 1e20 {
        *cla_inc *= 1e-20;
        for cri in learnts.iter() {
            let c = &mut ca[*cri];
            let scaled = c.activity() * 1e-10;
            c.setActivity(scaled);
        }
    }
}
