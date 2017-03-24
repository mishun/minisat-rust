use sat::formula::{Var, Lit, VarMap};
use sat::formula::assignment::*;
use sat::formula::clause::*;
use sat::formula::util::*;
use super::{Searcher, SearchSettings, SearchRes};
use super::super::budget::Budget;
use self::subsumption_queue::*;

pub mod elim_clauses;
mod elim_queue;
mod subsumption_queue;


pub struct SimplificatorSettings {
    pub grow              : usize, // Allow a variable elimination step to grow by a number of clauses (default to zero).
    pub clause_lim        : i32,   // Variables are not eliminated if it produces a resolvent with a length above this limit. -1 means no limit.
    pub subsumption_lim   : i32,   // Do not check if subsumption against a clause larger than this. -1 means no limit.
    pub simp_garbage_frac : f64,   // A different limit for when to issue a GC during simplification (Also see 'garbage_frac').
    pub use_asymm         : bool,  // Shrink clauses by asymmetric branching.
    pub use_elim          : bool   // Perform variable elimination.
}

impl Default for SimplificatorSettings {
    fn default() -> Self {
        SimplificatorSettings { grow              : 0
                              , clause_lim        : 20
                              , subsumption_lim   : 1000
                              , simp_garbage_frac : 0.5
                              , use_asymm         : false
                              , use_elim          : true
                              }
    }
}


#[derive(Default)]
struct Stats {
    merges            : u64,
    asymm_lits        : u64,
    eliminated_vars   : u64,
}


pub struct Simplificator {
    settings          : SimplificatorSettings,
    stats             : Stats,
    var_status        : VarMap<elim_queue::VarStatus>,
    occurs            : elim_queue::OccLists,
    elim              : elim_queue::ElimQueue,
    touched           : VarMap<i8>,
    n_touched         : usize,
    subsumption_queue : SubsumptionQueue
}

impl Simplificator {
    pub fn new(settings : SimplificatorSettings) -> Self {
        Simplificator { settings           : settings
                      , stats              : Stats::default()
                      , var_status         : VarMap::new()
                      , occurs             : elim_queue::OccLists::new()
                      , elim               : elim_queue::ElimQueue::new()
                      , touched            : VarMap::new()
                      , n_touched          : 0
                      , subsumption_queue  : SubsumptionQueue::new()
                      }
    }

    pub fn initVar(&mut self, v : Var) {
        self.var_status.insert(&v, elim_queue::VarStatus { frozen : 0, eliminated : 0 });
        self.occurs.initVar(&v);
        self.touched.insert(&v, 0);
        self.elim.initVar(v);
    }

    pub fn addClause(&mut self, search : &mut Searcher, ps : &[Lit]) -> bool {
        //#ifndef NDEBUG
        for l in ps.iter() {
            assert!(self.var_status[&l.var()].eliminated == 0);
        }
        //#endif

        match search.addClause(ps) {
            super::AddClauseRes::UnSAT        => { false }
            super::AddClauseRes::Consumed     => { true }
            super::AddClauseRes::Added(c, cr) => {
                // NOTE: the clause is added to the queue immediately and then
                // again during 'gatherTouchedClauses()'. If nothing happens
                // in between, it will only be checked once. Otherwise, it may
                // be checked twice unnecessarily. This is an unfortunate
                // consequence of how backward subsumption is used to mimic
                // forward subsumption.
                self.subsumption_queue.push(cr);

                for &lit in c.lits() {
                    self.occurs.pushOcc(&lit.var(), cr);
                    self.touched[&lit.var()] = 1;
                    self.n_touched += 1;
                    self.elim.bumpLitOcc(&lit, 1);
                }

                true
            }
        }
    }

    pub fn solveLimited(&mut self, mut search : Searcher, ss : &SearchSettings, budget : &Budget, elimclauses : &mut elim_clauses::ElimClauses, assumptions : &[Lit]) -> SearchRes {
        let mut extra_frozen : Vec<Var> = Vec::new();

        // Assumptions must be temporarily frozen to run variable elimination:
        for lit in assumptions.iter() {
            let ref mut st = self.var_status[&lit.var()];

            // If an assumption has been eliminated, remember it.
            assert!(st.eliminated == 0);
            if st.frozen == 0 {
                // Freeze and store.
                st.frozen = 1;
                extra_frozen.push(lit.var());
            }
        }

        if search.preprocess() && self.eliminate(&mut search, budget, elimclauses) {
            match search.search(ss, budget, assumptions) {
                SearchRes::Interrupted(prog, ns) => {

                    // Unfreeze the assumptions that were frozen:
                    for &v in extra_frozen.iter() {
                        self.var_status[&v].frozen = 0;
                        self.elim.updateElimHeap(v, &self.var_status, &ns.assigns);
                    }

                    SearchRes::Interrupted(prog, ns)
                }

                other => { other }
            }
        } else {
            SearchRes::UnSAT(search.stats())
        }
    }

    pub fn eliminate(&mut self, search : &mut Searcher, budget : &Budget, elimclauses : &mut elim_clauses::ElimClauses) -> bool {
        // Main simplification loop:
        while self.n_touched > 0 || self.subsumption_queue.assignsLeft(&search.assigns) > 0 || self.elim.len() > 0 {
            self.gatherTouchedClauses(&mut search.ca);

            if !self.backwardSubsumptionCheck(search, budget, true) {
                return false;
            }

            // Empty elim_heap and return immediately on user-interrupt:
            if budget.interrupted() {
                assert!(self.subsumption_queue.assignsLeft(&search.assigns) == 0);
                assert!(self.subsumption_queue.is_empty());
                assert!(self.n_touched == 0);
                self.elim.clear();
                return true;
            }

            trace!("ELIM: vars = {}", self.elim.len());
            let mut cnt = 0;
            while let Some(var) = self.elim.pop() {
                if budget.interrupted() { break; }
                if self.var_status[&var].eliminated == 0 && search.assigns.isUndef(var) {
                    if cnt % 100 == 0 {
                        trace!("elimination left: {:10}", self.elim.len());
                    }

                    if self.settings.use_asymm {
                        // Temporarily freeze variable. Otherwise, it would immediately end up on the queue again:
                        let was_frozen = self.var_status[&var].frozen;
                        self.var_status[&var].frozen = 1;
                        if !self.asymmVar(search, budget, var) {
                            return false;
                        }
                        self.var_status[&var].frozen = was_frozen;
                    }

                    // At this point, the variable may have been set by asymmetric branching, so check it
                    // again. Also, don't eliminate frozen variables:
                    if self.settings.use_elim
                        && search.assigns.isUndef(var)
                        && self.var_status[&var].frozen == 0
                        && !self.eliminateVar(search, budget, elimclauses, var) {
                        return false;
                    }

                    if search.ca.checkGarbage(self.settings.simp_garbage_frac) {
                        self.garbageCollect(search);
                    }
                }

                cnt += 1;
            }

            assert!(self.subsumption_queue.is_empty());
        }

        true
    }

    fn asymmVar(&mut self, search : &mut Searcher, budget : &Budget, v : Var) -> bool {
        let cls = {
            let cls = self.occurs.lookup(&v, &search.ca);
            if !search.assigns.isUndef(v) || cls.len() == 0 {
                return true;
            }
            cls.clone()
        };

        let mut bug = false;
        for &cr in cls.iter() {
            // TODO: this mimics original MiniSat bug. Fix it?
            if bug { bug = false; continue; }

            if let Some(l) = asymmetricBranching(search, v, cr) {
                if search.ca.view(cr).len() > 2 { bug = true; }

                self.stats.asymm_lits += 1;
                if !self.strengthenClause(search, cr, l) {
                    return false;
                }
            }
        }

        self.backwardSubsumptionCheck(search, budget, false)
    }

    fn removeClause(&mut self, search : &mut Searcher, cr : ClauseRef) {
        for &lit in search.ca.view(cr).lits() {
            self.elim.bumpLitOcc(&lit, -1);
            self.elim.updateElimHeap(lit.var(), &self.var_status, &search.assigns);
            self.occurs.smudge(&lit.var());
        }

        search.watches.unwatchClauseLazy(search.ca.view(cr));
        search.db.removeClause(&mut search.ca, cr);
    }

    fn strengthenClause(&mut self, search : &mut Searcher, cr : ClauseRef, l : Lit) -> bool {
        assert!(search.assigns.isGroundLevel());

        // FIX: this is too inefficient but would be nice to have (properly implemented)
        // if (!find(subsumption_queue, &c))
        self.subsumption_queue.push(cr);

        let len = search.ca.view(cr).len();
        if len == 2 {
            self.removeClause(search, cr);
            let unit = { let c = search.ca.edit(cr); c.strengthen(l); c.head() }; // TODO: it produces clauses of length 1. Not good.
            tryAssignLit(&mut search.assigns, unit, None) && search.watches.propagate(&mut search.ca, &mut search.assigns).is_none()
        } else {
            search.watches.unwatchClauseStrict(search.ca.view(cr), cr);
            search.db.editClause(&mut search.ca, cr, |c| { c.strengthen(l); assert!(c.len() == len - 1); });
            search.watches.watchClause(search.ca.view(cr), cr);

            self.occurs.removeOcc(&l.var(), cr);
            self.elim.bumpLitOcc(&l, -1);
            self.elim.updateElimHeap(l.var(), &self.var_status, &search.assigns);
            true
        }
    }

    fn eliminateVar(&mut self, search : &mut Searcher, budget : &Budget, elimclauses : &mut elim_clauses::ElimClauses, v : Var) -> bool {
        assert!({ let ref st = self.var_status[&v]; st.frozen == 0 && st.eliminated == 0 });
        assert!(search.assigns.isUndef(v));

        // Split the occurrences into positive and negative:
        let cls = self.occurs.lookup(&v, &search.ca).clone();
        let mut pos = Vec::new();
        let mut neg = Vec::new();
        for &cr in cls.iter() {
            for l in search.ca.view(cr).lits() {
                if l.var() == v {
                    if l.sign() { neg.push(cr); } else { pos.push(cr); }
                    break;
                }
            }
        }

        // Check wether the increase in number of clauses stays within the allowed ('grow'). Moreover, no
        // clause must exceed the limit on the maximal clause size (if it is set):
        let mut cnt = 0;
        for &pr in pos.iter() {
            for &nr in neg.iter() {
                self.stats.merges += 1;
                if let Some(resolvent) = merge(v, search.ca.view(pr), search.ca.view(nr)) {
                    cnt += 1;
                    if cnt > cls.len() + self.settings.grow || (self.settings.clause_lim != -1 && (resolvent.len() as i32) > self.settings.clause_lim) {
                        return true;
                    }
                }
            }
        }

        // Delete and store old clauses:
        self.var_status[&v].eliminated = 1;
        search.heur.setDecisionVar(v, false);
        self.stats.eliminated_vars += 1;

        if pos.len() > neg.len() {
            for &cr in neg.iter() {
                elimclauses.mkElimClause(v, search.ca.view(cr));
            }
            elimclauses.mkElimUnit(v.posLit());
        } else {
            for &cr in pos.iter() {
                elimclauses.mkElimClause(v, search.ca.view(cr));
            }
            elimclauses.mkElimUnit(v.negLit());
        }

        for &cr in cls.iter() {
            self.removeClause(search, cr);
        }

        // Produce clauses in cross product:
        for &pr in pos.iter() {
            for &nr in neg.iter() {
                self.stats.merges += 1;
                if let Some(resolvent) = merge(v, search.ca.view(pr), search.ca.view(nr)) {
                    if !self.addClause(search, &resolvent[..]) {
                        return false;
                    }
                }
            }
        }

        // Free occurs list for this variable:
        self.occurs.clearVar(&v);

        // Free watchers lists for this variable, if possible:
        search.watches.tryClearVar(v);

        self.backwardSubsumptionCheck(search, budget, false)
    }

    // Backward subsumption + backward subsumption resolution
    fn backwardSubsumptionCheck(&mut self, search : &mut Searcher, budget : &Budget, verbose : bool) -> bool {
        assert!(search.assigns.isGroundLevel());

        if verbose {
            trace!("BWD-SUB: queue = {}, trail = {}", self.subsumption_queue.len()
                                                    , self.subsumption_queue.assignsLeft(&search.assigns));
        }

        let mut cnt = 0u64;
        let mut subsumed = 0u64;
        let mut deleted_literals = 0u64;

        while let Some(job) = self.subsumption_queue.pop(&search.ca, &search.assigns) {
            // Empty subsumption queue and return immediately on user-interrupt:
            if budget.interrupted() {
                self.subsumption_queue.clear(&search.assigns);
                break;
            }

            if verbose && cnt % 1000 == 0 {
                trace!("subsumption left: {:10} ({:10} subsumed, {:10} deleted literals)",
                    self.subsumption_queue.len(), subsumed, deleted_literals);
            }
            cnt += 1;

            match job {
                SubsumptionJob::Assign(unit) => {
                    for &cj in self.occurs.lookup(&unit.var(), &search.ca).clone().iter() {
                        if { let c = search.ca.view(cj); !c.is_deleted() && (self.settings.subsumption_lim == -1 || (c.len() as i32) < self.settings.subsumption_lim) } {
                            match unitSubsumes(unit, search.ca.view(cj)) {
                                Subsumes::Different  => {}

                                Subsumes::Exact      => {
                                    subsumed += 1;
                                    self.removeClause(search, cj);
                                }

                                Subsumes::LitSign(l) => {
                                    deleted_literals += 1;
                                    if !self.strengthenClause(search, cj, !l) {
                                        return false;
                                    }
                                }
                            }
                        }
                    }
                }

                SubsumptionJob::Clause(cr)  => {
                    let best = {
                        let c = search.ca.view(cr);
                        let mut best = c.head().var();
                        for &lit in c.litsFrom(1) {
                            // TODO: why not use n_occ?
                            if self.occurs.occsDirty(lit.var()) < self.occurs.occsDirty(best) {
                                best = lit.var();
                            }
                        }
                        best
                    };

                    for &cj in self.occurs.lookup(&best, &search.ca).clone().iter() {
                        if search.ca.isDeleted(cr) {
                            break;
                        }

                        if cj != cr && { let c = search.ca.view(cj); !c.is_deleted() && (self.settings.subsumption_lim == -1 || (c.len() as i32) < self.settings.subsumption_lim) } {
                            match subsumes(search.ca.view(cr), search.ca.view(cj)) {
                                Subsumes::Different  => {}

                                Subsumes::Exact      => {
                                    subsumed += 1;
                                    self.removeClause(search, cj);
                                }

                                Subsumes::LitSign(l) => {
                                    deleted_literals += 1;
                                    if !self.strengthenClause(search, cj, !l) {
                                        return false;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        true
    }

    fn gatherTouchedClauses(&mut self, ca : &mut ClauseAllocator) {
        if self.n_touched == 0 { return; }

        self.subsumption_queue.remarkTouched(ca, false);

        for (v, touched) in self.touched.iter_mut() {
            if *touched != 0 && self.var_status[&v].eliminated == 0 {
                for &cr in self.occurs.lookup(&v, ca) {
                    let c = ca.edit(cr);
                    if !c.touched() {
                        self.subsumption_queue.push(cr);
                        c.setTouched(true);
                    }
                }
                *touched = 0;
            }
        }

        self.subsumption_queue.remarkTouched(ca, true);
        self.n_touched = 0;
    }

    fn garbageCollect(&mut self, search : &mut Searcher) {
        let mut to = ClauseAllocator::newForGC(&search.ca);
        self.relocGC(&mut search.ca, &mut to);
        search.relocGC(to);
    }

    fn relocGC(&mut self, from : &mut ClauseAllocator, to : &mut ClauseAllocator) {
        self.occurs.relocGC(from, to);
        self.subsumption_queue.relocGC(from, to);
    }

    // TODO: remove
    pub fn off(search : &mut Searcher) {
        search.db.settings.remove_satisfied = true;
        search.ca.set_extra_clause_field(false);

        // Force full cleanup (this is safe and desirable since it only happens once):
        search.heur.rebuildOrderHeap(&search.assigns);
        search.garbageCollect();
    }

    pub fn on(search : &mut Searcher) {
        search.ca.set_extra_clause_field(true);
        search.db.settings.remove_satisfied = false;
    }
}


fn asymmetricBranching(search : &mut Searcher, v : Var, cr : ClauseRef) -> Option<Lit> {
    assert!(search.assigns.isGroundLevel());

    let l = {
        let c = search.ca.view(cr);
        if c.is_deleted() || satisfiedWith(c, &search.assigns) {
            return None;
        }

        search.assigns.newDecisionLevel();

        let mut vl = None;
        for &lit in c.lits() {
            if v == lit.var() {
                vl = Some(lit);
            } else if search.assigns.isUndef(lit.var()) {
                search.assigns.assignLit(!lit, None);
            }
        }

        vl.unwrap()
    };

    let res = search.watches.propagate(&mut search.ca, &mut search.assigns);
    search.cancelUntil(GroundLevel);
    res.map(|_| l)
}
