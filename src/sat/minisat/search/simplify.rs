use crate::sat::formula::{util::*, clause::*, LBool, Lit, Var, VarMap};
use super::{util::*, SearchRes, SearchSettings, Searcher};
use super::super::budget::Budget;
use self::{elim_clauses::*, elim_queue::ElimOcc, subsumes::*, subsumption_queue::*};
use super::{backtrack::*, clause_db::*, decision_heuristic::*};

pub mod elim_clauses;
mod elim_queue;
pub mod subsumes;
mod subsumption_queue;


pub struct SimplificatorSettings {
    pub grow: usize, // Allow a variable elimination step to grow by a number of clauses (default to zero).
    pub clause_lim: i32, // Variables are not eliminated if it produces a resolvent with a length above this limit. -1 means no limit.
    pub subsumption_lim: i32, // Do not check if subsumption against a clause larger than this. -1 means no limit.
    pub simp_garbage_frac: f64, // A different limit for when to issue a GC during simplification (Also see 'garbage_frac').
    pub use_asymm: bool,        // Shrink clauses by asymmetric branching.
    pub use_elim: bool,         // Perform variable elimination.
}

impl Default for SimplificatorSettings {
    fn default() -> Self {
        SimplificatorSettings {
            grow: 0,
            clause_lim: 20,
            subsumption_lim: 1000,
            simp_garbage_frac: 0.5,
            use_asymm: false,
            use_elim: true,
        }
    }
}

impl SimplificatorSettings {
    pub fn validate_resolvent_len(&self, len: usize) -> bool {
        self.clause_lim == -1 || ((len as i32) <= self.clause_lim)
    }

    pub fn validate_subsumption_len(&self, len: usize) -> bool {
        self.subsumption_lim == -1 || ((len as i32) < self.subsumption_lim)
    }
}


#[derive(Default)]
struct Stats {
    asymm_lits: u64,
    eliminated_vars: u64,
}


pub struct Touched {
    touched: VarMap<bool>,
    n_touched: usize,
}

impl Touched {
    pub fn new() -> Self {
        Touched {
            touched: VarMap::new(),
            n_touched: 0
        }
    }

    pub fn is_empty(&self) -> bool {
        self.n_touched == 0
    }

    pub fn init_var(&mut self, v: Var) {
        self.touched.insert(&v, false);
    }

    pub fn add_clause(&mut self, lits: &[Lit]) {
        for &lit in lits {
            self.touched[&lit.var()] = true;
            self.n_touched += 1;
        }
    }


    fn enqueue_touched_clauses(&mut self, ca: &mut ClauseAllocator, elo: &mut ElimOcc, queue: &mut SubsumptionQueue) {
        if self.is_empty() {
            return;
        }

        for &cr in queue.iter() {
            ca.edit(cr).set_touched(true);
        }

        for (var, touched) in self.touched.iter_mut() {
            if !*touched || elo.is_eliminated(var) {
                continue;
            }

            for &cr in elo.occurs.lookup(ca, var) {
                let c = ca.edit(cr);
                if !c.is_touched() {
                    queue.push(cr);
                    c.set_touched(true);
                }
            }
            *touched = false;
        }

        for &cr in queue.iter() {
            ca.edit(cr).set_touched(false);
        }

        self.n_touched = 0;
    }
}


pub struct Simplificator {
    settings: SimplificatorSettings,
    stats: Stats,
    elo: elim_queue::ElimOcc,
    touched: Touched,
    subsumption_queue: SubsumptionQueue,
}

impl Simplificator {
    pub fn new(settings: SimplificatorSettings) -> Self {
        Simplificator {
            settings,
            stats: Stats::default(),
            elo: elim_queue::ElimOcc::new(),
            touched: Touched::new(),
            subsumption_queue: SubsumptionQueue::new()
        }
    }

    pub fn init_var(&mut self, v: Var) {
        self.elo.init_var(v);
        self.touched.init_var(v);
    }

    pub fn add_clause(&mut self, search: &mut Searcher, ps: &[Lit]) -> Result<(), ()> {
        //#ifndef NDEBUG
        for l in ps.iter() {
            assert!(!self.elo.is_eliminated(l.var()));
        }
        //#endif

        match search.add_clause(ps) {
            super::AddClauseRes::UnSAT => Err(()),
            super::AddClauseRes::Consumed => Ok(()),
            super::AddClauseRes::Added(cr) => {
                // NOTE: the clause is added to the queue immediately and then
                // again during 'gather_touched_clauses()'. If nothing happens
                // in between, it will only be checked once. Otherwise, it may
                // be checked twice unnecessarily. This is an unfortunate
                // consequence of how backward subsumption is used to mimic
                // forward subsumption.
                self.subsumption_queue.push(cr);
                let lits = search.bt.ca.literals(cr);
                self.elo.add_clause(cr, lits);
                self.touched.add_clause(lits);
                Ok(())
            }
        }
    }

    pub fn solve_limited(
        &mut self,
        mut search: Searcher,
        ss: &SearchSettings,
        budget: &Budget,
        elimclauses: &mut ElimClauses,
        assumptions: &[Lit],
    ) -> SearchRes {
        let mut extra_frozen: Vec<Var> = Vec::with_capacity(assumptions.len());

        // Assumptions must be temporarily frozen to run variable elimination:
        for lit in assumptions.iter() {
            let ref mut st = self.elo.var_status[&lit.var()];

            // If an assumption has been eliminated, remember it.
            assert!(!st.eliminated);
            if !st.frozen {
                // Freeze and store.
                st.frozen = true;
                extra_frozen.push(lit.var());
            }
        }

        if let None = search.bt.propagate() {
            search.try_simplify();
        } else {
            return SearchRes::UnSAT(search.stats());
        }

        if !self.eliminate(&mut search, budget, elimclauses).is_ok() {
            return SearchRes::UnSAT(search.stats());
        }

        match search.search(ss, budget, assumptions) {
            SearchRes::Interrupted(prog, ns) => {
                // Unfreeze the assumptions that were frozen:
                for &v in extra_frozen.iter() {
                    self.elo.var_status[&v].frozen = false;
                    self.elo.elim.update_elim_heap(v, &self.elo.var_status, &ns.bt.assigns);
                }

                SearchRes::Interrupted(prog, ns)
            }

            other => other,
        }
    }

    pub fn eliminate(
        &mut self,
        search: &mut Searcher,
        budget: &Budget,
        elimclauses: &mut ElimClauses,
    ) -> Result<(), ()> {
        // Main simplification loop:
        while !self.touched.is_empty() || self.subsumption_queue.assigns_left(&search.bt.assigns) > 0
            || self.elo.elim.len() > 0
        {
            self.touched.enqueue_touched_clauses(&mut search.bt.ca, &mut self.elo, &mut self.subsumption_queue);
            self.backward_subsumption_check(&mut search.bt, &mut search.ctx.db, budget, true)?;

            // Empty elim_heap and return immediately on user-interrupt:
            if budget.interrupted() {
                assert_eq!(self.subsumption_queue.assigns_left(&search.bt.assigns), 0);
                assert!(self.subsumption_queue.is_empty());
                assert!(self.touched.is_empty());
                self.elo.elim.clear();
                break;
            }

            trace!("ELIM: vars = {}", self.elo.elim.len());
            let mut cnt = 0;
            while let Some(var) = self.elo.elim.pop() {
                if budget.interrupted() {
                    break;
                }

                if cnt % 100 == 0 {
                    trace!("elimination left: {:10}", self.elo.elim.len());
                }
                cnt += 1;

                if self.elo.is_eliminated(var) || !search.bt.assigns.is_undef(var) {
                    continue;
                }

                if self.settings.use_asymm {
                    // Temporarily freeze variable. Otherwise, it would immediately end up on the queue again:
                    let was_frozen = self.elo.var_status[&var].frozen;
                    self.elo.var_status[&var].frozen = true;
                    self.asymm_var(&mut search.bt, &mut search.ctx.db, &mut search.ctx.heur, var)?;
                    self.backward_subsumption_check(&mut search.bt, &mut search.ctx.db, budget, false)?;
                    self.elo.var_status[&var].frozen = was_frozen;
                }

                // At this point, the variable may have been set by asymmetric branching, so check it
                // again. Also, don't eliminate frozen variables:
                if self.settings.use_elim && search.bt.assigns.is_undef(var) && !self.elo.is_frozen(var) {
                    self.eliminate_var(search, elimclauses, var)?;
                    self.backward_subsumption_check(&mut search.bt, &mut search.ctx.db, budget, false)?;
                }

                self.try_garbage_collect(search);
            }

            assert!(self.subsumption_queue.is_empty());
        }

        Ok(())
    }

    fn strengthen_clause(&mut self, bt: &mut BacktrackableFormula, db: &mut ClauseDB, cr: ClauseRef, l: Lit) -> Result<(), ()> {
        assert!(bt.is_ground_level());

        let len = bt.ca.view(cr).len();
        if len == 2 {
            self.elo.smudge_clause(&bt.assigns, bt.ca.literals(cr));
            bt.lazy_detach(cr);
            db.remove_clause(&mut bt.ca, cr);

            let unit = {
                let c = bt.ca.edit(cr);
                if l == c.prefix[0] { c.prefix[1] } else { c.prefix[0] }
            };

            try_propagate(bt, unit, None)?;
        } else {
            bt.force_detach(cr);
            db.edit_clause(&mut bt.ca, cr, |clause| {
                strengthen(clause, l);
            });
            bt.attach(cr);

            self.elo.remove_lit(&bt.assigns, l, cr);
        }
        Ok(())
    }

    fn asymm_var(&mut self, bt: &mut BacktrackableFormula, db: &mut ClauseDB, heur: &mut DecisionHeuristic, v: Var) -> Result<bool, ()> {
        if !bt.assigns.is_undef(v) {
            return Ok(false);
        }

        let cls = {
            let cls = self.elo.occurs.lookup(&bt.ca, v);
            if cls.is_empty() {
                return Ok(false);
            }
            cls.clone()
        };

        let mut bug = false;
        for &cr in cls.iter() {
            // TODO: this mimics original MiniSat bug. Fix it?
            if bug {
                bug = false;
                continue;
            }

            if let Some(l) = asymmetric_branching(bt, heur, v, cr) {
                if bt.ca.view(cr).len() > 2 {
                    bug = true;
                }

                self.stats.asymm_lits += 1;
                self.subsumption_queue.try_push(cr);
                self.strengthen_clause(bt, db, cr, l)?;
            }
        }

        Ok(true)
    }

    fn eliminate_var(&mut self, search: &mut Searcher, elimclauses: &mut ElimClauses, v: Var) -> Result<bool, ()> {
        assert!({
            let ref st = self.elo.var_status[&v];
            !st.frozen && !st.eliminated
        });
        assert!(search.bt.assigns.is_undef(v));

        let cls = self.elo.occurs.lookup(&search.bt.ca, v).clone();

        // Split the occurrences into positive and negative:
        let (pos, neg) = {
            let mut pos = Vec::with_capacity(cls.len());
            let mut neg = Vec::with_capacity(cls.len());
            for &cr in cls.iter() {
                for l in search.bt.ca.view(cr).lits() {
                    if l.var() == v {
                        if l.sign() {
                            neg.push(cr);
                        } else {
                            pos.push(cr);
                        }
                        break;
                    }
                }
            }
            (pos, neg)
        };

        // Check wether the increase in number of clauses stays within the allowed ('grow'). Moreover, no
        // clause must exceed the limit on the maximal clause size (if it is set):
        let resolvents = {
            let max_resolvents = self.settings.grow + pos.len() + neg.len();
            let mut resolvents = Vec::with_capacity(max_resolvents + 1);
            for &pr in pos.iter() {
                for &nr in neg.iter() {
                    if let Some(resolvent) = merge(v, search.bt.ca.literals(pr), search.bt.ca.literals(nr)) {
                        let len = resolvent.len();
                        resolvents.push(resolvent);
                        if resolvents.len() > max_resolvents || !self.settings.validate_resolvent_len(len) {
                            return Ok(false);
                        }
                    }
                }
            }
            resolvents
        };

        // Delete and store old clauses:
        self.elo.var_status[&v].eliminated = true;
        search.ctx.heur.set_decision_var(v, false);
        self.stats.eliminated_vars += 1;

        if pos.len() > neg.len() {
            for &cr in neg.iter() {
                elimclauses.mk_elim_clause(v, search.bt.ca.view(cr).lits());
            }
            elimclauses.mk_elim_unit(v.pos_lit());
        } else {
            for &cr in pos.iter() {
                elimclauses.mk_elim_clause(v, search.bt.ca.view(cr).lits());
            }
            elimclauses.mk_elim_unit(v.neg_lit());
        }

        for &cr in cls.iter() {
            self.elo.smudge_clause(&search.bt.assigns, search.bt.ca.literals(cr));
            search.bt.lazy_detach(cr);
            search.ctx.db.remove_clause(&mut search.bt.ca, cr);
        }

        // Produce clauses in cross product:
        for resolvent in resolvents.iter() {
            self.add_clause(search, resolvent.as_slice())?;
        }

        // Free occurs list for this variable:
        self.elo.occurs.clear_var(&v);

        // Free watchers lists for this variable, if possible:
        search.bt.try_clear_var(v);

        Ok(true)
    }

    // Backward subsumption + backward subsumption resolution
    fn backward_subsumption_check(
        &mut self,
        bt: &mut BacktrackableFormula,
        db: &mut ClauseDB,
        budget: &Budget,
        verbose: bool,
    ) -> Result<(), ()> {
        assert!(bt.is_ground_level());

        if verbose {
            trace!(
                "BWD-SUB: queue = {}, trail = {}",
                self.subsumption_queue.len(),
                self.subsumption_queue.assigns_left(&bt.assigns)
            );
        }

        let mut subsumed = 0u64;
        let mut deleted_literals = 0u64;

        let mut cnt = 0u64;
        while let Some(job) = self.subsumption_queue.pop(&bt.ca, &bt.assigns) {
            // Empty subsumption queue and return immediately on user-interrupt:
            if budget.interrupted() {
                self.subsumption_queue.clear(&bt.assigns);
                break;
            }

            if verbose && cnt % 1000 == 0 {
                trace!(
                    "subsumption left: {:10} ({:10} subsumed, {:10} deleted literals)",
                    self.subsumption_queue.len(), subsumed, deleted_literals
                );
            }
            cnt += 1;

            let lookup_var =
                match job {
                    SubsumptionJob::Assign(unit) => {
                        unit.var()
                    }

                    SubsumptionJob::Clause(sub_cr) => {
                        let c = bt.ca.view(sub_cr);
                        let mut best = c.prefix[0].var();
                        for &lit in &c.lits()[1..] {
                            // TODO: why not use n_occ?
                            if self.elo.occurs.occs_dirty(lit.var()) < self.elo.occurs.occs_dirty(best) {
                                best = lit.var();
                            }
                        }
                        best
                    }
                };

            for &cref_j in self.elo.occurs.lookup(&bt.ca, lookup_var).clone().iter() {
                if let SubsumptionJob::Clause(sub_cr) = job {
                    if bt.ca.is_deleted(sub_cr) {
                        break;
                    }
                    if cref_j == sub_cr {
                        continue;
                    }
                }

                let clause = bt.ca.view(cref_j);
                if clause.is_deleted() || !self.settings.validate_subsumption_len(clause.len()) {
                    continue;
                }

                let sub =
                    match job {
                        SubsumptionJob::Clause(sub_cr) => {
                            subsumes(bt.ca.view(sub_cr), clause)
                        }
                        SubsumptionJob::Assign(unit) => {
                            unit_subsumes(unit, clause)
                        }
                    };

                match sub {
                    Subsumes::Different => {}

                    Subsumes::Exact => {
                        subsumed += 1;
                        self.elo.smudge_clause(&bt.assigns, clause.lits());
                        bt.lazy_detach(cref_j);
                        db.remove_clause(&mut bt.ca, cref_j);
                    }

                    Subsumes::LitSign(l) => {
                        deleted_literals += 1;
                        self.subsumption_queue.try_push(cref_j);
                        self.strengthen_clause(bt, db, cref_j, !l)?;
                    }
                }
            }
        }

        Ok(())
    }


    fn try_garbage_collect(&mut self, search: &mut Searcher) {
        if search.bt.ca.check_garbage(self.settings.simp_garbage_frac) {
            let mut gc = search.gc();
            self.elo.occurs.gc(&mut gc);
            self.subsumption_queue.gc(&mut gc);
        }
    }


    // TODO: remove
    pub fn off(search: &mut Searcher) {
        search.ctx.db.settings.remove_satisfied = true;
        search.bt.ca.extra_clause_field = false;

        // Force full cleanup (this is safe and desirable since it only happens once):
        search.ctx.heur.rebuild_order_heap(&search.bt.assigns);

        search.gc();
    }

    pub fn on(search: &mut Searcher) {
        search.bt.ca.extra_clause_field = true;
        search.ctx.db.settings.remove_satisfied = false;
    }
}


fn try_propagate(bt: &mut BacktrackableFormula, p: Lit, reason: Option<ClauseRef>) -> Result<(), ()> {
    match bt.assigns.of_lit(p) {
        LBool::False => { return Err(()); }
        LBool::True  => {}
        LBool::Undef => { bt.assigns.assign_lit(p, reason); }
    }

    if bt.propagate().is_none() {
        Ok(())
    } else {
        Err(())
    }
}

fn strengthen(clause: &mut Clause, p: Lit) {
    assert!(clause.len() > 2, "Clause is too short");
    unsafe {
        let (mut l, r) = clause.ptr_range();
        while l < r {
            if *l == p {
                l = l.offset(1);
                while l < r {
                    *l.offset(-1) = *l;
                    l = l.offset(1);
                }
                clause.shrink_by(1);

                let new_abstraction = calc_abstraction(clause.lits());
                if let ClauseHeader::Clause { ref mut abstraction } = clause.header {
                    *abstraction = Some(new_abstraction);
                }
                return;
            }
            l = l.offset(1);
        }

        assert!(false, "Literal {:?} is not found in {:?}", p, clause);
    }
}
