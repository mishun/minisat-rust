use crate::sat::formula::{Lit, Var, VarMap};
use crate::sat::formula::assignment::*;
use crate::sat::formula::clause::*;
use crate::sat::formula::subsumes::*;
use crate::sat::formula::util::*;
use super::{SearchRes, SearchSettings, Searcher};
use super::super::budget::Budget;
use self::subsumption_queue::*;
use super::util::*;
use crate::sat::minisat::search::backtrack::BacktrackableFormula;
use crate::sat::minisat::search::clause_db::ClauseDB;
use crate::sat::minisat::search::decision_heuristic::DecisionHeuristic;

pub mod elim_clauses;
mod elim_queue;
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
    touched: VarMap<i8>,
    n_touched: usize,
}

impl Touched {
    pub fn new() -> Self {
        Touched {
            touched: VarMap::new(),
            n_touched: 0
        }
    }

    pub fn count(&self) -> usize {
        self.n_touched
    }

    pub fn init_var(&mut self, v: Var) {
        self.touched.insert(&v, 0);
    }

    pub fn add_clause(&mut self, lits: &[Lit]) {
        for &lit in lits {
            self.touched[&lit.var()] = 1;
            self.n_touched += 1;
        }
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
            assert_eq!(self.elo.var_status[&l.var()].eliminated, 0);
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
        elimclauses: &mut elim_clauses::ElimClauses,
        assumptions: &[Lit],
    ) -> SearchRes {
        let mut extra_frozen: Vec<Var> = Vec::new();

        // Assumptions must be temporarily frozen to run variable elimination:
        for lit in assumptions.iter() {
            let ref mut st = self.elo.var_status[&lit.var()];

            // If an assumption has been eliminated, remember it.
            assert_eq!(st.eliminated, 0);
            if st.frozen == 0 {
                // Freeze and store.
                st.frozen = 1;
                extra_frozen.push(lit.var());
            }
        }

        if search.preprocess() && self.eliminate(&mut search, budget, elimclauses).is_ok() {
            match search.search(ss, budget, assumptions) {
                SearchRes::Interrupted(prog, ns) => {
                    // Unfreeze the assumptions that were frozen:
                    for &v in extra_frozen.iter() {
                        self.elo.var_status[&v].frozen = 0;
                        self.elo.elim.update_elim_heap(v, &self.elo.var_status, &ns.bt.assigns);
                    }

                    SearchRes::Interrupted(prog, ns)
                }

                other => other,
            }
        } else {
            SearchRes::UnSAT(search.stats())
        }
    }

    pub fn eliminate(
        &mut self,
        search: &mut Searcher,
        budget: &Budget,
        elimclauses: &mut elim_clauses::ElimClauses,
    ) -> Result<(), ()> {
        // Main simplification loop:
        while self.touched.count() > 0 || self.subsumption_queue.assigns_left(&search.bt.assigns) > 0
            || self.elo.elim.len() > 0
        {
            self.gather_touched_clauses(&mut search.bt.ca);
            self.backward_subsumption_check(&mut search.bt, &mut search.ctx.db, budget, true)?;

            // Empty elim_heap and return immediately on user-interrupt:
            if budget.interrupted() {
                assert_eq!(self.subsumption_queue.assigns_left(&search.bt.assigns), 0);
                assert!(self.subsumption_queue.is_empty());
                assert_eq!(self.touched.count(), 0);
                self.elo.elim.clear();
                break;
            }

            trace!("ELIM: vars = {}", self.elo.elim.len());
            let mut cnt = 0;
            while let Some(var) = self.elo.elim.pop() {
                if budget.interrupted() {
                    break;
                }
                if self.elo.var_status[&var].eliminated == 0 && search.bt.assigns.is_undef(var) {
                    if cnt % 100 == 0 {
                        trace!("elimination left: {:10}", self.elo.elim.len());
                    }

                    if self.settings.use_asymm {
                        // Temporarily freeze variable. Otherwise, it would immediately end up on the queue again:
                        let was_frozen = self.elo.var_status[&var].frozen;
                        self.elo.var_status[&var].frozen = 1;
                        self.asymm_var(&mut search.bt, &mut search.ctx.db, &mut search.ctx.heur, budget, var)?;
                        self.elo.var_status[&var].frozen = was_frozen;
                    }

                    // At this point, the variable may have been set by asymmetric branching, so check it
                    // again. Also, don't eliminate frozen variables:
                    if self.settings.use_elim && search.bt.assigns.is_undef(var) && self.elo.var_status[&var].frozen == 0 {
                        self.eliminate_var(search, budget, elimclauses, var)?;
                    }

                    if search.bt.ca.check_garbage(self.settings.simp_garbage_frac) {
                        self.garbage_collect(search);
                    }
                }

                cnt += 1;
            }

            assert!(self.subsumption_queue.is_empty());
        }

        Ok(())
    }

    fn asymm_var(&mut self, bt: &mut BacktrackableFormula, db: &mut ClauseDB, heur: &mut DecisionHeuristic, budget: &Budget, v: Var) -> Result<(), ()> {
        let cls = {
            let cls = self.elo.occurs.lookup(&bt.ca, v);
            if !bt.assigns.is_undef(v) || cls.len() == 0 {
                return Ok(());
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
                self.strengthen_clause(bt, db, cr, l)?;
            }
        }

        self.backward_subsumption_check(bt, db, budget, false)
    }

    fn remove_clause(&mut self, bt: &mut BacktrackableFormula, db: &mut ClauseDB, cr: ClauseRef) {
        self.elo.remove_clause(&bt.assigns, bt.ca.literals(cr));
        bt.lazy_detach(cr);
        db.remove_clause(&mut bt.ca, cr);
    }

    fn strengthen_clause(&mut self, bt: &mut BacktrackableFormula, db: &mut ClauseDB, cr: ClauseRef, l: Lit) -> Result<(), ()> {
        assert!(bt.is_ground_level());

        // FIX: this is too inefficient but would be nice to have (properly implemented)
        // if (!find(subsumption_queue, &c))
        self.subsumption_queue.push(cr);

        let len = bt.ca.view(cr).len();
        if len == 2 {
            self.remove_clause(bt, db, cr);
            let unit = {
                let c = bt.ca.edit(cr);
                c.strengthen(l);
                c.head[0]
            }; // TODO: it produces clauses of length 1. Not good.
            if try_assign_lit(&mut bt.assigns, unit, None) && bt.propagate().is_none() {
                Ok(())
            } else {
                Err(())
            }
        } else {
            bt.force_detach(cr);
            db.edit_clause(&mut bt.ca, cr, |c| {
                c.strengthen(l);
                assert_eq!(c.len(), len - 1);
            });
            bt.attach(cr);

            self.elo.remove_lit(&bt.assigns, l, cr);
            Ok(())
        }
    }

    fn eliminate_var(
        &mut self,
        search: &mut Searcher,
        budget: &Budget,
        elimclauses: &mut elim_clauses::ElimClauses,
        v: Var,
    ) -> Result<(), ()> {
        assert!({
            let ref st = self.elo.var_status[&v];
            st.frozen == 0 && st.eliminated == 0
        });
        assert!(search.bt.assigns.is_undef(v));

        let cls = self.elo.occurs.lookup(&search.bt.ca, v).clone();

        // Split the occurrences into positive and negative:
        let (pos, neg) = {
            let mut pos = Vec::new();
            let mut neg = Vec::new();
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
                            return Ok(());
                        }
                    }
                }
            }
            resolvents
        };

        // Delete and store old clauses:
        self.elo.var_status[&v].eliminated = 1;
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
            self.remove_clause(&mut search.bt, &mut search.ctx.db, cr);
        }

        // Produce clauses in cross product:
        for resolvent in resolvents.iter() {
            self.add_clause(search, resolvent.as_slice())?
        }

        // Free occurs list for this variable:
        self.elo.occurs.clear_var(&v);

        // Free watchers lists for this variable, if possible:
        search.bt.try_clear_var(v);

        self.backward_subsumption_check(&mut search.bt, &mut search.ctx.db, budget, false)
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

        let mut cnt = 0u64;
        let mut subsumed = 0u64;
        let mut deleted_literals = 0u64;

        while let Some(job) = self.subsumption_queue.pop(&bt.ca, &bt.assigns) {
            // Empty subsumption queue and return immediately on user-interrupt:
            if budget.interrupted() {
                self.subsumption_queue.clear(&bt.assigns);
                break;
            }

            if verbose && cnt % 1000 == 0 {
                trace!(
                    "subsumption left: {:10} ({:10} subsumed, {:10} deleted literals)",
                    self.subsumption_queue.len(),
                    subsumed,
                    deleted_literals
                );
            }
            cnt += 1;

            match job {
                SubsumptionJob::Assign(unit) => {
                    for &cj in self.elo.occurs.lookup(&bt.ca, unit.var()).clone().iter() {
                        let c = bt.ca.view(cj);
                        if c.is_deleted() || !self.settings.validate_subsumption_len(c.len()) {
                            continue;
                        }

                        match unit_subsumes(unit, c) {
                            Subsumes::Different => {}

                            Subsumes::Exact => {
                                subsumed += 1;
                                self.remove_clause(bt, db, cj);
                            }

                            Subsumes::LitSign(l) => {
                                deleted_literals += 1;
                                self.strengthen_clause(bt, db, cj, !l)?;
                            }
                        }
                    }
                }

                SubsumptionJob::Clause(sub_cr) => {
                    let best = {
                        let c = bt.ca.view(sub_cr);
                        let mut best = c.head[0].var();
                        for &lit in &c.lits()[1..] {
                            // TODO: why not use n_occ?
                            if self.elo.occurs.occs_dirty(lit.var()) < self.elo.occurs.occs_dirty(best) {
                                best = lit.var();
                            }
                        }
                        best
                    };

                    for &cj in self.elo.occurs.lookup(&bt.ca, best).clone().iter() {
                        let sub_c = bt.ca.view(sub_cr);
                        if sub_c.is_deleted() {
                            break;
                        }

                        if cj == sub_cr {
                            continue;
                        }

                        let c = bt.ca.view(cj);
                        if c.is_deleted() || !self.settings.validate_subsumption_len(c.len()) {
                            continue;
                        }

                        match subsumes(sub_c, c) {
                            Subsumes::Different => {}

                            Subsumes::Exact => {
                                subsumed += 1;
                                self.remove_clause(bt, db, cj);
                            }

                            Subsumes::LitSign(l) => {
                                deleted_literals += 1;
                                self.strengthen_clause(bt, db, cj, !l)?;
                            }
                        }
                    }
                }
            }
        }

        Ok(())
    }

    fn gather_touched_clauses(&mut self, ca: &mut ClauseAllocator) {
        if self.touched.count() == 0 {
            return;
        }

        for &cr in self.subsumption_queue.iter() {
            ca.edit(cr).set_touched(true);
        }

        for (v, touched) in self.touched.touched.iter_mut() {
            if *touched != 0 && self.elo.var_status[&v].eliminated == 0 {
                for &cr in self.elo.occurs.lookup(ca, v) {
                    let c = ca.edit(cr);
                    if !c.is_touched() {
                        self.subsumption_queue.push(cr);
                        c.set_touched(true);
                    }
                }
                *touched = 0;
            }
        }

        for &cr in self.subsumption_queue.iter() {
            ca.edit(cr).set_touched(false);
        }

        self.touched.n_touched = 0;
    }

    fn garbage_collect(&mut self, search: &mut Searcher) {
        let mut to = ClauseAllocator::new_for_gc(&search.bt.ca);
        self.reloc_gc(&mut search.bt.ca, &mut to);
        search.reloc_gc(to);
    }

    fn reloc_gc(&mut self, from: &mut ClauseAllocator, to: &mut ClauseAllocator) {
        self.elo.occurs.reloc_gc(from, to);
        self.subsumption_queue.reloc_gc(from, to);
    }


    // TODO: remove
    pub fn off(search: &mut Searcher) {
        search.ctx.db.settings.remove_satisfied = true;
        search.bt.ca.set_extra_clause_field(false);

        // Force full cleanup (this is safe and desirable since it only happens once):
        search.ctx.heur.rebuild_order_heap(&search.bt.assigns);
        search.garbage_collect();
    }

    pub fn on(search: &mut Searcher) {
        search.bt.ca.set_extra_clause_field(true);
        search.ctx.db.settings.remove_satisfied = false;
    }
}
