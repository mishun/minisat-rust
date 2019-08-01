use crate::sat::formula::{Lit, Var, VarMap};
use crate::sat::formula::assignment::*;
use crate::sat::formula::clause::*;
use crate::sat::formula::subsumes::*;
use crate::sat::formula::util::*;
use super::{SearchRes, SearchSettings, Searcher};
use super::super::budget::Budget;
use self::subsumption_queue::*;

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


#[derive(Default)]
struct Stats {
    merges: u64,
    asymm_lits: u64,
    eliminated_vars: u64,
}


pub struct Simplificator {
    settings: SimplificatorSettings,
    stats: Stats,
    var_status: VarMap<elim_queue::VarStatus>,
    occurs: elim_queue::OccLists,
    elim: elim_queue::ElimQueue,
    touched: VarMap<i8>,
    n_touched: usize,
    subsumption_queue: SubsumptionQueue,
}

impl Simplificator {
    pub fn new(settings: SimplificatorSettings) -> Self {
        Simplificator {
            settings,
            stats: Stats::default(),
            var_status: VarMap::new(),
            occurs: elim_queue::OccLists::new(),
            elim: elim_queue::ElimQueue::new(),
            touched: VarMap::new(),
            n_touched: 0,
            subsumption_queue: SubsumptionQueue::new(),
        }
    }

    pub fn init_var(&mut self, v: Var) {
        self.var_status.insert(
            &v,
            elim_queue::VarStatus {
                frozen: 0,
                eliminated: 0,
            },
        );
        self.occurs.init_var(&v);
        self.touched.insert(&v, 0);
        self.elim.init_var(v);
    }

    pub fn add_clause(&mut self, search: &mut Searcher, ps: &[Lit]) -> bool {
        //#ifndef NDEBUG
        for l in ps.iter() {
            assert_eq!(self.var_status[&l.var()].eliminated, 0);
        }
        //#endif

        match search.add_clause(ps) {
            super::AddClauseRes::UnSAT => false,
            super::AddClauseRes::Consumed => true,
            super::AddClauseRes::Added(c, cr) => {
                // NOTE: the clause is added to the queue immediately and then
                // again during 'gather_touched_clauses()'. If nothing happens
                // in between, it will only be checked once. Otherwise, it may
                // be checked twice unnecessarily. This is an unfortunate
                // consequence of how backward subsumption is used to mimic
                // forward subsumption.
                self.subsumption_queue.push(cr);

                for &lit in c.lits() {
                    self.occurs.push_occ(&lit.var(), cr);
                    self.touched[&lit.var()] = 1;
                    self.n_touched += 1;
                    self.elim.bump_lit_occ(&lit, 1);
                }

                true
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
            let ref mut st = self.var_status[&lit.var()];

            // If an assumption has been eliminated, remember it.
            assert_eq!(st.eliminated, 0);
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
                        self.elim.update_elim_heap(v, &self.var_status, &ns.assigns);
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
    ) -> bool {
        // Main simplification loop:
        while self.n_touched > 0 || self.subsumption_queue.assigns_left(&search.assigns) > 0
            || self.elim.len() > 0
        {
            self.gather_touched_clauses(&mut search.ca);

            if !self.backward_subsumption_check(search, budget, true) {
                return false;
            }

            // Empty elim_heap and return immediately on user-interrupt:
            if budget.interrupted() {
                assert_eq!(self.subsumption_queue.assigns_left(&search.assigns), 0);
                assert!(self.subsumption_queue.is_empty());
                assert_eq!(self.n_touched, 0);
                self.elim.clear();
                return true;
            }

            trace!("ELIM: vars = {}", self.elim.len());
            let mut cnt = 0;
            while let Some(var) = self.elim.pop() {
                if budget.interrupted() {
                    break;
                }
                if self.var_status[&var].eliminated == 0 && search.assigns.is_undef(var) {
                    if cnt % 100 == 0 {
                        trace!("elimination left: {:10}", self.elim.len());
                    }

                    if self.settings.use_asymm {
                        // Temporarily freeze variable. Otherwise, it would immediately end up on the queue again:
                        let was_frozen = self.var_status[&var].frozen;
                        self.var_status[&var].frozen = 1;
                        if !self.asymm_var(search, budget, var) {
                            return false;
                        }
                        self.var_status[&var].frozen = was_frozen;
                    }

                    // At this point, the variable may have been set by asymmetric branching, so check it
                    // again. Also, don't eliminate frozen variables:
                    if self.settings.use_elim && search.assigns.is_undef(var)
                        && self.var_status[&var].frozen == 0
                        && !self.eliminate_var(search, budget, elimclauses, var)
                    {
                        return false;
                    }

                    if search.ca.check_garbage(self.settings.simp_garbage_frac) {
                        self.garbage_collect(search);
                    }
                }

                cnt += 1;
            }

            assert!(self.subsumption_queue.is_empty());
        }

        true
    }

    fn asymm_var(&mut self, search: &mut Searcher, budget: &Budget, v: Var) -> bool {
        let cls = {
            let cls = self.occurs.lookup(&v, &search.ca);
            if !search.assigns.is_undef(v) || cls.len() == 0 {
                return true;
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

            if let Some(l) = asymmetric_branching(search, v, cr) {
                if search.ca.view(cr).len() > 2 {
                    bug = true;
                }

                self.stats.asymm_lits += 1;
                if !self.strengthen_clause(search, cr, l) {
                    return false;
                }
            }
        }

        self.backward_subsumption_check(search, budget, false)
    }

    fn remove_clause(&mut self, search: &mut Searcher, cr: ClauseRef) {
        for &lit in search.ca.view(cr).lits() {
            self.elim.bump_lit_occ(&lit, -1);
            self.elim
                .update_elim_heap(lit.var(), &self.var_status, &search.assigns);
            self.occurs.smudge(&lit.var());
        }

        search.watches.unwatch_clause_lazy(search.ca.view(cr));
        search.db.remove_clause(&mut search.ca, cr);
    }

    fn strengthen_clause(&mut self, search: &mut Searcher, cr: ClauseRef, l: Lit) -> bool {
        assert!(search.assigns.is_ground_level());

        // FIX: this is too inefficient but would be nice to have (properly implemented)
        // if (!find(subsumption_queue, &c))
        self.subsumption_queue.push(cr);

        let len = search.ca.view(cr).len();
        if len == 2 {
            self.remove_clause(search, cr);
            let unit = {
                let c = search.ca.edit(cr);
                c.strengthen(l);
                c.head[0]
            }; // TODO: it produces clauses of length 1. Not good.
            try_assign_lit(&mut search.assigns, unit, None)
                && search.watches.propagate(&mut search.ca, &mut search.assigns).is_none()
        } else {
            search.watches.unwatch_clause_strict(search.ca.view(cr), cr);
            search.db.edit_clause(&mut search.ca, cr, |c| {
                c.strengthen(l);
                assert_eq!(c.len(), len - 1);
            });
            search.watches.watch_clause(search.ca.view(cr), cr);

            self.occurs.remove_occ(&l.var(), cr);
            self.elim.bump_lit_occ(&l, -1);
            self.elim.update_elim_heap(l.var(), &self.var_status, &search.assigns);
            true
        }
    }

    fn eliminate_var(
        &mut self,
        search: &mut Searcher,
        budget: &Budget,
        elimclauses: &mut elim_clauses::ElimClauses,
        v: Var,
    ) -> bool {
        assert!({
            let ref st = self.var_status[&v];
            st.frozen == 0 && st.eliminated == 0
        });
        assert!(search.assigns.is_undef(v));

        // Split the occurrences into positive and negative:
        let cls = self.occurs.lookup(&v, &search.ca).clone();
        let mut pos = Vec::new();
        let mut neg = Vec::new();
        for &cr in cls.iter() {
            for l in search.ca.view(cr).lits() {
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

        // Check wether the increase in number of clauses stays within the allowed ('grow'). Moreover, no
        // clause must exceed the limit on the maximal clause size (if it is set):
        let mut cnt = 0;
        for &pr in pos.iter() {
            for &nr in neg.iter() {
                self.stats.merges += 1;
                if let Some(resolvent) = merge(v, search.ca.literals(pr), search.ca.literals(nr)) {
                    cnt += 1;
                    if cnt > cls.len() + self.settings.grow
                        || (self.settings.clause_lim != -1
                            && (resolvent.len() as i32) > self.settings.clause_lim)
                    {
                        return true;
                    }
                }
            }
        }

        // Delete and store old clauses:
        self.var_status[&v].eliminated = 1;
        search.heur.set_decision_var(v, false);
        self.stats.eliminated_vars += 1;

        if pos.len() > neg.len() {
            for &cr in neg.iter() {
                elimclauses.mk_elim_clause(v, search.ca.view(cr).lits());
            }
            elimclauses.mk_elim_unit(v.pos_lit());
        } else {
            for &cr in pos.iter() {
                elimclauses.mk_elim_clause(v, search.ca.view(cr).lits());
            }
            elimclauses.mk_elim_unit(v.neg_lit());
        }

        for &cr in cls.iter() {
            self.remove_clause(search, cr);
        }

        // Produce clauses in cross product:
        for &pr in pos.iter() {
            for &nr in neg.iter() {
                self.stats.merges += 1;
                if let Some(resolvent) = merge(v, search.ca.literals(pr), search.ca.literals(nr)) {
                    if !self.add_clause(search, &resolvent[..]) {
                        return false;
                    }
                }
            }
        }

        // Free occurs list for this variable:
        self.occurs.clear_var(&v);

        // Free watchers lists for this variable, if possible:
        search.watches.try_clear_var(v);

        self.backward_subsumption_check(search, budget, false)
    }

    // Backward subsumption + backward subsumption resolution
    fn backward_subsumption_check(
        &mut self,
        search: &mut Searcher,
        budget: &Budget,
        verbose: bool,
    ) -> bool {
        assert!(search.assigns.is_ground_level());

        if verbose {
            trace!(
                "BWD-SUB: queue = {}, trail = {}",
                self.subsumption_queue.len(),
                self.subsumption_queue.assigns_left(&search.assigns)
            );
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
                    for &cj in self.occurs.lookup(&unit.var(), &search.ca).clone().iter() {
                        if {
                            let c = search.ca.view(cj);
                            !c.is_deleted()
                                && (self.settings.subsumption_lim == -1
                                    || (c.len() as i32) < self.settings.subsumption_lim)
                        } {
                            match unit_subsumes(unit, search.ca.view(cj)) {
                                Subsumes::Different => {}

                                Subsumes::Exact => {
                                    subsumed += 1;
                                    self.remove_clause(search, cj);
                                }

                                Subsumes::LitSign(l) => {
                                    deleted_literals += 1;
                                    if !self.strengthen_clause(search, cj, !l) {
                                        return false;
                                    }
                                }
                            }
                        }
                    }
                }

                SubsumptionJob::Clause(cr) => {
                    let best = {
                        let c = search.ca.view(cr);
                        let mut best = c.head[0].var();
                        for &lit in &c.lits()[1..] {
                            // TODO: why not use n_occ?
                            if self.occurs.occs_dirty(lit.var()) < self.occurs.occs_dirty(best) {
                                best = lit.var();
                            }
                        }
                        best
                    };

                    for &cj in self.occurs.lookup(&best, &search.ca).clone().iter() {
                        if search.ca.is_deleted(cr) {
                            break;
                        }

                        if cj != cr && {
                            let c = search.ca.view(cj);
                            !c.is_deleted()
                                && (self.settings.subsumption_lim == -1
                                    || (c.len() as i32) < self.settings.subsumption_lim)
                        } {
                            match subsumes(search.ca.view(cr), search.ca.view(cj)) {
                                Subsumes::Different => {}

                                Subsumes::Exact => {
                                    subsumed += 1;
                                    self.remove_clause(search, cj);
                                }

                                Subsumes::LitSign(l) => {
                                    deleted_literals += 1;
                                    if !self.strengthen_clause(search, cj, !l) {
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

    fn gather_touched_clauses(&mut self, ca: &mut ClauseAllocator) {
        if self.n_touched == 0 {
            return;
        }

        self.subsumption_queue.remark_touched(ca, false);

        for (v, touched) in self.touched.iter_mut() {
            if *touched != 0 && self.var_status[&v].eliminated == 0 {
                for &cr in self.occurs.lookup(&v, ca) {
                    let c = ca.edit(cr);
                    if !c.is_touched() {
                        self.subsumption_queue.push(cr);
                        c.set_touched(true);
                    }
                }
                *touched = 0;
            }
        }

        self.subsumption_queue.remark_touched(ca, true);
        self.n_touched = 0;
    }

    fn garbage_collect(&mut self, search: &mut Searcher) {
        let mut to = ClauseAllocator::new_for_gc(&search.ca);
        self.reloc_gc(&mut search.ca, &mut to);
        search.reloc_gc(to);
    }

    fn reloc_gc(&mut self, from: &mut ClauseAllocator, to: &mut ClauseAllocator) {
        self.occurs.reloc_gc(from, to);
        self.subsumption_queue.reloc_gc(from, to);
    }

    // TODO: remove
    pub fn off(search: &mut Searcher) {
        search.db.settings.remove_satisfied = true;
        search.ca.set_extra_clause_field(false);

        // Force full cleanup (this is safe and desirable since it only happens once):
        search.heur.rebuild_order_heap(&search.assigns);
        search.garbage_collect();
    }

    pub fn on(search: &mut Searcher) {
        search.ca.set_extra_clause_field(true);
        search.db.settings.remove_satisfied = false;
    }
}


fn asymmetric_branching(search: &mut Searcher, v: Var, cr: ClauseRef) -> Option<Lit> {
    assert!(search.assigns.is_ground_level());

    let l = {
        let c = search.ca.view(cr);
        if c.is_deleted() || satisfied_with(c.lits(), &search.assigns) {
            return None;
        }

        search.assigns.new_decision_level();

        let mut vl = None;
        for &lit in c.lits() {
            if v == lit.var() {
                vl = Some(lit);
            } else if search.assigns.is_undef(lit.var()) {
                search.assigns.assign_lit(!lit, None);
            }
        }

        vl.unwrap()
    };

    let res = search.watches.propagate(&mut search.ca, &mut search.assigns);
    search.cancel_until(GROUND_LEVEL);
    res.map(|_| l)
}
