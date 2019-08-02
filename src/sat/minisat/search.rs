use crate::sat;
use crate::sat::formula::{assignment::*, clause::*, LBool, Lit, LitMap, Var};
use self::conflict::{AnalyzeContext, CCMinMode, Conflict};
use self::decision_heuristic::{DecisionHeuristic, DecisionHeuristicSettings};
use super::budget::Budget;

pub mod conflict;
pub mod clause_db;
pub mod decision_heuristic;
mod luby;
pub mod simplify;
mod random;
mod watches;


#[derive(Clone, Copy, Debug)]
pub struct RestartStrategy {
    pub luby_restart: bool,
    pub restart_first: f64, // The initial restart limit.
    pub restart_inc: f64, // The factor with which the restart limit is multiplied in each restart.
}

impl Default for RestartStrategy {
    fn default() -> Self {
        RestartStrategy {
            luby_restart: true,
            restart_first: 100.0,
            restart_inc: 2.0,
        }
    }
}

impl RestartStrategy {
    pub fn conflicts_to_go(&self, restarts: u32) -> u64 {
        let rest_base = if self.luby_restart {
            luby::luby(self.restart_inc, restarts)
        } else {
            self.restart_inc.powi(restarts as i32)
        };

        (rest_base * self.restart_first) as u64
    }
}


#[derive(Clone, Copy, Debug)]
pub struct LearningStrategy {
    pub min_learnts_lim: i32, // Minimum number to set the learnts limit to.
    pub size_factor: f64, // The intitial limit for learnt clauses is a factor of the original clauses.
    pub size_inc: f64, // The limit for learnt clauses is multiplied with this factor each restart.
    pub size_adjust_start_confl: i32,
    pub size_adjust_inc: f64,
}

impl Default for LearningStrategy {
    fn default() -> Self {
        LearningStrategy {
            min_learnts_lim: 0,
            size_factor: 1.0 / 3.0,
            size_inc: 1.1,
            size_adjust_start_confl: 100,
            size_adjust_inc: 1.5,
        }
    }
}


struct LearningGuard {
    settings: LearningStrategy,
    max_learnts: f64,
    size_adjust_confl: f64,
    size_adjust_cnt: i32,
}

impl LearningGuard {
    pub fn new(settings: LearningStrategy) -> Self {
        LearningGuard {
            settings,
            max_learnts: 0.0,
            size_adjust_confl: 0.0,
            size_adjust_cnt: 0,
        }
    }

    pub fn reset(&mut self, clauses: usize) {
        self.max_learnts = ((clauses as f64) * self.settings.size_factor)
            .max(self.settings.min_learnts_lim as f64);
        self.size_adjust_confl = self.settings.size_adjust_start_confl as f64;
        self.size_adjust_cnt = self.settings.size_adjust_start_confl;
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

    pub fn border(&self) -> f64 {
        self.max_learnts
    }
}


struct SimplifyGuard {
    simp_db_assigns: Option<usize>, // Number of top-level assignments since last execution of 'simplify()'.
    simp_db_props: u64,
}

impl SimplifyGuard {
    pub fn new() -> Self {
        SimplifyGuard {
            simp_db_assigns: None,
            simp_db_props: 0,
        }
    }

    pub fn skip(&self, assigns: usize, propagations: u64) -> bool {
        Some(assigns) == self.simp_db_assigns || propagations < self.simp_db_props
    }

    pub fn set_next(&mut self, assigns: usize, propagations: u64, prop_limit: u64) {
        self.simp_db_assigns = Some(assigns);
        self.simp_db_props = propagations + prop_limit;
    }
}


#[derive(Default)]
struct Stats {
    solves: u64,
    starts: u64,
    decisions: u64,
    conflicts: u64,
}


#[derive(Clone, Copy, Default, Debug)]
pub struct SearchSettings {
    pub restart: RestartStrategy,
    pub learn: LearningStrategy,
}


pub enum AddClauseRes<'c> {
    UnSAT,
    Consumed,
    Added(&'c Clause, ClauseRef),
}


pub enum SearchRes {
    UnSAT(sat::Stats),
    SAT(Assignment, sat::Stats),
    Interrupted(f64, Searcher),
}


pub struct SearcherSettings {
    pub garbage_frac: f64, // The fraction of wasted memory allowed before a garbage collection is triggered.
    pub use_rcheck: bool, // Check if a clause is already implied. Prett costly, and subsumes subsumptions :)
}

impl Default for SearcherSettings {
    fn default() -> Self {
        SearcherSettings {
            garbage_frac: 0.20,
            use_rcheck: false,
        }
    }
}


enum LoopRes {
    Restart,
    UnSAT,
    SAT,
    Interrupted(f64),
    AssumpsConfl(LitMap<()>),
}


pub struct Searcher {
    settings: SearcherSettings,
    stats: Stats,
    ca: ClauseAllocator,
    db: clause_db::ClauseDB,
    assigns: Assignment,       // The current assignments.
    watches: watches::Watches, // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    heur: DecisionHeuristic,
    analyze: AnalyzeContext,
    simp: SimplifyGuard,
}

impl Searcher {
    pub fn new(
        settings: SearcherSettings,
        db_set: clause_db::ClauseDBSettings,
        heur_set: DecisionHeuristicSettings,
        ccmin_mode: CCMinMode,
    ) -> Self {
        Searcher {
            settings,
            stats: Stats::default(),
            ca: ClauseAllocator::new_empty(),
            db: clause_db::ClauseDB::new(db_set),
            assigns: Assignment::new(),
            watches: watches::Watches::new(),
            heur: DecisionHeuristic::new(heur_set),
            analyze: AnalyzeContext::new(ccmin_mode),
            simp: SimplifyGuard::new(),
        }
    }

    pub fn number_of_vars(&self) -> usize {
        self.assigns.number_of_vars()
    }

    pub fn number_of_clauses(&self) -> usize {
        self.db.stats.num_clauses
    }

    pub fn new_var(&mut self, upol: Option<bool>, dvar: bool) -> Var {
        let v = self.assigns.new_var();
        self.watches.init_var(v);
        self.heur.init_var(v, upol, dvar);
        self.analyze.init_var(v);
        v
    }

    pub fn add_clause(&mut self, clause: &[Lit]) -> AddClauseRes {
        // TODO: it should be here to work identical to original MiniSat. Probably not the best place.
        if self.settings.use_rcheck && is_implied(self, &clause) {
            return AddClauseRes::Consumed;
        }

        let ps = {
            let mut ps = clause.to_vec();

            // Check if clause is satisfied and remove false/duplicate literals:
            ps.sort();
            ps.dedup();
            ps.retain(|&lit| !self.assigns.is_assigned_neg(lit));

            {
                let mut prev = None;
                for &lit in ps.iter() {
                    if self.assigns.is_assigned_pos(lit) || prev == Some(!lit) {
                        return AddClauseRes::Consumed;
                    }
                    prev = Some(lit);
                }
            }

            ps
        };

        match &ps[..] {
            [] => { AddClauseRes::UnSAT }

            [unit] => {
                self.assigns.assign_lit(*unit, None);
                match self.watches.propagate(&mut self.ca, &mut self.assigns) {
                    None => AddClauseRes::Consumed,
                    Some(_) => AddClauseRes::UnSAT,
                }
            }

            lits => {
                let (c, cr) = self.db.add_clause(&mut self.ca, lits);
                self.watches.watch_clause(c, cr);
                AddClauseRes::Added(c, cr)
            }
        }
    }

    pub fn preprocess(&mut self) -> bool {
        if let None = self.watches.propagate(&mut self.ca, &mut self.assigns) {
            self.try_simplify();
            true
        } else {
            false
        }
    }

    pub fn search(self, ss: &SearchSettings, budget: &Budget, assumptions: &[Lit]) -> SearchRes {
        info!("============================[ Search Statistics ]==============================");
        info!("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |");
        info!("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |");
        info!("===============================================================================");

        let res = self.search_internal(ss, budget, assumptions);

        info!("===============================================================================");
        res
    }

    fn search_internal(mut self, ss: &SearchSettings, budget: &Budget, assumptions: &[Lit]) -> SearchRes {
        self.stats.solves += 1;
        let mut learnt = LearningGuard::new(ss.learn);
        learnt.reset(self.db.stats.num_clauses);

        let mut curr_restarts = 0;
        loop {
            let conflicts_to_go = ss.restart.conflicts_to_go(curr_restarts);
            match self.search_loop(conflicts_to_go, budget, &mut learnt, assumptions) {
                LoopRes::Restart => {
                    curr_restarts += 1;
                }

                LoopRes::SAT => {
                    let stats = self.stats();
                    return SearchRes::SAT(self.assigns, stats);
                }

                LoopRes::UnSAT => {
                    return SearchRes::UnSAT(self.stats());
                }

                LoopRes::AssumpsConfl(_) => {
                    // TODO: implement properly
                    self.cancel_until(GROUND_LEVEL);
                    return SearchRes::UnSAT(self.stats());
                }

                LoopRes::Interrupted(c) => {
                    self.cancel_until(GROUND_LEVEL);
                    return SearchRes::Interrupted(c, self);
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
    fn search_loop(
        &mut self,
        nof_conflicts: u64,
        budget: &Budget,
        learnt: &mut LearningGuard,
        assumptions: &[Lit],
    ) -> LoopRes {
        self.stats.starts += 1;

        let confl_limit = self.stats.conflicts + nof_conflicts;
        loop {
            if !self.propagate_learn_backtrack(learnt) {
                return LoopRes::UnSAT;
            }

            if !budget.within(self.stats.conflicts, self.watches.propagations) {
                let progress_estimate = progress_estimate(&self.assigns);
                self.cancel_until(GROUND_LEVEL);
                return LoopRes::Interrupted(progress_estimate);
            }

            if self.stats.conflicts >= confl_limit {
                self.cancel_until(GROUND_LEVEL);
                return LoopRes::Restart;
            }

            // Simplify the set of problem clauses:
            self.try_simplify();

            if (self.db.learnts() as f64) >= learnt.border() + (self.assigns.number_of_assigns() as f64)
            {
                // Reduce the set of learnt clauses:
                {
                    let watches = &mut self.watches;
                    self.db.reduce(&mut self.ca, &mut self.assigns, move |c| {
                        watches.unwatch_clause_lazy(c);
                    });
                }

                if self.ca.check_garbage(self.settings.garbage_frac) {
                    self.garbage_collect();
                }
            }

            match self.decide(assumptions) {
                Err(confl) => { return LoopRes::AssumpsConfl(confl) }
                Ok(None) => { return LoopRes::SAT } // Model found:
                Ok(Some(next)) => {
                    // Increase decision level and enqueue 'next'
                    self.assigns.new_decision_level();
                    self.assigns.assign_lit(next, None);
                }
            }
        }
    }

    fn decide(&mut self, assumptions: &[Lit]) -> Result<Option<Lit>, LitMap<()>> {
        while self.assigns.decision_level().offset() < assumptions.len() {
            // Perform user provided assumption:
            let p = assumptions[ self.assigns.decision_level().offset() ];
            match self.assigns.of_lit(p) {
                LBool::True => {
                    // Dummy decision level:
                    self.assigns.new_decision_level();
                }
                LBool::False => {
                    let conflict = self.analyze.analyze_final(&self.ca, &self.assigns, !p);
                    return Err(conflict);
                }
                LBool::Undef => {
                    return Ok(Some(p));
                }
            }
        }

        // New variable decision:
        self.stats.decisions += 1;
        Ok(self.heur.pick_branch_lit(&self.assigns))
    }

    fn propagate_learn_backtrack(&mut self, learnt: &mut LearningGuard) -> bool {
        while let Some(confl) = self.watches.propagate(&mut self.ca, &mut self.assigns) {
            self.stats.conflicts += 1;

            match self.analyze.analyze(
                &self.assigns,
                &mut self.ca,
                confl,
                {
                    let heur = &mut self.heur;
                    move |v| heur.bump_activity(&v)
                },
                {
                    let db = &mut self.db;
                    move |ca, c| db.bump_activity(ca, c)
                },
            ) {
                Conflict::Ground => {
                    return false;
                }

                Conflict::Unit(level, unit) => {
                    self.cancel_until(level);
                    self.assigns.assign_lit(unit, None);
                }

                Conflict::Learned(level, lit, clause) => {
                    self.cancel_until(level);
                    let (c, cr) = self.db.learn_clause(&mut self.ca, &clause[..]);
                    self.watches.watch_clause(c, cr);
                    self.assigns.assign_lit(lit, Some(cr));
                }
            }

            self.heur.decay_activity();
            self.db.decay_activity();

            if learnt.bump() {
                info!(
                    "| {:9} | {:7} {:8} {:8} | {:8} {:8} {:6.0} | {:6.3} % |",
                    self.stats.conflicts,
                    self.heur.dec_vars - self.assigns.number_of_ground_assigns(),
                    self.db.stats.num_clauses,
                    self.db.stats.clauses_literals,
                    learnt.border() as u64,
                    self.db.stats.num_learnts,
                    (self.db.stats.learnts_literals as f64) / (self.db.stats.num_learnts as f64),
                    progress_estimate(&self.assigns) * 100.0
                );
            }
        }

        true
    }

    // Description:
    //   Simplify the clause database according to the current top-level assigment. Currently, the only
    //   thing done here is the removal of satisfied clauses, but more things can be put here.
    fn try_simplify(&mut self) {
        if !self.assigns.is_ground_level()
            || self.simp.skip(self.assigns.number_of_assigns(), self.watches.propagations)
        {
            return;
        }

        {
            let watches = &mut self.watches;
            self.db
                .remove_satisfied(&mut self.ca, &mut self.assigns, move |c| {
                    watches.unwatch_clause_lazy(c);
                });
        }

        //        // TODO: why if?
        //        if self.db.settings.remove_satisfied {
        //            // Remove all released variables from the trail:
        //            for v in self.released_vars.iter() {
        //                assert!(self.analyze.seen[v] == Seen::Undef);
        //                self.analyze.seen[v] = Seen::Source;
        //            }
        //
        //            {
        //                let seen = &self.analyze.seen;
        //                self.assigns.retain_assignments(|l| { seen[&l.var()] == Seen::Undef });
        //            }
        //
        //            for v in self.released_vars.iter() {
        //                self.analyze.seen[v] = Seen::Undef;
        //            }
        //
        //            // Released variables are now ready to be reused:
        //            for &v in self.released_vars.iter() {
        //                self.assigns.free_var(v);
        //            }
        //            self.released_vars.clear();
        //        }

        if self.ca.check_garbage(self.settings.garbage_frac) {
            self.garbage_collect();
        }

        self.heur.rebuild_order_heap(&self.assigns);
        self.simp.set_next(
            self.assigns.number_of_assigns(),
            self.watches.propagations,
            self.db.stats.clauses_literals + self.db.stats.learnts_literals,
        ); // (shouldn't depend on stats really, but it will do for now)
    }

    // Revert to the state at given level (keeping all assignment at 'level' but not beyond).
    fn cancel_until(&mut self, target_level: DecisionLevel) {
        let ref mut heur = self.heur;
        let top_level = self.assigns.decision_level();
        self.assigns.rewind_until_level(target_level, |level, lit| {
            heur.cancel(lit, level == top_level);
        });
    }

    fn garbage_collect(&mut self) {
        // Initialize the next region to a size corresponding to the estimated utilization degree. This
        // is not precise but should avoid some unnecessary reallocations for the new region:

        let to = ClauseAllocator::new_for_gc(&self.ca);
        self.reloc_gc(to);
    }

    fn reloc_gc(&mut self, mut to: ClauseAllocator) {
        self.watches.reloc_gc(&mut self.ca, &mut to);
        self.assigns.reloc_gc(&mut self.ca, &mut to);
        self.db.reloc_gc(&mut self.ca, &mut to);

        debug!(
            "|  Garbage collection:   {:12} bytes => {:12} bytes             |",
            self.ca.size(),
            to.size()
        );
        self.ca = to;
    }

    pub fn stats(&self) -> sat::Stats {
        sat::Stats {
            solves: self.stats.solves,
            restarts: self.stats.starts,
            decisions: self.stats.decisions,
            rnd_decisions: self.heur.rnd_decisions,
            conflicts: self.stats.conflicts,
            propagations: self.watches.propagations,
            tot_literals: self.analyze.tot_literals,
            del_literals: self.analyze.max_literals - self.analyze.tot_literals,
        }
    }
}


fn is_implied(search: &mut Searcher, c: &[Lit]) -> bool {
    assert!(search.assigns.is_ground_level());

    search.assigns.new_decision_level();
    for &lit in c.iter() {
        match search.assigns.of_lit(lit) {
            LBool::True => {
                search.cancel_until(GROUND_LEVEL);
                return true;
            }
            LBool::Undef => {
                search.assigns.assign_lit(!lit, None);
            }
            LBool::False => {}
        }
    }

    let result = search.watches.propagate(&mut search.ca, &mut search.assigns).is_some();
    search.cancel_until(GROUND_LEVEL);
    return result;
}
