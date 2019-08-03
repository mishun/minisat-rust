use crate::sat;
use crate::sat::formula::{assignment::*, clause::*, LBool, Lit, LitMap, Var};
use self::backtrack::BacktrackableFormula;
use self::conflict::{AnalyzeContext, CCMinMode, Conflict};
use self::decision_heuristic::{DecisionHeuristic, DecisionHeuristicSettings};
use super::budget::Budget;

mod backtrack;
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


pub enum AddClauseRes {
    UnSAT,
    Consumed,
    Added(ClauseRef),
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


pub struct SearchCtx {
    stats: Stats,
    db: clause_db::ClauseDB,
    heur: DecisionHeuristic,
    analyze: AnalyzeContext,
    simp: SimplifyGuard,
}

impl SearchCtx {
    pub fn new(db_set: clause_db::ClauseDBSettings, heur_set: DecisionHeuristicSettings, ccmin_mode: CCMinMode) -> Self {
        SearchCtx {
            stats: Stats::default(),
            db: clause_db::ClauseDB::new(db_set),
            heur: DecisionHeuristic::new(heur_set),
            analyze: AnalyzeContext::new(ccmin_mode),
            simp: SimplifyGuard::new(),
        }
    }

    pub fn init_var(&mut self, v: Var, upol: Option<bool>, dvar: bool) {
        self.heur.init_var(v, upol, dvar);
        self.analyze.init_var(v);
    }

    pub fn decide(&mut self, assigns: &mut Assignment, ca: &ClauseAllocator, assumptions: &[Lit]) -> Result<Option<Lit>, LitMap<()>> {
        while let Some(&p) = assumptions.get(assigns.current_level().offset_from_ground()) {
            // Perform user provided assumption:
            match assigns.of_lit(p) {
                LBool::True => {
                    // Dummy decision level:
                    assigns.new_decision_level();
                }
                LBool::False => {
                    let conflict = self.analyze.analyze_final(ca, assigns, !p);
                    return Err(conflict);
                }
                LBool::Undef => {
                    return Ok(Some(p));
                }
            }
        }

        // New variable decision:
        self.stats.decisions += 1;
        Ok(self.heur.pick_branch_lit(assigns))
    }

    fn analyze(&mut self, assigns: &Assignment, ca: &mut ClauseAllocator, confl: ClauseRef) -> conflict::Conflict {
        self.analyze.analyze(assigns, ca,
            confl,
            {
                let heur = &mut self.heur;
                move |v| heur.bump_activity(&v)
            },
            {
                let db = &mut self.db;
                move |ca, c| db.bump_activity(ca, c)
            }
        )
    }

    fn cancel_until(&mut self, assigns: &Assignment, level: DecisionLevel) {
        let top_level = assigns.current_level();
        for (level, trail) in assigns.levels_above_rev(level) {
            for &lit in trail.iter().rev() {
                self.heur.cancel(lit, level == top_level);
            }
        }
    }

    fn handle_conflict(&mut self, learnt: &mut LearningGuard, bt: &mut BacktrackableFormula, confl: ClauseRef)
        -> Option<(DecisionLevel, Lit, Option<ClauseRef>)>
    {
        self.stats.conflicts += 1;

        let res =
            match self.analyze(&bt.assigns, &mut bt.ca, confl) {
                Conflict::Ground => {
                    return None;
                }

                Conflict::Unit(level, unit) => {
                    self.cancel_until(&bt.assigns, level);
                    (level, unit, None)
                }

                Conflict::Learned(level, lit, clause) => {
                    self.cancel_until(&bt.assigns, level);
                    let cr = self.db.learn_clause(&mut bt.ca, &clause[..]);
                    (level, lit, Some(cr))
                }
            };

        self.heur.decay_activity();
        self.db.decay_activity();

        if learnt.bump() {
            info!(
                "| {:9} | {:7} {:8} {:8} | {:8} {:8} {:6.0} | {:6.3} % |",
                self.stats.conflicts,
                self.heur.dec_vars - bt.assigns.number_of_ground_assigns(),
                self.db.stats.num_clauses,
                self.db.stats.clauses_literals,
                learnt.border() as u64,
                self.db.stats.num_learnts,
                (self.db.stats.learnts_literals as f64) / (self.db.stats.num_learnts as f64),
                progress_estimate(&bt.assigns) * 100.0
            );
        }

        Some(res)
    }
}


pub struct Searcher {
    settings: SearcherSettings,
    bt: backtrack::BacktrackableFormula,
    ctx: SearchCtx
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
            bt: backtrack::BacktrackableFormula::new(),
            ctx: SearchCtx::new(db_set, heur_set, ccmin_mode)
        }
    }

    pub fn number_of_vars(&self) -> usize {
        self.bt.assigns.number_of_vars()
    }

    pub fn number_of_clauses(&self) -> usize {
        self.ctx.db.stats.num_clauses
    }

    pub fn new_var(&mut self, upol: Option<bool>, dvar: bool) -> Var {
        let v = self.bt.new_var();
        self.ctx.init_var(v, upol, dvar);
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
            ps.retain(|&lit| !self.bt.assigns.is_assigned_neg(lit));

            {
                let mut prev = None;
                for &lit in ps.iter() {
                    if self.bt.assigns.is_assigned_pos(lit) || prev == Some(!lit) {
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
                self.bt.assigns.assign_lit(*unit, None);
                match self.bt.propagate() {
                    None => AddClauseRes::Consumed,
                    Some(_) => AddClauseRes::UnSAT,
                }
            }

            lits => {
                let cr = self.ctx.db.add_clause(&mut self.bt.ca, lits);
                self.bt.attach(cr);
                AddClauseRes::Added(cr)
            }
        }
    }

    pub fn preprocess(&mut self) -> bool {
        if let None = self.bt.propagate() {
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
        self.ctx.stats.solves += 1;
        let mut learnt = LearningGuard::new(ss.learn);
        learnt.reset(self.ctx.db.stats.num_clauses);

        let mut curr_restarts = 0;
        loop {
            let conflicts_to_go = ss.restart.conflicts_to_go(curr_restarts);
            match self.search_loop(conflicts_to_go, budget, &mut learnt, assumptions) {
                LoopRes::Restart => {
                    curr_restarts += 1;
                }

                LoopRes::SAT => {
                    let stats = self.stats();
                    return SearchRes::SAT(self.bt.assigns, stats);
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
        self.ctx.stats.starts += 1;

        let confl_limit = self.ctx.stats.conflicts + nof_conflicts;
        loop {
            if !self.propagate_learn_backtrack(learnt) {
                return LoopRes::UnSAT;
            }

            if !budget.within(self.ctx.stats.conflicts, self.bt.propagations()) {
                let progress_estimate = progress_estimate(&self.bt.assigns);
                self.cancel_until(GROUND_LEVEL);
                return LoopRes::Interrupted(progress_estimate);
            }

            if self.ctx.stats.conflicts >= confl_limit {
                self.cancel_until(GROUND_LEVEL);
                return LoopRes::Restart;
            }

            // Simplify the set of problem clauses:
            self.try_simplify();

            if (self.ctx.db.number_of_learnts() as f64) >= learnt.border() + (self.bt.assigns.number_of_assigns() as f64) {
                // Reduce the set of learnt clauses:
                {
                    let watches = &mut self.bt.watches;
                    self.ctx.db.reduce(&mut self.bt.ca, &self.bt.assigns, move |c| {
                        watches.unwatch_clause_lazy(c);
                    });
                }

                self.try_garbage_collect();
            }

            match self.ctx.decide(&mut self.bt.assigns, &self.bt.ca, assumptions) {
                Err(confl) => { return LoopRes::AssumpsConfl(confl) }
                Ok(None) => { return LoopRes::SAT } // Model found:
                Ok(Some(next)) => {
                    self.bt.push_decision(next);
                }
            }
        }
    }

    fn propagate_learn_backtrack(&mut self, learnt: &mut LearningGuard) -> bool {
        while let Some(confl) = self.bt.propagate() {
            match self.ctx.handle_conflict(learnt, &mut self.bt, confl) {
                None => { return false; }
                Some((level, lit, reason)) => {
                    self.bt.assigns.backtrack_to(level);
                    self.bt.assigns.assign_lit(lit, reason);
                    for &cr in reason.iter() {
                        self.bt.attach(cr);
                    }
                }
            }
        }
        true
    }

    // Description:
    //   Simplify the clause database according to the current top-level assigment. Currently, the only
    //   thing done here is the removal of satisfied clauses, but more things can be put here.
    fn try_simplify(&mut self) {
        if !self.bt.assigns.is_ground_level()
            || self.ctx.simp.skip(self.bt.assigns.number_of_assigns(), self.bt.propagations())
        {
            return;
        }

        {
            let watches = &mut self.bt.watches;
            self.ctx.db.remove_satisfied(&mut self.bt.ca, &self.bt.assigns, move |c| {
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

        self.try_garbage_collect();

        self.ctx.heur.rebuild_order_heap(&self.bt.assigns);
        self.ctx.simp.set_next(
            self.bt.assigns.number_of_assigns(),
            self.bt.propagations(),
            self.ctx.db.stats.clauses_literals + self.ctx.db.stats.learnts_literals,
        ); // (shouldn't depend on stats really, but it will do for now)
    }

    // Revert to the state at given level (keeping all assignment at 'level' but not beyond).
    fn cancel_until(&mut self, target_level: DecisionLevel) {
        self.ctx.cancel_until(&self.bt.assigns, target_level);
        self.bt.assigns.backtrack_to(target_level);
    }


    fn try_garbage_collect(&mut self) {
        if self.bt.ca.check_garbage(self.settings.garbage_frac) {
            self.garbage_collect();
        }
    }

    fn garbage_collect(&mut self) {
        // Initialize the next region to a size corresponding to the estimated utilization degree. This
        // is not precise but should avoid some unnecessary reallocations for the new region:
        let to = ClauseAllocator::new_for_gc(&self.bt.ca);
        self.reloc_gc(to);
    }

    fn reloc_gc(&mut self, mut to: ClauseAllocator) {
        self.bt.reloc_gc(&mut to);
        self.ctx.db.reloc_gc(&mut self.bt.ca, &mut to);

        debug!(
            "|  Garbage collection:   {:12} bytes => {:12} bytes             |",
            self.bt.ca.size(), to.size()
        );
        self.bt.ca = to;
    }


    pub fn stats(&self) -> sat::Stats {
        sat::Stats {
            solves: self.ctx.stats.solves,
            restarts: self.ctx.stats.starts,
            decisions: self.ctx.stats.decisions,
            rnd_decisions: self.ctx.heur.rnd_decisions,
            conflicts: self.ctx.stats.conflicts,
            propagations: self.bt.propagations(),
            tot_literals: self.ctx.analyze.tot_literals,
            del_literals: self.ctx.analyze.max_literals - self.ctx.analyze.tot_literals,
        }
    }
}


fn is_implied(search: &mut Searcher, c: &[Lit]) -> bool {
    assert!(search.bt.assigns.is_ground_level());

    search.bt.assigns.new_decision_level();
    for &lit in c.iter() {
        match search.bt.assigns.of_lit(lit) {
            LBool::True => {
                search.cancel_until(GROUND_LEVEL);
                return true;
            }
            LBool::Undef => {
                search.bt.assigns.assign_lit(!lit, None);
            }
            LBool::False => {}
        }
    }

    let result = search.bt.propagate().is_some();
    search.cancel_until(GROUND_LEVEL);
    return result;
}


fn progress_estimate(assigns: &Assignment) -> f64 {
    let vars = 1.0 / (assigns.number_of_vars() as f64);
    let mut progress = 0.0;
    let mut factor = vars;
    for (_, level_trail) in assigns.all_levels_dir() {
        progress += factor * (level_trail.len() as f64);
        factor *= vars;
    }
    progress
}
