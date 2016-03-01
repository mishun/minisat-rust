use sat;
use sat::formula::{Var, Lit, LitMap};
use sat::formula::clause::*;
use sat::formula::assignment::*;
use self::conflict::{AnalyzeContext, Conflict, CCMinMode};
use self::decision_heuristic::{DecisionHeuristicSettings, DecisionHeuristic};
use super::budget;

pub mod conflict;
pub mod clause_db;
pub mod decision_heuristic;
pub mod simplify;
mod util;
mod watches;


#[derive(Clone, Copy, Debug)]
pub struct RestartStrategy {
    pub luby_restart  : bool,
    pub restart_first : f64,   // The initial restart limit.
    pub restart_inc   : f64    // The factor with which the restart limit is multiplied in each restart.
}

impl Default for RestartStrategy {
    fn default() -> Self {
        RestartStrategy { luby_restart  : true
                        , restart_first : 100.0
                        , restart_inc   : 2.0
                        }
    }
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


#[derive(Clone, Copy, Debug)]
pub struct LearningStrategy {
    pub min_learnts_lim         : i32,  // Minimum number to set the learnts limit to.
    pub size_factor             : f64,  // The intitial limit for learnt clauses is a factor of the original clauses.
    pub size_inc                : f64,  // The limit for learnt clauses is multiplied with this factor each restart.
    pub size_adjust_start_confl : i32,
    pub size_adjust_inc         : f64
}

impl Default for LearningStrategy {
    fn default() -> Self {
        LearningStrategy { min_learnts_lim         : 0
                         , size_factor             : 1.0 / 3.0
                         , size_inc                : 1.1
                         , size_adjust_start_confl : 100
                         , size_adjust_inc         : 1.5
                         }
    }
}


struct LearningGuard {
    settings          : LearningStrategy,
    max_learnts       : f64,
    size_adjust_confl : f64,
    size_adjust_cnt   : i32
}

impl LearningGuard {
    pub fn new(settings : LearningStrategy) -> Self {
        LearningGuard { settings          : settings
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

    pub fn border(&self) -> f64 {
        self.max_learnts
    }
}


struct SimplifyGuard {
    simpDB_assigns : Option<usize>, // Number of top-level assignments since last execution of 'simplify()'.
    simpDB_props   : u64
}

impl SimplifyGuard {
    pub fn new() -> Self {
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


#[derive(Default)]
struct Stats {
    solves    : u64,
    starts    : u64,
    decisions : u64,
    conflicts : u64
}


#[derive(Clone, Copy, Default, Debug)]
pub struct SearchSettings {
    pub restart : RestartStrategy,
    pub learn   : LearningStrategy
}


pub enum AddClauseRes<'c> {
    UnSAT,
    Consumed,
    Added(&'c Clause, ClauseRef)
}


pub enum SearchRes {
    UnSAT(sat::Stats),
    SAT(Assignment, sat::Stats),
    Interrupted(Searcher, f64, sat::Stats)
}


pub struct SearcherSettings {
    pub garbage_frac : f64,  // The fraction of wasted memory allowed before a garbage collection is triggered.
    pub use_rcheck   : bool, // Check if a clause is already implied. Prett costly, and subsumes subsumptions :)
}

impl Default for SearcherSettings {
    fn default() -> Self {
        SearcherSettings { garbage_frac : 0.20
                         , use_rcheck   : false
                         }
    }
}


enum LoopRes {
    Restart,
    UnSAT,
    SAT,
    Interrupted(f64),
    AssumpsConfl(LitMap<()>)
}


pub struct Searcher {
    settings : SearcherSettings,
    stats    : Stats,
    db       : clause_db::ClauseDB,
    assigns  : Assignment,             // The current assignments.
    watches  : watches::Watches,       // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    heur     : DecisionHeuristic,
    analyze  : AnalyzeContext,
    simp     : SimplifyGuard,
}

impl Searcher {
    pub fn new(settings : SearcherSettings, db_set : clause_db::ClauseDBSettings, heur_set : DecisionHeuristicSettings, ccmin_mode : CCMinMode) -> Self {
        Searcher { settings : settings
                 , stats    : Stats::default()
                 , db       : clause_db::ClauseDB::new(db_set)
                 , assigns  : Assignment::new()
                 , watches  : watches::Watches::new()
                 , heur     : DecisionHeuristic::new(heur_set)
                 , analyze  : AnalyzeContext::new(ccmin_mode)
                 , simp     : SimplifyGuard::new()
                 }
    }

    pub fn numberOfVars(&self) -> usize {
        self.assigns.numberOfVars()
    }

    pub fn numberOfClauses(&self) -> usize {
        self.db.stats.num_clauses
    }

    pub fn newVar(&mut self, upol : Option<bool>, dvar : bool) -> Var {
        let v = self.assigns.newVar();
        self.watches.initVar(v);
        self.heur.initVar(v, upol, dvar);
        self.analyze.initVar(v);
        v
    }

    pub fn addClause(&mut self, clause : &[Lit]) -> AddClauseRes {
        // TODO: it should be here to work identical to original MiniSat. Probably not the best place.
        if self.settings.use_rcheck && isImplied(self, &clause) {
            return AddClauseRes::Consumed;
        }

        let ps = {
            let mut ps = clause.to_vec();

            // Check if clause is satisfied and remove false/duplicate literals:
            ps.sort();
            ps.dedup();
            ps.retain(|&lit| { !self.assigns.isUnsat(lit) });

            {
                let mut prev = None;
                for &lit in ps.iter() {
                    if self.assigns.isSat(lit) || prev == Some(!lit) {
                        return AddClauseRes::Consumed;
                    }
                    prev = Some(lit);
                }
            }

            ps.into_boxed_slice()
        };

        match ps.len() {
            0 => { AddClauseRes::UnSAT }

            1 => {
                self.assigns.assignLit(ps[0], None);
                match self.watches.propagate(&mut self.db.ca, &mut self.assigns) {
                    None    => { AddClauseRes::Consumed }
                    Some(_) => { AddClauseRes::UnSAT }
                }
            }

            _ => {
                let (c, cr) = self.db.addClause(ps);
                self.watches.watchClause(c, cr);
                AddClauseRes::Added(c, cr)
            }
        }
    }

    pub fn preprocess(&mut self) -> bool {
        if let None = self.watches.propagate(&mut self.db.ca, &mut self.assigns) {
            self.simplify();
            true
        } else {
            false
        }
    }

    pub fn search(mut self, ss : &SearchSettings, budget : &budget::Budget, assumptions : &[Lit]) -> SearchRes {
        info!("============================[ Search Statistics ]==============================");
        info!("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |");
        info!("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |");
        info!("===============================================================================");

        self.stats.solves += 1;
        let mut learnt = LearningGuard::new(ss.learn);
        learnt.reset(self.db.stats.num_clauses);

        let mut curr_restarts = 0;
        loop {
            let conflicts_to_go = ss.restart.conflictsToGo(curr_restarts);
            match self.searchLoop(conflicts_to_go, budget, &mut learnt, assumptions) {
                LoopRes::Restart         => {
                    curr_restarts += 1;
                }

                LoopRes::SAT             => {
                    info!("===============================================================================");
                    let stats = self.stats();
                    return SearchRes::SAT(self.assigns, stats);
                }

                LoopRes::UnSAT           => {
                    info!("===============================================================================");
                    return SearchRes::UnSAT(self.stats());
                }

                LoopRes::AssumpsConfl(_) => { // TODO: implement properly
                    //self.cancelUntil(GroundLevel);
                    info!("===============================================================================");
                    return SearchRes::UnSAT(self.stats());
                }

                LoopRes::Interrupted(c)  => {
                    self.cancelUntil(GroundLevel);
                    info!("===============================================================================");
                    let stats = self.stats();
                    return SearchRes::Interrupted(self, c, stats);
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
    fn searchLoop(&mut self, nof_conflicts : u64, budget : &budget::Budget, learnt : &mut LearningGuard, assumptions : &[Lit]) -> LoopRes {
        self.stats.starts += 1;

        let confl_limit = self.stats.conflicts + nof_conflicts;
        loop {
            if !self.propagateLearnBacktrack(learnt) {
                return LoopRes::UnSAT;
            }

            if !budget.within(self.stats.conflicts, self.watches.propagations) {
                let progress_estimate = progressEstimate(&self.assigns);
                self.cancelUntil(GroundLevel);
                return LoopRes::Interrupted(progress_estimate);
            }

            if self.stats.conflicts >= confl_limit {
                self.cancelUntil(GroundLevel);
                return LoopRes::Restart;
            }

            // Simplify the set of problem clauses:
            self.simplify();

            if (self.db.learnts() as f64) >= learnt.border() + (self.assigns.numberOfAssigns() as f64) {
                // Reduce the set of learnt clauses:
                {
                    let watches = &mut self.watches;
                    self.db.reduce(&mut self.assigns, move |c| { watches.unwatchClauseLazy(c); });
                }

                if self.db.ca.checkGarbage(self.settings.garbage_frac) {
                    self.garbageCollect();
                }
            }

            let next = {
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
                            return LoopRes::AssumpsConfl(conflict);
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
                        None    => { return LoopRes::SAT; } // Model found:
                    };
                }

                next.unwrap()
            };

            // Increase decision level and enqueue 'next'
            self.assigns.newDecisionLevel();
            self.assigns.assignLit(next, None);
        }
    }

    fn propagateLearnBacktrack(&mut self, learnt : &mut LearningGuard) -> bool {
        while let Some(confl) = self.watches.propagate(&mut self.db.ca, &mut self.assigns) {
            self.stats.conflicts += 1;

            match self.analyze.analyze(&mut self.db, &mut self.heur, &self.assigns, confl) {
                Conflict::Ground => { return false; }

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

            if learnt.bump() {
                info!("| {:9} | {:7} {:8} {:8} | {:8} {:8} {:6.0} | {:6.3} % |",
                        self.stats.conflicts,
                        self.heur.dec_vars - self.assigns.numberOfGroundAssigns(),
                        self.db.stats.num_clauses,
                        self.db.stats.clauses_literals,
                        learnt.border() as u64,
                        self.db.stats.num_learnts,
                        (self.db.stats.learnts_literals as f64) / (self.db.stats.num_learnts as f64),
                        progressEstimate(&self.assigns) * 100.0
                );
            }
        }

        true
    }

    // Description:
    //   Simplify the clause database according to the current top-level assigment. Currently, the only
    //   thing done here is the removal of satisfied clauses, but more things can be put here.
    fn simplify(&mut self) {
        if !self.assigns.isGroundLevel() || self.simp.skip(self.assigns.numberOfAssigns(), self.watches.propagations) {
            return;
        }

        {
            let watches = &mut self.watches;
            self.db.removeSatisfied(&mut self.assigns, move |c| { watches.unwatchClauseLazy(c); });
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
//                self.assigns.retainAssignments(|l| { seen[&l.var()] == Seen::Undef });
//            }
//
//            for v in self.released_vars.iter() {
//                self.analyze.seen[v] = Seen::Undef;
//            }
//
//            // Released variables are now ready to be reused:
//            for &v in self.released_vars.iter() {
//                self.assigns.freeVar(v);
//            }
//            self.released_vars.clear();
//        }

        if self.db.ca.checkGarbage(self.settings.garbage_frac) {
            self.garbageCollect();
        }

        self.heur.rebuildOrderHeap(&self.assigns);
        self.simp.setNext(self.assigns.numberOfAssigns(), self.watches.propagations, self.db.stats.clauses_literals + self.db.stats.learnts_literals); // (shouldn't depend on stats really, but it will do for now)
    }

    // Revert to the state at given level (keeping all assignment at 'level' but not beyond).
    fn cancelUntil(&mut self, target_level : DecisionLevel) {
        let ref mut heur = self.heur;
        let top_level = self.assigns.decisionLevel();
        self.assigns.rewindUntilLevel(target_level, |level, lit| { heur.cancel(lit, level == top_level); });
    }

    fn garbageCollect(&mut self) {
        // Initialize the next region to a size corresponding to the estimated utilization degree. This
        // is not precise but should avoid some unnecessary reallocations for the new region:

        let to = ClauseAllocator::newForGC(&self.db.ca);
        self.relocGC(to);
    }

    fn relocGC(&mut self, mut to : ClauseAllocator) {
        self.watches.relocGC(&mut self.db.ca, &mut to);
        self.assigns.relocGC(&mut self.db.ca, &mut to);
        self.db.relocGC(to);
    }

    pub fn stats(&self) -> sat::Stats {
        sat::Stats { solves        : self.stats.solves
                   , restarts      : self.stats.starts
                   , decisions     : self.stats.decisions
                   , rnd_decisions : self.heur.rnd_decisions
                   , conflicts     : self.stats.conflicts
                   , propagations  : self.watches.propagations
                   , tot_literals  : self.analyze.tot_literals
                   , del_literals  : self.analyze.max_literals - self.analyze.tot_literals
                   }
    }
}


fn isImplied(search : &mut Searcher, c : &[Lit]) -> bool {
    assert!(search.assigns.isGroundLevel());

    search.assigns.newDecisionLevel();
    for &lit in c.iter() {
        match search.assigns.ofLit(lit) {
            LitVal::True  => { search.cancelUntil(GroundLevel); return true; }
            LitVal::Undef => { search.assigns.assignLit(!lit, None); }
            LitVal::False => {}
        }
    }

    let result = search.watches.propagate(&mut search.db.ca, &mut search.assigns).is_some();
    search.cancelUntil(GroundLevel);
    return result;
}
