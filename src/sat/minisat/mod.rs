use sat::{SolveRes, Solver, Stats};
use sat::formula::{Lit, Var};
use sat::formula::assignment::*;
use self::search::clause_db::ClauseDBSettings;
pub use self::search::conflict::CCMinMode;
use self::search::decision_heuristic::DecisionHeuristicSettings;
pub use self::search::decision_heuristic::PhaseSaving;
use self::search::*;
use self::search::simplify::elim_clauses::*;
use self::search::simplify::*;
use self::budget::Budget;

pub mod budget;
mod search;


#[derive(Default)]
pub struct CoreSettings {
    pub heur: DecisionHeuristicSettings,
    pub db: ClauseDBSettings,
    pub ccmin_mode: CCMinMode,
    pub search: SearchSettings,
    pub core: SearcherSettings,
}


pub struct CoreSolver {
    ok: bool, // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    ss: SearchSettings,
    search: Searcher,
}

impl Solver for CoreSolver {
    fn nVars(&self) -> usize {
        self.search.numberOfVars()
    }

    fn nClauses(&self) -> usize {
        self.search.numberOfClauses()
    }

    fn newVar(&mut self, upol: Option<bool>, dvar: bool) -> Var {
        self.search.newVar(upol, dvar)
    }

    fn addClause(&mut self, clause: &[Lit]) -> bool {
        if self.ok {
            if let AddClauseRes::UnSAT = self.search.addClause(clause) {
                self.ok = false;
            }
        }
        self.ok
    }

    fn preprocess(&mut self, _: &Budget) -> bool {
        if self.ok {
            self.ok = self.search.preprocess();
        }
        self.ok
    }

    fn solveLimited(self, budget: &Budget, assumptions: &[Lit]) -> SolveRes<Self> {
        if self.ok {
            match self.search.search(&self.ss, budget, assumptions) {
                SearchRes::UnSAT(stats) => SolveRes::UnSAT(stats),
                SearchRes::SAT(assigns, stats) => SolveRes::SAT(extractModel(&assigns), stats),
                SearchRes::Interrupted(c, s) => SolveRes::Interrupted(
                    c,
                    CoreSolver {
                        ok: true,
                        ss: self.ss,
                        search: s,
                    },
                ),
            }
        } else {
            SolveRes::UnSAT(self.search.stats())
        }
    }

    fn stats(&self) -> Stats {
        self.search.stats()
    }
}

impl CoreSolver {
    pub fn new(settings: CoreSettings) -> Self {
        CoreSolver {
            ok: true,
            ss: settings.search,
            search: Searcher::new(
                settings.core,
                settings.db,
                settings.heur,
                settings.ccmin_mode,
            ),
        }
    }
}


pub struct SimpSettings {
    pub core: CoreSettings,
    pub simp: SimplificatorSettings,
    pub extend_model: bool, // Flag to indicate whether the user needs to look at the full model.
}

impl Default for SimpSettings {
    fn default() -> Self {
        SimpSettings {
            core: Default::default(),
            simp: Default::default(),
            extend_model: true,
        }
    }
}


pub struct SimpSolver {
    core: CoreSolver,
    elimclauses: ElimClauses,
    simp: Option<Simplificator>,
}

impl Solver for SimpSolver {
    fn nVars(&self) -> usize {
        self.core.nVars()
    }

    fn nClauses(&self) -> usize {
        self.core.nClauses()
    }

    fn newVar(&mut self, upol: Option<bool>, dvar: bool) -> Var {
        let v = self.core.newVar(upol, dvar);
        if let Some(ref mut simp) = self.simp {
            simp.initVar(v);
        }
        v
    }

    fn addClause(&mut self, ps: &[Lit]) -> bool {
        match self.simp {
            None => self.core.addClause(ps),
            Some(ref mut simp) => {
                let res = simp.addClause(&mut self.core.search, ps);
                if !res {
                    self.core.ok = false;
                }
                res
            }
        }
    }

    fn preprocess(&mut self, budget: &Budget) -> bool {
        if !self.core.preprocess(budget) {
            return false;
        }

        let turn_off_elim = true;
        let result = if let Some(ref mut simp) = self.simp {
            let result = simp.eliminate(&mut self.core.search, budget, &mut self.elimclauses);
            if !result {
                self.core.ok = false;
            }
            // TODO:
            //                if !turn_off_elim && self.core.search.db.ca.checkGarbage(self.core.search.settings.garbage_frac) {
            //                    simp.garbageCollect(&mut self.core.search);
            //                }
            result
        } else {
            return true;
        };

        if turn_off_elim {
            self.simpOff();
        }

        self.elimclauses.logSize();
        result
    }

    fn solveLimited(mut self, budget: &Budget, assumptions: &[Lit]) -> SolveRes<Self> {
        match self.simp {
            Some(mut simp) => {
                match simp.solveLimited(
                    self.core.search,
                    &self.core.ss,
                    budget,
                    &mut self.elimclauses,
                    assumptions,
                ) {
                    SearchRes::UnSAT(stats) => SolveRes::UnSAT(stats),

                    SearchRes::SAT(mut assigns, stats) => {
                        self.elimclauses.extend(&mut assigns);
                        SolveRes::SAT(extractModel(&assigns), stats)
                    }

                    SearchRes::Interrupted(c, s) => {
                        // TODO:
                        //        if turn_off_simp {
                        //            self.simpOff();
                        //        }
                        SolveRes::Interrupted(
                            c,
                            SimpSolver {
                                core: CoreSolver {
                                    ok: true,
                                    ss: self.core.ss,
                                    search: s,
                                },
                                elimclauses: self.elimclauses,
                                simp: Some(simp),
                            },
                        )
                    }
                }
            }

            _ => match self.core.search.search(&self.core.ss, budget, assumptions) {
                SearchRes::UnSAT(stats) => SolveRes::UnSAT(stats),

                SearchRes::SAT(mut assigns, stats) => {
                    self.elimclauses.extend(&mut assigns);
                    SolveRes::SAT(extractModel(&assigns), stats)
                }

                SearchRes::Interrupted(c, s) => SolveRes::Interrupted(
                    c,
                    SimpSolver {
                        core: CoreSolver {
                            ok: true,
                            ss: self.core.ss,
                            search: s,
                        },
                        elimclauses: self.elimclauses,
                        simp: None,
                    },
                ),
            },
        }
    }

    fn stats(&self) -> Stats {
        self.core.search.stats()
    }
}

impl SimpSolver {
    pub fn new(settings: SimpSettings) -> Self {
        let mut core = CoreSolver::new(settings.core);
        Simplificator::on(&mut core.search);
        SimpSolver {
            core: core,
            elimclauses: ElimClauses::new(settings.extend_model),
            simp: Some(Simplificator::new(settings.simp)),
        }
    }

    fn simpOff(&mut self) {
        if let Some(_) = self.simp {
            Simplificator::off(&mut self.core.search);
            self.simp = None;
        }
    }
}
