use crate::sat::formula::{assignment::*, clause::*, Lit, Var};
use super::watches::Watches;


pub struct BacktrackableFormula {
    pub ca: ClauseAllocator,
    pub assigns: Assignment, // The current assignments.
    pub watches: Watches     // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
}

impl BacktrackableFormula {
    pub fn new() -> Self {
        BacktrackableFormula {
            ca: ClauseAllocator::new_empty(),
            assigns: Assignment::new(),
            watches: Watches::new()
        }
    }

    pub fn new_var(&mut self) -> Var {
        let v = self.assigns.new_var();
        self.watches.init_var(v);
        v
    }


    pub fn attach(&mut self, cr: ClauseRef) {
        let c = self.ca.view(cr);
        self.watches.watch_clause(c, cr);
    }

    pub fn force_detach(&mut self, cr: ClauseRef) {
        self.watches.unwatch_clause_strict(self.ca.view(cr), cr);
    }

    pub fn lazy_detach(&mut self, cr: ClauseRef) {
        self.watches.unwatch_clause_lazy(self.ca.view(cr));
    }

    pub fn try_clear_var(&mut self, v: Var) {
        self.watches.try_clear_var(v);
    }


    pub fn propagations(&self) -> u64 {
        self.watches.propagations
    }

    pub fn propagate(&mut self) -> Option<ClauseRef> {
        self.watches.propagate(&mut self.ca, &mut self.assigns)
    }


    pub fn is_ground_level(&self) -> bool {
        self.assigns.current_level().is_ground()
    }

    pub fn push_decision(&mut self, next: Lit) {
        // Increase decision level and enqueue 'next'
        self.assigns.new_decision_level();
        self.assigns.assign_lit(next, None);
    }


    pub fn reloc_gc(&mut self, to: &mut ClauseAllocator) {
        self.watches.reloc_gc(&mut self.ca, to);
        self.assigns.reloc_gc(&mut self.ca, to);
    }

/*
    pub fn start<'a>(&'a mut self) -> Backtrack<'a> {
        match self.watches.propagate(&mut self.ca, &mut self.assigns) {
            Some(confl) => {
                Backtrack::Conflict(confl, BacktrackConflict { formula: self })
            }

            None => {
                Backtrack::Decide(BacktrackDecide { formula : self })
            }
        }
    }*/
}


//pub enum Backtrack<'a> {
//    Conflict(ClauseRef, BacktrackConflict<'a>),
//    Decide(BacktrackDecide<'a>)
//}


/*
pub struct BacktrackConflict<'a> {
    formula: &'a mut BacktrackableFormula
}

impl<'a> BacktrackConflict<'a> {
    pub fn invalidate(self) {
    }

    pub fn unit(self, level: DecisionLevel, unit: Lit) -> Backtrack<'a> {
        //self.cancel_until(level);
        self.formula.assigns.assign_lit(unit, None);

        match self.formula.watches.propagate(&mut self.formula.ca, &mut self.formula.assigns) {
            Some(confl) => {
                Backtrack::Conflict(confl, BacktrackConflict { formula: self.formula })
            }

            None => {
                Backtrack::Decide(BacktrackDecide { formula : self.formula })
            }
        }
    }

    pub fn learned(self, level: DecisionLevel, lit: Lit, cr: ClauseRef) -> Backtrack<'a> {
        //self.cancel_until(level);
        //let (c, cr) = self.db.learn_clause(&mut self.ca, &clause[..]);

        let c = self.formula.ca.view(cr);
        self.formula.watches.watch_clause(c, cr);
        self.formula.assigns.assign_lit(lit, Some(cr));

        match self.formula.watches.propagate(&mut self.formula.ca, &mut self.formula.assigns) {
            Some(confl) => {
                Backtrack::Conflict(confl, BacktrackConflict { formula: self.formula })
            }

            None => {
                Backtrack::Decide(BacktrackDecide { formula : self.formula })
            }
        }
    }
}
*/

/*
pub struct BacktrackDecide<'a> {
    formula: &'a mut BacktrackableFormula
}

impl<'a> BacktrackDecide<'a> {
    pub fn decide(self, next: Lit) -> Backtrack<'a> {
        self.formula.assigns.new_decision_level();
        self.formula.assigns.assign_lit(next, None);

        match self.formula.watches.propagate(&mut self.formula.ca, &mut self.formula.assigns) {
            Some(confl) => {
                Backtrack::Conflict(confl, BacktrackConflict { formula: self.formula })
            }

            None => {
                Backtrack::Decide(BacktrackDecide { formula : self.formula })
            }
        }
    }
}
*/