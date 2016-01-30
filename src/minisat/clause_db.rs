use std::cmp::Ordering;
use super::literal::Lit;
use super::clause::*;
use super::assignment::*;
use super::watches::*;


pub struct ClauseDBSettings {
    pub remove_satisfied : bool, // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.
    pub clause_decay     : f64
}

impl Default for ClauseDBSettings {
    fn default() -> ClauseDBSettings {
        ClauseDBSettings { remove_satisfied : true
                         , clause_decay     : 0.999
                         }
    }
}


pub struct ClauseDB {
    pub settings         : ClauseDBSettings,
    cla_inc              : f64,              // Amount to bump next clause with.
    pub ca               : ClauseAllocator,
    clauses              : Vec<ClauseRef>,   // List of problem clauses.
    learnts              : Vec<ClauseRef>,   // List of learnt clauses.
    pub num_clauses      : usize,
    pub num_learnts      : usize,
    pub clauses_literals : u64,
    pub learnts_literals : u64,
}

impl ClauseDB {
    pub fn new(settings : ClauseDBSettings) -> ClauseDB {
        ClauseDB { settings         : settings
                 , cla_inc          : 1.0
                 , ca               : ClauseAllocator::newEmpty()
                 , clauses          : Vec::new()
                 , learnts          : Vec::new()
                 , num_clauses      : 0
                 , num_learnts      : 0
                 , clauses_literals : 0
                 , learnts_literals : 0
                 }
    }

    pub fn addClause(&mut self, ps : &Vec<Lit>) -> ClauseRef {
        let cr = self.ca.alloc(ps, false);
        self.clauses.push(cr);
        self.num_clauses += 1;
        self.clauses_literals += ps.len() as u64;
        cr
    }

    pub fn learnClause(&mut self, learnt_clause : &Vec<Lit>) -> ClauseRef {
        let cr = self.ca.alloc(learnt_clause, true);
        self.learnts.push(cr);
        self.bumpActivity(cr);
        self.num_learnts += 1;
        self.learnts_literals += learnt_clause.len() as u64;
        cr
    }

    pub fn removeClause(&mut self, assigns : &mut Assignment, cr : ClauseRef) {
        {
            let ref c = self.ca[cr];
            if c.is_learnt() {
                self.num_learnts -= 1;
                self.learnts_literals -= c.len() as u64;
            } else {
                self.num_clauses -= 1;
                self.clauses_literals -= c.len() as u64;
            }
        }

        // TODO: do we really need this?
        assigns.forgetReason(&self.ca, cr);

        self.ca.free(cr);
    }

    pub fn editClause<F : FnOnce(&mut Clause) -> ()>(&mut self, cr : ClauseRef, f : F) {
        let c = self.ca.edit(cr);
        if c.is_learnt() { self.learnts_literals -= c.len() as u64; } else { self.clauses_literals -= c.len() as u64; }
        f(c);
        if c.is_learnt() { self.learnts_literals += c.len() as u64; } else { self.clauses_literals += c.len() as u64; }
    }

    pub fn bumpActivity(&mut self, cr : ClauseRef) {
        let new = {
            let c = self.ca.edit(cr);
            if !c.is_learnt() { return; }

            let new = c.activity() + self.cla_inc;
            c.setActivity(new);
            new
        };

        if new > 1e20 {
            self.cla_inc *= 1e-20;
            for cri in self.learnts.iter() {
                let c = self.ca.edit(*cri);
                let scaled = c.activity() * 1e-10;
                c.setActivity(scaled);
            }
        }
    }

    pub fn decayActivity(&mut self) {
        self.cla_inc *= 1.0 / self.settings.clause_decay;
    }

    pub fn needReduce(&self, border : usize) -> bool {
        self.learnts.len() >= border
    }

    // Description:
    //   Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
    //   clauses are clauses that are reason to some assignment. Binary clauses are never removed.
    pub fn reduce(&mut self, assigns : &mut Assignment, watches : &mut Watches) {
        {
            let ca = &self.ca;
            self.learnts.sort_by(|rx, ry| {
                let ref x = ca[*rx];
                let ref y = ca[*ry];
                if x.len() > 2 && (y.len() == 2 || x.activity() < y.activity()) {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            });
        }

        // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
        // and clauses with activity smaller than 'extra_lim':
        let extra_lim = self.cla_inc / self.learnts.len() as f64; // Remove any clause below this activity
        {
            let mut j = 0;
            for i in 0 .. self.learnts.len() {
                let cr = self.learnts[i];
                if self.ca[cr].is_deleted() { continue; }

                let remove = {
                    let ref c = self.ca[cr];
                    c.len() > 2 && !assigns.isLocked(&self.ca, cr)
                                && (i < self.learnts.len() / 2 || c.activity() < extra_lim)
                };
                if remove {
                    watches.unwatchClauseLazy(&self.ca[cr]);
                    self.removeClause(assigns, cr);
                } else {
                    self.learnts[j] = cr;
                    j += 1;
                }
            }
            self.learnts.truncate(j);
        }
    }

    fn retainClause(&mut self, assigns : &mut Assignment, watches : &mut Watches, cr : ClauseRef) -> bool {
        if self.ca[cr].is_deleted() {
            false
        } else if satisfiedWith(&self.ca[cr], assigns) {
            watches.unwatchClauseLazy(&self.ca[cr]);
            self.removeClause(assigns, cr);
            false
        } else {
            let c = self.ca.edit(cr);
            assert!(assigns.undef(c[0].var()) && assigns.undef(c[1].var()));
            c.retainSuffix(2, |lit| !assigns.unsat(*lit));
            true
        }
    }

    pub fn removeSatisfied(&mut self, assigns : &mut Assignment, watches : &mut Watches) {
        // Remove satisfied clauses:
        {
            let mut j = 0;
            for i in 0 .. self.learnts.len() {
                let cr = self.learnts[i];
                if self.retainClause(assigns, watches, cr) {
                    self.learnts[j] = cr;
                    j += 1;
                }
            }
            self.learnts.truncate(j);
        }

        // TODO: what todo in if 'remove_satisfied' is false?
        if self.settings.remove_satisfied {       // Can be turned off.
            let mut j = 0;
            for i in 0 .. self.clauses.len() {
                let cr = self.clauses[i];
                if self.retainClause(assigns, watches, cr) {
                    self.clauses[j] = cr;
                    j += 1;
                }
            }
            self.clauses.truncate(j);
        }
    }

    pub fn relocGC(&mut self, mut to : ClauseAllocator) {
        // All learnt:
        {
            let mut j = 0;
            for i in 0 .. self.learnts.len() {
                if !self.ca[self.learnts[i]].is_deleted() {
                    self.learnts[j] = self.ca.relocTo(&mut to, self.learnts[i]);
                    j += 1;
                }
            }
            self.learnts.truncate(j);
        }

        // All original:
        {
            let mut j = 0;
            for i in 0 .. self.clauses.len() {
                if !self.ca[self.clauses[i]].is_deleted() {
                    self.clauses[j] = self.ca.relocTo(&mut to, self.clauses[i]);
                    j += 1;
                }
            }
            self.clauses.truncate(j);
        }

        debug!("|  Garbage collection:   {:12} bytes => {:12} bytes             |", self.ca.size(), to.size());
        self.ca = to;
    }
}
