use std::cmp::Ordering;
use crate::sat::formula::{assignment::Assignment, clause::*, util::*, Lit};


pub struct ClauseDBSettings {
    pub remove_satisfied: bool, // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.
    pub clause_decay: f64,
}

impl Default for ClauseDBSettings {
    fn default() -> ClauseDBSettings {
        ClauseDBSettings {
            remove_satisfied: true,
            clause_decay: 0.999,
        }
    }
}


#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    pub num_clauses: usize,
    pub num_learnts: usize,
    pub clauses_literals: u64,
    pub learnts_literals: u64,
}

impl Stats {
    fn add(&mut self, clause: &Clause) {
        match clause.header {
            ClauseHeader::Learnt { activity: _ } => {
                self.num_learnts += 1;
                self.learnts_literals += clause.len() as u64;
            }

            ClauseHeader::Clause { abstraction: _ } => {
                self.num_clauses += 1;
                self.clauses_literals += clause.len() as u64;
            }
        }
    }

    fn del(&mut self, clause: &Clause) {
        match clause.header {
            ClauseHeader::Learnt { activity: _ } => {
                self.num_learnts -= 1;
                self.learnts_literals -= clause.len() as u64;
            }

            ClauseHeader::Clause { abstraction: _ } => {
                self.num_clauses -= 1;
                self.clauses_literals -= clause.len() as u64;
            }
        }
    }
}


pub struct ClauseDB {
    pub settings: ClauseDBSettings,
    cla_inc: f64,            // Amount to bump next clause with.
    clauses: Vec<ClauseRef>, // List of problem clauses.
    learnts: Vec<ClauseRef>, // List of learnt clauses.
    pub stats: Stats,
}

impl ClauseDB {
    pub fn new(settings: ClauseDBSettings) -> ClauseDB {
        ClauseDB {
            settings,
            cla_inc: 1.0,
            clauses: Vec::new(),
            learnts: Vec::new(),
            stats: Stats::default(),
        }
    }

    pub fn add_clause<'c>(&mut self, ca: &'c mut ClauseAllocator, literals: &[Lit]) -> ClauseRef {
        let header = ClauseHeader::Clause {
            abstraction:
                if ca.extra_clause_field {
                    Some(calc_abstraction(literals))
                } else {
                    None
                }
        };
        let (c, cr) = ca.alloc(literals, header);
        self.stats.add(c);
        self.clauses.push(cr);
        cr
    }

    pub fn learn_clause<'c>(&mut self, ca: &mut ClauseAllocator, literals: &[Lit]) -> ClauseRef {
        let header = ClauseHeader::Learnt { activity: 0.0 };
        let (c, cr) = ca.alloc(literals, header);
        self.stats.add(c);
        self.learnts.push(cr);
        self.bump_activity(ca, cr);
        cr
    }

    pub fn remove_clause(&mut self, ca: &mut ClauseAllocator, cr: ClauseRef) {
        self.stats.del(ca.view(cr));
        ca.free(cr);
    }

    pub fn edit_clause<F: FnOnce(&mut Clause) -> ()>(
        &mut self,
        ca: &mut ClauseAllocator,
        cr: ClauseRef,
        f: F,
    ) {
        let c = ca.edit(cr);
        self.stats.del(c);
        f(c);
        self.stats.add(c);
    }

    pub fn bump_activity(&mut self, ca: &mut ClauseAllocator, cr: ClauseRef) {
        let new = {
            let c = ca.edit(cr);
            if let ClauseHeader::Learnt { ref mut activity } = c.header {
                let new = *activity as f64 + self.cla_inc;
                *activity = new as f32;
                new
            } else {
                return;
            }
        };

        if new > 1e20 {
            self.cla_inc *= 1e-20;
            for &cri in self.learnts.iter() {
                let c = ca.edit(cri);
                if let ClauseHeader::Learnt { ref mut activity } = c.header {
                    let scaled = (*activity as f64) * 1e-20;
                    *activity = scaled as f32;
                } else {
                    panic!("Expected learnt");
                }
            }
        }
    }

    pub fn decay_activity(&mut self) {
        self.cla_inc *= 1.0 / self.settings.clause_decay;
    }

    pub fn number_of_learnts(&self) -> usize {
        self.learnts.len()
    }

    // Description:
    //   Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
    //   clauses are clauses that are reason to some assignment. Binary clauses are never removed.
    pub fn reduce<F: FnMut(&Clause) -> ()>(
        &mut self,
        ca: &mut ClauseAllocator,
        assigns: &Assignment,
        mut notify: F,
    ) {
        self.learnts.sort_by(|&rx, &ry| {
            let x = ca.view(rx);
            let y = ca.view(ry);

            if x.len() == 2 && y.len() == 2 {
                Ordering::Equal
            } else if x.len() == 2 {
                Ordering::Greater
            } else if y.len() == 2 {
                Ordering::Less
            } else {
                let x_activity = x.header.activity();
                let y_activity = y.header.activity();
                x_activity.partial_cmp(&y_activity).unwrap()
            }
        });

        // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
        // and clauses with activity smaller than 'extra_lim':
        {
            let index_lim = self.learnts.len() / 2;
            let extra_lim = self.cla_inc / self.learnts.len() as f64; // Remove any clause below this activity
            let stats = &mut self.stats;

            let mut i = 0;
            self.learnts.retain(move |&cr| {
                if ca.is_deleted(cr) {
                    i += 1;
                    return false;
                }

                let remove = {
                    let c = ca.view(cr);
                    let remove = c.len() > 2 && !assigns.is_reason_for(cr, c.head[0])
                        && (i < index_lim || (c.header.activity() as f64) < extra_lim);

                    if remove {
                        notify(c);
                        stats.del(c);
                    }

                    remove
                };

                i += 1;
                if remove {
                    ca.free(cr);
                    false
                } else {
                    true
                }
            });
        }
    }

    fn retain_clause<F: FnMut(&Clause) -> ()>(
        stats: &mut Stats,
        ca: &mut ClauseAllocator,
        assigns: &Assignment,
        notify: &mut F,
        cr: ClauseRef,
    ) -> bool {
        if ca.is_deleted(cr) {
            false
        } else if satisfied_with_assignment(ca.view(cr).lits(), assigns) {
            notify(ca.view(cr));
            stats.del(ca.view(cr));
            ca.free(cr);
            false
        } else {
            let clause = ca.edit(cr);
            retain_clause(clause, assigns);
            true
        }
    }

    pub fn remove_satisfied<F>(&mut self, ca: &mut ClauseAllocator, assigns: &Assignment, mut notify: F)
        where F: FnMut(&Clause) -> ()
    {
        // Remove satisfied clauses:
        let stats = &mut self.stats;
        self.learnts.retain(|&cr| {
            Self::retain_clause(stats, ca, assigns, &mut notify, cr)
        });

        // TODO: what todo in if 'remove_satisfied' is false?
        if self.settings.remove_satisfied {
            // Can be turned off.
            self.clauses.retain(|&cr| {
                Self::retain_clause(stats, ca, assigns, &mut notify, cr)
            });
        }
    }

    pub fn gc(&mut self, gc: &mut ClauseGC) {
        // All learnt:
        {
            let mut j = 0;
            for i in 0..self.learnts.len() {
                if let Some(cr) = gc.relocate(self.learnts[i]) {
                    self.learnts[j] = cr;
                    j += 1;
                }
            }
            self.learnts.truncate(j);
        }

        // All original:
        {
            let mut j = 0;
            for i in 0..self.clauses.len() {
                if let Some(cr) = gc.relocate(self.clauses[i]) {
                    self.clauses[j] = cr;
                    j += 1;
                }
            }
            self.clauses.truncate(j);
        }
    }
}

fn retain_clause(clause: &mut Clause, assigns: &Assignment) {
    assert!({
        let [c0, c1] = clause.head;
        assigns.is_undef(c0.var()) && assigns.is_undef(c1.var())
    });

    unsafe {
        let (mut l, mut r) = clause.ptr_range();
        l = l.add(2);

        while l < r {
            if !assigns.is_assigned_neg(*l) {
                l = l.offset(1);
            } else {
                clause.shrink_by(1);
                r = r.offset(-1);
                *l = *r;
            }
        }
    }
}
