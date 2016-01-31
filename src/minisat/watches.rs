use minisat::formula::{Lit, Var};
use minisat::formula::index_map::LitMap;
use minisat::formula::clause::*;
use minisat::formula::assignment::*;
use minisat::propagation_trail::*;


#[derive(Clone)]
struct Watcher {
    pub cref    : ClauseRef,
    pub blocker : Lit
}


struct WatchesLine {
    watchers : Vec<Watcher>,
    dirty    : bool
}


pub struct Watches {
    watches          : LitMap<WatchesLine>,
    pub propagations : u64
}

impl Watches {
    pub fn new() -> Watches {
        Watches { watches      : LitMap::new()
                , propagations : 0
                }
    }

    pub fn initVar(&mut self, var : Var) {
        self.initLit(Lit::new(var, false));
        self.initLit(Lit::new(var, true));
    }

    fn initLit(&mut self, lit : Lit) {
        self.watches.insert(&lit, WatchesLine {
            watchers : Vec::new(),
            dirty    : false,
        });
    }

    pub fn tryClearVar(&mut self, var : Var) {
        self.tryClearLit(Lit::new(var, false));
        self.tryClearLit(Lit::new(var, true));
    }

    fn tryClearLit(&mut self, lit : Lit) {
        if self.watches[&lit].watchers.is_empty() {
            self.watches.remove(&lit);
        }
    }

    pub fn watchClause(&mut self, c : &Clause, cr : ClauseRef) {
        assert!(c.len() > 1);
        self.watches[&!c[0]].watchers.push(Watcher { cref : cr, blocker : c[1] });
        self.watches[&!c[1]].watchers.push(Watcher { cref : cr, blocker : c[0] });
    }

    pub fn unwatchClauseStrict(&mut self, c : &Clause, cr : ClauseRef)
    {
        assert!(c.len() > 1);
        self.watches[&!c[0]].watchers.retain(|w| w.cref != cr);
        self.watches[&!c[1]].watchers.retain(|w| w.cref != cr);
    }

    pub fn unwatchClauseLazy(&mut self, c : &Clause)
    {
        assert!(c.len() > 1);
        self.watches[&!c[0]].dirty = true;
        self.watches[&!c[1]].dirty = true;
    }

    // Description:
    //   Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
    //   otherwise CRef_Undef.
    //
    //   Post-conditions:
    //     * the propagation queue is empty, even if there was a conflict.
    pub fn propagate(&mut self, trail : &mut PropagationTrail<Lit>, assigns : &mut Assignment, ca : &mut ClauseAllocator) -> Option<ClauseRef> {
        while let Some(p) = trail.dequeue() {
            self.propagations += 1;
            let false_lit = !p;

            {
                let ref mut line = self.watches[&p];
                if line.dirty {
                    line.watchers.retain(|w| { !ca[w.cref].is_deleted() });
                    line.dirty = false;
                }
            }

            let mut i = 0;
            let mut j = 0;
            loop {
                let (cw, new_watch) = {
                    let ref mut p_watches = self.watches[&p].watchers;
                    if i >= p_watches.len() { break; }
                    let pwi = p_watches[i].clone();
                    i += 1;

                    if assigns.sat(pwi.blocker) {
                        p_watches[j] = pwi;
                        j += 1;
                        continue;
                    }

                    let c = ca.edit(pwi.cref);
                    if c[0] == false_lit {
                        c[0] = c[1];
                        c[1] = false_lit;
                    }
                    assert!(c[1] == false_lit);

                    // If 0th watch is true, then clause is already satisfied.
                    let cw = Watcher { cref : pwi.cref, blocker : c[0] };
                    if cw.blocker != pwi.blocker && assigns.sat(cw.blocker) {
                        p_watches[j] = cw;
                        j += 1;
                        continue;
                    }

                    // Look for new watch:
                    let mut new_watch = None;
                    for k in 2 .. c.len() {
                        if !assigns.unsat(c[k]) {
                            let lit = c[k];
                            c[1] = lit;
                            c[k] = false_lit;
                            new_watch = Some(lit);
                            break;
                        }
                    }

                    (cw, new_watch)
                };

                match new_watch {
                    Some(lit) => {
                        self.watches[&!lit].watchers.push(cw);
                    }

                    // Did not find watch -- clause is unit under assignment:
                    None      => {
                        let ref mut p_watches = self.watches[&p].watchers;
                        p_watches[j] = cw.clone();
                        j += 1;

                        if assigns.unsat(cw.blocker) {
                            trail.dequeueAll();

                            // Copy the remaining watches:
                            while i < p_watches.len() {
                                p_watches[j] = p_watches[i].clone();
                                j += 1;
                                i += 1;
                            }

                            p_watches.truncate(j);
                            return Some(cw.cref);
                        } else {
                            assigns.assignLit(cw.blocker, trail.decisionLevel(), Some(cw.cref));
                            trail.push(cw.blocker);
                        }
                    }
                }
            }

            self.watches[&p].watchers.truncate(j);
        }

        None
    }

    pub fn relocGC(&mut self, from : &mut ClauseAllocator, to : &mut ClauseAllocator) {
        for (_, line) in self.watches.iter_mut() {
            line.dirty = false;
            line.watchers.retain(|w| { !from[w.cref].is_deleted() });
            for w in line.watchers.iter_mut() {
                w.cref = from.relocTo(to, w.cref);
            }
        }
    }
}
