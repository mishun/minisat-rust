use super::index_map::IndexMap;
use super::literal::{Lit, Var};
use super::clause::{ClauseRef, ClauseAllocator};
use super::assignment::*;
use super::propagation_trail::*;


#[derive(Clone)]
struct Watcher {
    pub cref    : ClauseRef,
    pub blocker : Lit
}


struct WatchesLine {
    watchers : Vec<Watcher>,
    dirty    : bool
}

impl WatchesLine {
    #[inline]
    fn clean(&mut self, ca : &ClauseAllocator) {
        if self.dirty {
            self.watchers.retain(|w| { !ca[w.cref].is_deleted() });
            self.dirty = false;
        }
    }
}


pub struct Watches {
    watches : IndexMap<Lit, WatchesLine>
}

impl Watches {
    pub fn new() -> Watches {
        Watches { watches : IndexMap::new() }
    }

    pub fn initVar(&mut self, var : Var) {
        self.initLit(Lit::new(var, false));
        self.initLit(Lit::new(var, true));
    }

    pub fn initLit(&mut self, lit : Lit) {
        self.watches.insert(&lit, WatchesLine {
            watchers : Vec::new(),
            dirty    : false,
        });
    }

    pub fn tryClearVar(&mut self, var : Var) {
        self.tryClearLit(Lit::new(var, false));
        self.tryClearLit(Lit::new(var, true));
    }

    pub fn tryClearLit(&mut self, lit : Lit) {
        if self.watches[&lit].watchers.is_empty() {
            self.watches.remove(&lit);
        }
    }

    pub fn watch(&mut self, lit : Lit, cr : ClauseRef, blocker : Lit) {
        self.watches[&!lit].watchers.push(Watcher { cref : cr, blocker : blocker });
    }

    pub fn unwatch(&mut self, lit : Lit, cr : ClauseRef, strict : bool) {
        let wl = &mut self.watches[&!lit];
        if strict {
            wl.watchers.retain(|w| w.cref != cr);
        } else {
            wl.dirty = true;
        }
    }

    pub fn propagate(&mut self, trail : &mut PropagationTrail<Lit>, assigns : &mut Assignment, ca : &mut ClauseAllocator) -> (Option<ClauseRef>, u64) {
        let mut confl = None;
        let mut num_props = 0;

        while let Some(p) = trail.dequeue() {
            num_props += 1;
            let false_lit = !p;

            self.watches[&p].clean(ca);

            let mut i = 0;
            let mut j = 0;
            loop {
                let (cw, first, new_watch) = {
                    let ref mut p_watches = self.watches[&p].watchers;
                    if i >= p_watches.len() { break; }

                    let cw = p_watches[i].clone();
                    if assigns.sat(cw.blocker) {
                        p_watches[j] = p_watches[i].clone();
                        i += 1;
                        j += 1;
                        continue;
                    }

                    let ref mut c = ca[cw.cref];
                    if c[0] == false_lit {
                        c[0] = c[1];
                        c[1] = false_lit;
                    }
                    assert!(c[1] == false_lit);
                    i += 1;

                    // If 0th watch is true, then clause is already satisfied.
                    let first = c[0];
                    if first != cw.blocker && assigns.sat(first) {
                        p_watches[j] = Watcher { cref : cw.cref, blocker : first };
                        j += 1;
                        continue;
                    }

                    // Look for new watch:
                    let mut new_watch = None;
                    for k in 2 .. c.len() {
                        if !assigns.unsat(c[k]) {
                            new_watch = Some(k);
                            break;
                        }
                    }

                    (cw, first, new_watch)
                };

                match new_watch {
                    Some(k) => {
                        let ref mut c = ca[cw.cref];
                        let lit = c[k];
                        c[1] = lit;
                        c[k] = false_lit;
                        self.watch(lit, cw.cref, first);
                    }

                    // Did not find watch -- clause is unit under assignment:
                    None    => {
                        let ref mut p_watches = self.watches[&p].watchers;
                        p_watches[j] = Watcher { cref : cw.cref, blocker : first };
                        j += 1;

                        if assigns.unsat(first) {
                            confl = Some(cw.cref);
                            trail.dequeueAll();

                            // Copy the remaining watches:
                            while i < p_watches.len() {
                                p_watches[j] = p_watches[i].clone();
                                j += 1;
                                i += 1;
                            }
                        } else {
                            assigns.assignLit(first, VarData { level : trail.decisionLevel(), reason : Some(cw.cref) });
                            trail.push(first);
                        }
                    }
                }
            }

            self.watches[&p].watchers.truncate(j);
        }

        (confl, num_props)
    }

    pub fn relocGC(&mut self, from : &mut ClauseAllocator, to : &mut ClauseAllocator) {
        self.watches.modify_in_place(|line| {
            line.clean(from);
            for w in line.watchers.iter_mut() {
                w.cref = from.relocTo(to, w.cref);
            }
        });
    }
}
