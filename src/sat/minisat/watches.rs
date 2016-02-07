use sat::formula::{Lit, Var, LitMap};
use sat::formula::assignment::Assignment;
use sat::formula::clause::*;


#[derive(Clone, Copy)]
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
        self.initLit(var.posLit());
        self.initLit(var.negLit());
    }

    fn initLit(&mut self, lit : Lit) {
        self.watches.insert(&lit, WatchesLine {
            watchers : Vec::new(),
            dirty    : false,
        });
    }

    pub fn tryClearVar(&mut self, var : Var) {
        self.tryClearLit(var.posLit());
        self.tryClearLit(var.negLit());
    }

    fn tryClearLit(&mut self, lit : Lit) {
        if self.watches[&lit].watchers.is_empty() {
            self.watches.remove(&lit);
        }
    }

    pub fn watchClause(&mut self, c : &Clause, cr : ClauseRef) {
        let (c0, c1) = c.headPair();
        self.watches[&!c0].watchers.push(Watcher { cref : cr, blocker : c1 });
        self.watches[&!c1].watchers.push(Watcher { cref : cr, blocker : c0 });
    }

    pub fn unwatchClauseStrict(&mut self, c : &Clause, cr : ClauseRef)
    {
        let (c0, c1) = c.headPair();
        self.watches[&!c0].watchers.retain(|w| w.cref != cr);
        self.watches[&!c1].watchers.retain(|w| w.cref != cr);
    }

    pub fn unwatchClauseLazy(&mut self, c : &Clause)
    {
        let (c0, c1) = c.headPair();
        self.watches[&!c0].dirty = true;
        self.watches[&!c1].dirty = true;
    }

    // Description:
    //   Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
    //   otherwise CRef_Undef.
    //
    //   Post-conditions:
    //     * the propagation queue is empty, even if there was a conflict.
    pub fn propagate(&mut self, ca : &mut ClauseAllocator, assigns : &mut Assignment) -> Option<ClauseRef> {
        while let Some(p) = assigns.dequeue() {
            self.propagations += 1;
            let false_lit = !p;

            {
                let ref mut line = self.watches[&p];
                if line.dirty {
                    line.watchers.retain(|w| { !ca.isDeleted(w.cref) });
                    line.dirty = false;
                }
            }

            let mut i = 0;
            let mut j = 0;
            loop {
                let (cw, new_watch) = {
                    let ref mut p_watches = self.watches[&p].watchers;
                    if i >= p_watches.len() { break; }
                    let pwi = p_watches[i];
                    i += 1;

                    if assigns.isSat(pwi.blocker) {
                        p_watches[j] = pwi;
                        j += 1;
                        continue;
                    }

                    let c = ca.edit(pwi.cref);
                    if c.head() == false_lit {
                        c.swap(0, 1);
                    }
                    assert!(c[1] == false_lit);

                    // If 0th watch is true, then clause is already satisfied.
                    let cw = Watcher { cref : pwi.cref, blocker : c.head() };
                    if cw.blocker != pwi.blocker && assigns.isSat(cw.blocker) {
                        p_watches[j] = cw;
                        j += 1;
                        continue;
                    }

                    // Look for new watch:
                    (cw, c.pullLiteral(1, |lit| { !assigns.isUnsat(lit) }))
                };

                match new_watch {
                    Some(lit) => {
                        self.watches[&!lit].watchers.push(cw);
                    }

                    // Did not find watch -- clause is unit under assignment:
                    None      => {
                        let ref mut p_watches = self.watches[&p].watchers;
                        p_watches[j] = cw;
                        j += 1;

                        if assigns.isUnsat(cw.blocker) {
                            assigns.dequeueAll();

                            // Copy the remaining watches:
                            while i < p_watches.len() {
                                p_watches[j] = p_watches[i];
                                j += 1;
                                i += 1;
                            }

                            p_watches.truncate(j);
                            return Some(cw.cref);
                        } else {
                            assigns.assignLit(cw.blocker, Some(cw.cref));
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
            line.watchers.retain(|w| { !from.isDeleted(w.cref) });
            for w in line.watchers.iter_mut() {
                w.cref = from.relocTo(to, w.cref);
            }
        }
    }
}
