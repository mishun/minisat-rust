use super::literal::{Lit, Var};
use super::clause::{ClauseRef, ClauseAllocator};
use super::index_map::{IndexMap};


#[derive(Clone)]
pub struct Watcher {
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
    watches : IndexMap<Lit, WatchesLine>,
    dirties : Vec<Lit>
}

impl Watches {
    pub fn new() -> Watches {
        Watches { watches : IndexMap::new()
                , dirties : Vec::new()
                }
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
        } else if !wl.dirty {
            wl.dirty = true;
            self.dirties.push(!lit);
        }
    }

    pub fn lookup(&mut self, ca : &ClauseAllocator, lit : Lit) -> &mut Vec<Watcher> {
        let wl = &mut self.watches[&lit];
        wl.clean(ca);
        &mut wl.watchers
    }

    pub fn getDirty(&mut self, lit : Lit) -> &mut Vec<Watcher> {
        &mut self.watches[&lit].watchers
    }

    pub fn cleanAll(&mut self, ca : &ClauseAllocator) {
        for dl in self.dirties.iter() {
            self.watches[dl].clean(ca);
        }
        self.dirties.clear();
    }
}
