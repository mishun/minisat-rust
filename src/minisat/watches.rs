use super::literal::{Lit, Var};
use super::clause::{ClauseRef, ClauseAllocator};
use super::index_map::{IndexMap};


#[deriving(Clone)]
pub struct Watcher {
    pub cref    : ClauseRef,
    pub blocker : Lit,
}


struct WatchesLine {
    watchers : Vec<Watcher>,
    dirty    : bool,
}

impl WatchesLine {
    #[inline]
    fn clean(&mut self, ca : &ClauseAllocator) {
        if self.dirty {
            self.watchers.retain(|w| {
                !(ca[w.cref].mark() == 1)
            });
            self.dirty = false;
        }
    }
}


pub struct Watches {
    watches : IndexMap<Lit, WatchesLine>,
    dirties : Vec<Lit>,
}

impl Watches {
    pub fn new() -> Watches {
        Watches {
            watches : IndexMap::new(),
            dirties : Vec::new()
        }
    }

    pub fn initVar(&mut self, var : Var) {
        self.initLit(Lit::new(var, false));
        self.initLit(Lit::new(var, true));
    }

    pub fn initLit(&mut self, lit : Lit) {
        self.watches.insert(&lit, WatchesLine {
            watchers : Vec::new(),
            dirty : false,
        });
    }

    pub fn lookup(&mut self, ca : &ClauseAllocator, lit : Lit) -> &mut Vec<Watcher> {
        let wl = &mut self.watches[lit];
        wl.clean(ca);
        &mut wl.watchers
    }

    pub fn smudge(&mut self, lit : Lit) {
        let wl = &mut self.watches[lit];
        if !wl.dirty {
            wl.dirty = true;
            self.dirties.push(lit);
        }
    }

    pub fn cleanAll(&mut self, ca : &ClauseAllocator) {
        for dl in self.dirties.iter() {
            self.watches[*dl].clean(ca);
        }
        self.dirties.clear();
    }

    pub fn clear(&mut self) {
        self.watches.clear();
        self.dirties.clear();
    }
}

impl Index<Lit, Vec<Watcher>> for Watches {
    #[inline]
    fn index(&self, lit : &Lit) -> &Vec<Watcher> {
        &self.watches[*lit].watchers
    }
}

impl IndexMut<Lit, Vec<Watcher>> for Watches {
    #[inline]
    fn index_mut(&mut self, lit : &Lit) -> &mut Vec<Watcher> {
        &mut self.watches[*lit].watchers
    }
}
