use sat::formula::{Var, Lit, VarMap, LitMap, VarHeap};
use sat::formula::assignment::Assignment;
use sat::formula::clause::*;


#[derive(Debug)]
pub struct VarStatus {
    pub frozen     : i8,
    pub eliminated : i8
}


pub struct ElimQueue {
    heap  : VarHeap,
    n_occ : LitMap<isize>
}

impl ElimQueue {
    pub fn new() -> ElimQueue {
        ElimQueue {
            heap  : VarHeap::new(),
            n_occ : LitMap::new()
        }
    }

    pub fn initVar(&mut self, v : Var) {
        self.n_occ.insert(&v.posLit(), 0);
        self.n_occ.insert(&v.negLit(), 0);

        let ref n_occ = self.n_occ;
        self.heap.insert(v, move |a, b| { Self::before(n_occ, a, b) });
    }

    #[inline]
    fn before(n_occ : &LitMap<isize>, a : &Var, b : &Var) -> bool {
        let costA = (n_occ[&a.posLit()] as u64) * (n_occ[&a.negLit()] as u64);
        let costB = (n_occ[&b.posLit()] as u64) * (n_occ[&b.negLit()] as u64);
        costA < costB
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.heap.len()
    }

    pub fn updateElimHeap(&mut self, v : Var, var_status : &VarMap<VarStatus>, assigns : &Assignment) {
        let ref n_occ = self.n_occ;
        if self.heap.contains(&v) {
            self.heap.update(&v, move |a, b| { Self::before(n_occ, a, b) });
        } else if var_status[&v].frozen == 0 && var_status[&v].eliminated == 0 && assigns.isUndef(v) {
            self.heap.insert(v, move |a, b| { Self::before(n_occ, a, b) });
        }
    }

    pub fn clear(&mut self) {
        self.heap.clear();
    }

    pub fn bumpLitOcc(&mut self, lit : &Lit, delta : isize) {
        self.n_occ[lit] += delta;

        let ref n_occ = self.n_occ;
        self.heap.update(&lit.var(), move |a, b| { Self::before(n_occ, a, b) });
    }

    pub fn pop(&mut self) -> Option<Var>
    {
        let ref n_occ = self.n_occ;
        self.heap.pop(move |a, b| { Self::before(n_occ, a, b) })
    }
}


#[derive(Debug)]
struct OccLine {
    occs  : Vec<ClauseRef>,
    dirty : bool
}

pub struct OccLists {
    occs : VarMap<OccLine>
}

impl OccLists {
    pub fn new() -> OccLists {
        OccLists { occs : VarMap::new() }
    }

    pub fn initVar(&mut self, v : &Var) {
        self.occs.insert(v, OccLine { occs : Vec::new(), dirty : false });
    }

    pub fn clearVar(&mut self, v : &Var) {
        self.occs.remove(v);
    }

    pub fn pushOcc(&mut self, v : &Var, x : ClauseRef) {
        self.occs[v].occs.push(x);
    }

    pub fn removeOcc(&mut self, v : &Var, x : ClauseRef) {
        self.occs[v].occs.retain(|&y| { y != x })
    }

    pub fn lookup(&mut self, v : &Var, ca : &ClauseAllocator) -> &Vec<ClauseRef> {
        let ol = &mut self.occs[v];
        if ol.dirty {
            ol.occs.retain(|&cr| { !ca.isDeleted(cr) });
            ol.dirty = false;
        }
        &ol.occs
    }

    pub fn occsDirty(&self, v : Var) -> usize {
        self.occs[&v].occs.len()
    }

    pub fn smudge(&mut self, v : &Var) {
        let ol = &mut self.occs[v];
        if !ol.dirty {
            ol.dirty = true;
        }
    }

    pub fn relocGC(&mut self, from : &mut ClauseAllocator, to : &mut ClauseAllocator) {
        for (_, ol) in self.occs.iter_mut() {
            if ol.dirty {
                ol.occs.retain(|&cr| { !from.isDeleted(cr) });
                ol.dirty = false;
            }

            for occ in ol.occs.iter_mut() {
                *occ = from.relocTo(to, *occ);
            }
        }
    }
}
