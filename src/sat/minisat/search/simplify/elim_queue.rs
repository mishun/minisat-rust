use crate::sat::formula::{Lit, LitMap, Var, VarHeap, VarMap};
use crate::sat::formula::assignment::Assignment;
use crate::sat::formula::clause::*;


#[derive(Debug)]
pub struct VarStatus {
    pub frozen: bool,
    pub eliminated: bool,
}


pub struct ElimQueue {
    heap: VarHeap,
    n_occ: LitMap<isize>,
}

impl ElimQueue {
    pub fn new() -> ElimQueue {
        ElimQueue {
            heap: VarHeap::new(),
            n_occ: LitMap::new(),
        }
    }

    pub fn init_var(&mut self, v: Var) {
        self.n_occ.insert(&v.pos_lit(), 0);
        self.n_occ.insert(&v.neg_lit(), 0);

        let ref n_occ = self.n_occ;
        self.heap.insert(v, move |a, b| Self::before(n_occ, a, b));
    }

    #[inline]
    fn before(n_occ: &LitMap<isize>, a: &Var, b: &Var) -> bool {
        let cost_a = (n_occ[&a.pos_lit()] as u64) * (n_occ[&a.neg_lit()] as u64);
        let cost_b = (n_occ[&b.pos_lit()] as u64) * (n_occ[&b.neg_lit()] as u64);
        cost_a < cost_b
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.heap.len()
    }

    pub fn update_elim_heap(
        &mut self,
        v: Var,
        var_status: &VarMap<VarStatus>,
        assigns: &Assignment,
    ) {
        let ref n_occ = self.n_occ;
        if self.heap.contains(&v) {
            self.heap.update(&v, move |a, b| Self::before(n_occ, a, b));
        } else if !var_status[&v].frozen && !var_status[&v].eliminated && assigns.is_undef(v) {
            self.heap.insert(v, move |a, b| Self::before(n_occ, a, b));
        }
    }

    pub fn clear(&mut self) {
        self.heap.clear();
    }

    pub fn bump_lit_occ(&mut self, lit: &Lit, delta: isize) {
        self.n_occ[lit] += delta;

        let ref n_occ = self.n_occ;
        self.heap
            .update(&lit.var(), move |a, b| Self::before(n_occ, a, b));
    }

    pub fn pop(&mut self) -> Option<Var> {
        let ref n_occ = self.n_occ;
        self.heap.pop(move |a, b| Self::before(n_occ, a, b))
    }
}


#[derive(Debug)]
struct OccLine {
    occs: Vec<ClauseRef>,
    dirty: bool,
}

pub struct OccLists {
    occs: VarMap<OccLine>,
}

impl OccLists {
    pub fn new() -> OccLists {
        OccLists {
            occs: VarMap::new(),
        }
    }

    pub fn init_var(&mut self, v: &Var) {
        self.occs.insert(
            v,
            OccLine {
                occs: Vec::new(),
                dirty: false,
            },
        );
    }

    pub fn clear_var(&mut self, v: &Var) {
        self.occs.remove(v);
    }

    pub fn push_occ(&mut self, v: &Var, x: ClauseRef) {
        self.occs[v].occs.push(x);
    }

    pub fn remove_occ(&mut self, v: &Var, x: ClauseRef) {
        self.occs[v].occs.retain(|&y| y != x)
    }

    pub fn lookup(&mut self, ca: &ClauseAllocator, v: Var) -> &Vec<ClauseRef> {
        let ol = &mut self.occs[&v];
        if ol.dirty {
            ol.occs.retain(|&cr| !ca.is_deleted(cr));
            ol.dirty = false;
        }
        &ol.occs
    }

    pub fn occs_dirty(&self, v: Var) -> usize {
        self.occs[&v].occs.len()
    }

    pub fn smudge(&mut self, v: &Var) {
        let ol = &mut self.occs[v];
        if !ol.dirty {
            ol.dirty = true;
        }
    }

    pub fn gc(&mut self, gc: &mut ClauseGC) {
        for (_, ol) in self.occs.iter_mut() {
            let mut j = 0;
            for i in 0..ol.occs.len() {
                if let Some(cr) = gc.relocate(ol.occs[i]) {
                    ol.occs[j] = cr;
                    j += 1;
                }
            }
            ol.occs.truncate(j);
            ol.dirty = false;
        }
    }
}


pub struct ElimOcc {
    pub occurs: OccLists,
    pub elim: ElimQueue,
    pub var_status: VarMap<VarStatus>
}

impl ElimOcc {
    pub fn new() -> Self {
        ElimOcc {
            occurs: OccLists::new(),
            elim: ElimQueue::new(),
            var_status: VarMap::new()
        }
    }

    pub fn init_var(&mut self, v: Var) {
        self.var_status.insert(&v, VarStatus { frozen: false, eliminated: false });
        self.occurs.init_var(&v);
        self.elim.init_var(v);
    }

    pub fn add_clause(&mut self, cr: ClauseRef, lits: &[Lit]) {
        for &lit in lits {
            self.occurs.push_occ(&lit.var(), cr);
            self.elim.bump_lit_occ(&lit, 1);
        }
    }

    pub fn smudge_clause(&mut self, assigns: &Assignment, lits: &[Lit]) {
        for &lit in lits {
            self.elim.bump_lit_occ(&lit, -1);
            self.elim.update_elim_heap(lit.var(), &self.var_status, assigns);
            self.occurs.smudge(&lit.var());
        }
    }

    pub fn remove_lit(&mut self, assigns: &Assignment, l: Lit, cr: ClauseRef) {
        self.elim.bump_lit_occ(&l, -1);
        self.elim.update_elim_heap(l.var(), &self.var_status, assigns);
        self.occurs.remove_occ(&l.var(), cr);
    }

    pub fn is_eliminated(&self, var: Var) -> bool {
        self.var_status[&var].eliminated
    }

    pub fn is_frozen(&self, var: Var) -> bool {
        self.var_status[&var].frozen
    }
}
