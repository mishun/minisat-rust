use sat::formula::{Var, Lit, VarMap, LitMap, VarHeap};
use sat::formula::assignment::Assignment;


pub struct VarStatus {
    pub frozen     : i8,
    pub eliminated : i8
}


pub struct ElimQueue {
    heap  : VarHeap,
    n_occ : LitMap<i32>
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
        self.heap.insert(v, |a, b| { Self::before(n_occ, a, b) });
    }

    #[inline]
    fn before(n_occ : &LitMap<i32>, a : &Var, b : &Var) -> bool {
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
            self.heap.update(&v, |a, b| { Self::before(n_occ, a, b) });
        } else if var_status[&v].frozen == 0 && var_status[&v].eliminated == 0 && assigns.isUndef(v) {
            self.heap.insert(v, |a, b| { Self::before(n_occ, a, b) });
        }
    }

    pub fn clear(&mut self) {
        self.heap.clear();
    }

    pub fn bumpLitOcc(&mut self, lit : &Lit, delta : i32) {
        self.n_occ[lit] += delta;

        let ref n_occ = self.n_occ;
        self.heap.update(&lit.var(), |a, b| { Self::before(n_occ, a, b) });
    }

    pub fn pop(&mut self) -> Option<Var>
    {
        let ref n_occ = self.n_occ;
        self.heap.pop(|a, b| { Self::before(n_occ, a, b) })
    }
}
