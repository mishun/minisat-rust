use super::index_map::{HasIndex};
use super::literal::{Var, Lit};
use super::lbool::{LBool};


pub struct Assignment {
    assigns   : Vec<LBool>,
    free_vars : Vec<uint>,
}

impl Assignment {
    pub fn new() -> Assignment {
        Assignment {
            assigns   : Vec::new(),
            free_vars : Vec::new(),
        }
    }

    #[inline]
    pub fn nVars(&self) -> uint {
        self.assigns.len()
    }

    pub fn newVar(&mut self) -> Var {
        let v =
            match self.free_vars.pop() {
                Some(v) => {
                    self.assigns[v] = LBool::Undef();
                    v
                }

                None    => {
                    self.assigns.push(LBool::Undef());
                    self.assigns.len() - 1
                }
            };
        Var::new(v)
    }

    pub fn freeVar(&mut self, v : &Var) {
        self.free_vars.push(v.toIndex());
    }

    #[inline]
    pub fn assignLit(&mut self, p : Lit) {
        let i = p.var().toIndex();
        assert!(self.assigns[i].isUndef());
        self.assigns[i] = LBool::new(!p.sign());
    }

    #[inline]
    pub fn cancel(&mut self, x : Var) {
        self.assigns[x.toIndex()] = LBool::Undef();
    }

    #[inline]
    pub fn undef(&self, x : Var) -> bool {
        self.assigns[x.toIndex()].isUndef()
    }

    #[inline]
    pub fn sat(&self, p : Lit) -> bool {
        self.ofLit(p).isTrue()
    }

    #[inline]
    pub fn unsat(&self, p : Lit) -> bool {
        self.ofLit(p).isFalse()
    }

    #[inline]
    pub fn ofVar(&self, x : Var) -> LBool {
        self.assigns[x.toIndex()]
    }

    #[inline]
    pub fn ofLit(&self, p : Lit) -> LBool {
        self.assigns[p.var().toIndex()] ^ p.sign()
    }
}

