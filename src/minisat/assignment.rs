use super::index_map::{HasIndex, IndexMap};
use super::clause;
use super::literal::{Var, Lit};
use super::lbool::*;
use super::clause::Clause;
use super::propagation_trail::DecisionLevel;


pub struct VarData {
    pub reason : Option<clause::ClauseRef>,
    pub level  : DecisionLevel
}


pub struct Assignment {
    assigns     : Vec<LBool>,
    free_vars   : Vec<usize>,
    pub vardata : IndexMap<Var, VarData>
}

impl Assignment {
    pub fn new() -> Assignment {
        Assignment {
            assigns   : Vec::new(),
            free_vars : Vec::new(),
            vardata   : IndexMap::new()
        }
    }

    #[inline]
    pub fn nVars(&self) -> usize {
        self.assigns.len()
    }

    pub fn newVar(&mut self, vd : VarData) -> Var {
        let vid =
            match self.free_vars.pop() {
                Some(vid) => {
                    self.assigns[vid] = LBool::Undef();
                    vid
                }

                None    => {
                    self.assigns.push(LBool::Undef());
                    self.assigns.len() - 1
                }
            };
        let v = Var::new(vid);
        self.vardata.insert(&v, vd);
        v
    }

    pub fn freeVar(&mut self, v : &Var) {
        self.free_vars.push(v.toIndex());
    }

    #[inline]
    pub fn assignLit(&mut self, p : Lit, vd : VarData) {
        let i = p.var().toIndex();
        assert!(self.assigns[i].isUndef());
        self.assigns[i] = LBool::new(!p.sign());
        self.vardata.insert(&p.var(), vd);
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
    pub fn ofVar(&self, x : Var) -> Option<bool> {
        let b = self.assigns[x.toIndex()];
        if b.isUndef() { None } else { Some(b.isTrue()) }
    }

    #[inline]
    pub fn ofLit(&self, p : Lit) -> LBool {
        self.assigns[p.var().toIndex()] ^ p.sign()
    }
}


// Returns TRUE if a clause is satisfied in the current state.
pub fn satisfiedWith(c : &Clause, s : &Assignment) -> bool {
    for i in 0 .. c.len() {
        if s.sat(c[i]) {
            return true;
        }
    }
    false
}
