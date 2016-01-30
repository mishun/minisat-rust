use super::index_map::HasIndex;
use super::literal::{Var, Lit};
use super::lbool::*;
use super::clause;
use super::propagation_trail::*;


struct VarData {
    pub reason : Option<clause::ClauseRef>,
    pub level  : DecisionLevel
}


struct VarLine {
    assign : LBool,
    vd     : VarData
}


pub struct Assignment {
    assignment : Vec<VarLine>,
    free_vars  : Vec<usize>
}

impl Assignment {
    pub fn new() -> Assignment {
        Assignment { assignment : Vec::new()
                   , free_vars  : Vec::new()
                   }
    }

    #[inline]
    pub fn nVars(&self) -> usize {
        self.assignment.len()
    }

    pub fn newVar(&mut self) -> Var {
        let line = VarLine { assign : LBool::Undef(), vd : VarData { reason : None, level : 0 } };
        let vid =
            match self.free_vars.pop() {
                Some(v) => {
                    self.assignment[v] = line;
                    v
                }

                None    => {
                    self.assignment.push(line);
                    self.assignment.len() - 1
                }
            };

        Var::new(vid)
    }

    pub fn freeVar(&mut self, v : &Var) {
        self.free_vars.push(v.toIndex());
    }

    pub fn forgetReason(&mut self, ca : &clause::ClauseAllocator, cr : clause::ClauseRef) {
        // Don't leave pointers to free'd memory!
        if isLocked(ca, self, cr) {
            let ref mut line = self.assignment[ca[cr][0].var().toIndex()];
            assert!(!line.assign.isUndef());
            line.vd.reason = None;
        }
    }

    #[inline]
    pub fn vardata(&self, v : Var) -> &VarData {
        let ref line = self.assignment[v.toIndex()];
        assert!(!line.assign.isUndef());
        &line.vd
    }

    #[inline]
    pub fn assignLit(&mut self, p : Lit, level : DecisionLevel, reason : Option<clause::ClauseRef>) {
        let ref mut line = self.assignment[p.var().toIndex()];
        assert!(line.assign.isUndef());
        line.assign = LBool::new(!p.sign());
        line.vd.level = level;
        line.vd.reason = reason;
    }

    #[inline]
    pub fn cancel(&mut self, x : Var) {
        let ref mut line = self.assignment[x.toIndex()];
        line.assign = LBool::Undef();
    }

    #[inline]
    pub fn undef(&self, x : Var) -> bool {
        let ref line = self.assignment[x.toIndex()];
        line.assign.isUndef()
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
    pub fn ofLit(&self, p : Lit) -> LBool {
        let ref line = self.assignment[p.var().toIndex()];
        line.assign ^ p.sign()
    }

    pub fn extractModel(&self) -> Vec<Option<bool>> {
        let mut model = Vec::with_capacity(self.assignment.len());
        for line in self.assignment.iter() {
            model.push(if line.assign.isUndef() { None } else { Some(line.assign.isTrue()) });
        }
        model
    }

    pub fn relocGC(&mut self, trail : &PropagationTrail<Lit>, from : &mut clause::ClauseAllocator, to : &mut clause::ClauseAllocator) {
        for l in trail.trail.iter() {
            let v = l.var();

            // Note: it is not safe to call 'locked()' on a relocated clause. This is why we keep
            // 'dangling' reasons here. It is safe and does not hurt.
            match self.assignment[v.toIndex()].vd.reason {
                Some(cr) if from[cr].reloced() || isLocked(from, self, cr) => {
                    assert!(!from[cr].is_deleted());
                    self.assignment[v.toIndex()].vd.reason = Some(from.relocTo(to, cr));
                }

                _ => {}
            }
        }
    }
}


// Returns TRUE if a clause is satisfied in the current state.
pub fn satisfiedWith(c : &clause::Clause, s : &Assignment) -> bool {
    for i in 0 .. c.len() {
        if s.sat(c[i]) {
            return true;
        }
    }
    false
}


pub fn isLocked(ca : &clause::ClauseAllocator, assigns : &Assignment, cr : clause::ClauseRef) -> bool {
    let lit = ca[cr][0];
    if !assigns.sat(lit) { return false; }
    match assigns.vardata(lit.var()).reason {
        Some(r) if cr == r => { true }
        _                  => { false }
    }
}
