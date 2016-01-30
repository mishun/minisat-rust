use super::index_map::HasIndex;
use super::literal::{Var, Lit};
use super::clause;
use super::propagation_trail::*;


#[derive(Clone, Copy)]
#[repr(u8)]
pub enum Value { Undef, False, True }

impl Value {
    #[inline]
    fn isUndef(&self) -> bool {
        match *self {
            Value::Undef => { true }
            _            => { false }
        }
    }

    fn extractBool(&self) -> Option<bool> {
        match *self {
            Value::Undef  => { None }
            Value::False  => { Some(false) }
            Value::True   => { Some(true) }
        }
    }
}


struct VarData {
    pub reason : Option<clause::ClauseRef>,
    pub level  : DecisionLevel
}


struct VarLine {
    assign : [Value; 2],
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
        let line = VarLine { assign : [Value::Undef, Value::Undef], vd : VarData { reason : None, level : 0 } };
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

    #[inline]
    pub fn assignLit(&mut self, p : Lit, level : DecisionLevel, reason : Option<clause::ClauseRef>) {
        let ref mut line = self.assignment[p.var().toIndex()];
        assert!(line.assign[0].isUndef());
        line.assign[p.sign() as usize] = Value::True;
        line.assign[(p.sign() as usize) ^ 1] = Value::False;
        line.vd.level = level;
        line.vd.reason = reason;
    }

    #[inline]
    pub fn cancel(&mut self, x : Var) {
        let ref mut line = self.assignment[x.toIndex()];
        line.assign = [Value::Undef, Value::Undef];
    }

    #[inline]
    pub fn undef(&self, x : Var) -> bool {
        let ref line = self.assignment[x.toIndex()];
        line.assign[0].isUndef()
    }

    #[inline]
    pub fn sat(&self, p : Lit) -> bool {
        match self.ofLit(p) {
            Value::True => { true }
            _           => { false }
        }
    }

    #[inline]
    pub fn unsat(&self, p : Lit) -> bool {
        match self.ofLit(p) {
            Value::False => { true }
            _            => { false }
        }
    }

    #[inline]
    pub fn ofLit(&self, p : Lit) -> Value {
        let ref line = self.assignment[p.var().toIndex()];
        line.assign[p.sign() as usize]
    }

    #[inline]
    pub fn vardata(&self, v : Var) -> &VarData {
        let ref line = self.assignment[v.toIndex()];
        assert!(!line.assign[0].isUndef());
        &line.vd
    }

    pub fn extractModel(&self) -> Vec<Option<bool>> {
        let mut model = Vec::with_capacity(self.assignment.len());
        for line in self.assignment.iter() {
            model.push(line.assign[0].extractBool());
        }
        model
    }

    pub fn relocGC(&mut self, trail : &PropagationTrail<Lit>, from : &mut clause::ClauseAllocator, to : &mut clause::ClauseAllocator) {
        for l in trail.trail.iter() {
            let v = l.var();

            // Note: it is not safe to call 'locked()' on a relocated clause. This is why we keep
            // 'dangling' reasons here. It is safe and does not hurt.
            match self.assignment[v.toIndex()].vd.reason {
                Some(cr) if from[cr].reloced() || self.isLocked(from, cr) => {
                    assert!(!from[cr].is_deleted());
                    self.assignment[v.toIndex()].vd.reason = Some(from.relocTo(to, cr));
                }

                _ => {}
            }
        }
    }

    pub fn isLocked(&self, ca : &clause::ClauseAllocator, cr : clause::ClauseRef) -> bool {
        let lit = ca[cr][0];
        if !self.sat(lit) { return false; }
        match self.vardata(lit.var()).reason {
            Some(r) if cr == r => { true }
            _                  => { false }
        }
    }

    pub fn forgetReason(&mut self, ca : &clause::ClauseAllocator, cr : clause::ClauseRef) {
        // Don't leave pointers to free'd memory!
        if self.isLocked(ca, cr) {
            let ref mut line = self.assignment[ca[cr][0].var().toIndex()];
            line.vd.reason = None;
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
