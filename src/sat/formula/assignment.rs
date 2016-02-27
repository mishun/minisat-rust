use std::{cmp, fmt};
use super::{Var, Lit};
use super::clause;
use super::index_map::VarMap;


#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct DecisionLevel(usize);

pub const GroundLevel : DecisionLevel = DecisionLevel(0);

impl DecisionLevel {
    pub fn offset(&self) -> usize {
        self.0
    }
}


#[derive(Clone, Copy)]
#[repr(u8)]
pub enum LitVal { Undef, False, True }

impl LitVal {
    #[inline]
    fn isUndef(&self) -> bool {
        match *self {
            LitVal::Undef => { true }
            _             => { false }
        }
    }
}


pub struct VarData {
    pub reason : Option<clause::ClauseRef>,
    pub level  : DecisionLevel
}


struct VarLine {
    assign : [LitVal; 2],
    vd     : VarData
}


pub struct Assignment {
    assignment : Vec<VarLine>,
    free_vars  : Vec<usize>,
    trail      : Vec<Lit>,
    lim        : Vec<usize>,
    qhead      : usize
}

impl Assignment {
    pub fn new() -> Assignment {
        Assignment { assignment : Vec::new()
                   , free_vars  : Vec::new()
                   , trail      : Vec::new()
                   , lim        : Vec::new()
                   , qhead      : 0
                   }
    }


    #[inline]
    pub fn numberOfVars(&self) -> usize {
        self.assignment.len()
    }

    #[inline]
    pub fn numberOfAssigns(&self) -> usize {
        self.trail.len()
    }

    #[inline]
    pub fn numberOfGroundAssigns(&self) -> usize {
        match self.lim.first() {
            Some(&lim) => { lim }
            None       => { self.trail.len() }
        }
    }


    pub fn newVar(&mut self) -> Var {
        let line = VarLine { assign : [LitVal::Undef, LitVal::Undef]
                           , vd     : VarData { reason : None, level : GroundLevel }
                           };
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

        Var(vid)
    }

    pub fn freeVar(&mut self, Var(v) : Var) {
        self.free_vars.push(v);
    }


    #[inline]
    pub fn decisionLevel(&self) -> DecisionLevel {
        DecisionLevel(self.lim.len())
    }

    #[inline]
    pub fn isGroundLevel(&self) -> bool {
        self.lim.is_empty()
    }

    #[inline]
    pub fn newDecisionLevel(&mut self) {
        self.lim.push(self.trail.len());
    }


    #[inline]
    pub fn assignLit(&mut self, Lit(p) : Lit, reason : Option<clause::ClauseRef>) {
        let ref mut line = self.assignment[p >> 1];
        assert!(line.assign[0].isUndef());
        line.assign[p & 1]       = LitVal::True;
        line.assign[(p & 1) ^ 1] = LitVal::False;
        line.vd.level  = DecisionLevel(self.lim.len());
        line.vd.reason = reason;
        self.trail.push(Lit(p));
    }

    #[inline]
    pub fn rewindUntilLevel<F : FnMut(DecisionLevel, Lit) -> ()>(&mut self, DecisionLevel(target_level) : DecisionLevel, mut f : F) {
        while self.lim.len() > target_level {
            let level = self.trail.len();
            let bottom = self.lim.pop().unwrap();
            while self.trail.len() > bottom {
                let lit = self.trail.pop().unwrap();

                f(DecisionLevel(level), lit);

                let Var(v) = lit.var();
                let ref mut line = self.assignment[v];
                line.assign = [LitVal::Undef, LitVal::Undef];
                line.vd.reason = None;
            }
        }

        self.qhead = cmp::min(self.qhead, self.trail.len());
    }

    #[inline]
    pub fn inspectUntilLevel<F : FnMut(Lit) -> ()>(&self, DecisionLevel(target_level) : DecisionLevel, mut f : F) {
        if self.lim.len() > target_level {
            for i in (self.lim[target_level] .. self.trail.len()).rev() {
                f(self.trail[i]);
            }
        }
    }

    #[inline]
    pub fn retainAssignments<F : Fn(&Lit) -> bool>(&mut self, f : F) {
        assert!(self.isGroundLevel());
        self.trail.retain(f); // TODO: what to do with assigned values?
        self.qhead = self.trail.len();
    }


    #[inline]
    pub fn dequeueAll(&mut self) {
        self.qhead = self.trail.len()
    }

    #[inline]
    pub fn dequeue(&mut self) -> Option<Lit> {
        if self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            Some(p)
        } else {
            None
        }
    }

    #[inline]
    pub fn assignAt(&self, index : usize) -> Lit {
        self.trail[index]
    }


    #[inline]
    pub fn isUndef(&self, Var(v) : Var) -> bool {
        let ref line = self.assignment[v];
        line.assign[0].isUndef()
    }

    #[inline]
    pub fn isSat(&self, p : Lit) -> bool {
        match self.ofLit(p) {
            LitVal::True => { true }
            _            => { false }
        }
    }

    #[inline]
    pub fn isUnsat(&self, p : Lit) -> bool {
        match self.ofLit(p) {
            LitVal::False => { true }
            _             => { false }
        }
    }

    #[inline]
    pub fn ofLit(&self, Lit(p) : Lit) -> LitVal {
        let ref line = self.assignment[p >> 1];
        line.assign[p & 1]
    }

    #[inline]
    pub fn vardata(&self, Var(v) : Var) -> &VarData {
        let ref line = self.assignment[v];
        assert!(!line.assign[0].isUndef());
        &line.vd
    }


    pub fn relocGC(&mut self, from : &mut clause::ClauseAllocator, to : &mut clause::ClauseAllocator) {
        for l in self.trail.iter() {
            let Var(v) = l.var();

            // Note: it is not safe to call 'locked()' on a relocated clause. This is why we keep
            // 'dangling' reasons here. It is safe and does not hurt.
            match self.assignment[v].vd.reason {
                Some(cr) if from.view(cr).reloced() || self.isLocked(from, cr) => {
                    assert!(!from.isDeleted(cr));
                    self.assignment[v].vd.reason = Some(from.relocTo(to, cr));
                }

                _ => {}
            }
        }
    }

    pub fn isLocked(&self, ca : &clause::ClauseAllocator, cr : clause::ClauseRef) -> bool {
        let lit = ca.view(cr).head();
        if !self.isSat(lit) { return false; }
        match self.vardata(lit.var()).reason {
            Some(r) if cr == r => { true }
            _                  => { false }
        }
    }

    pub fn forgetReason(&mut self, ca : &clause::ClauseAllocator, cr : clause::ClauseRef) {
        // Don't leave pointers to free'd memory!
        if self.isLocked(ca, cr) {
            let Var(v) = ca.view(cr).head().var();
            self.assignment[v].vd.reason = None;
        }
    }
}

impl fmt::Debug for Assignment {
    fn fmt(&self, f : &mut fmt::Formatter) -> fmt::Result {
        for level in 0 .. 1 + self.lim.len() {
            let l = if level > 0 { self.lim[level - 1] } else { 0 };
            let r = if level < self.lim.len() { self.lim[level] } else { self.trail.len() };

            if r > l {
                try!(write!(f, "[{}:", level));
                for i in l .. r {
                    try!(write!(f, " {:?}", self.trail[i]));
                }
                try!(write!(f, " ]"));
            }
        }

        Ok(())
    }
}


pub fn progressEstimate(assigns : &Assignment) -> f64 {
    let F = 1.0 / (assigns.numberOfVars() as f64);
    let mut progress = 0.0;

    let cl = assigns.lim.len();
    for level in 0 .. cl + 1 {
        let l = if level == 0 { 0 } else { assigns.lim[level - 1] };
        let r = if level == cl { assigns.trail.len() } else { assigns.lim[level] };
        progress += F.powi(level as i32) * ((r - l) as f64);
    }
    progress * F
}


pub fn extractModel(assigns : &Assignment) -> VarMap<bool> {
    let mut model = VarMap::new();
    for i in 0 .. assigns.assignment.len() {
        match assigns.assignment[i].assign[0] {
            LitVal::Undef => {}
            LitVal::False => { model.insert(&Var(i), false); }
            LitVal::True  => { model.insert(&Var(i), true); }
        }
    }
    model
}


pub fn tryAssignLit(assigns : &mut Assignment, p : Lit, from : Option<clause::ClauseRef>) -> bool {
    match assigns.ofLit(p) {
        LitVal::True  => { true }
        LitVal::False => { false }
        LitVal::Undef => { assigns.assignLit(p, from); true }
    }
}
