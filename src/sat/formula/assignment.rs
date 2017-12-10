use std::{cmp, fmt};
use super::{Lit, Var};
use super::clause;


#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct DecisionLevel(usize);

pub const GROUND_LEVEL: DecisionLevel = DecisionLevel(0);

impl DecisionLevel {
    pub fn offset(&self) -> usize {
        self.0
    }
}


#[derive(PartialEq, Eq, Clone, Copy, Debug)]
#[repr(u8)]
pub enum LitVal {
    Undef,
    False,
    True,
}

impl LitVal {
    #[inline]
    fn is_undef(&self) -> bool {
        match *self {
            LitVal::Undef => true,
            _ => false,
        }
    }
}


pub struct VarData {
    pub reason: Option<clause::ClauseRef>,
    pub level: DecisionLevel,
}


struct VarLine {
    assign: [LitVal; 2],
    vd: VarData,
}


pub struct Assignment {
    assignment: Vec<VarLine>,
    free_vars: Vec<usize>,
    trail: Vec<Lit>,
    lim: Vec<usize>,
    qhead: usize,
}

impl Assignment {
    pub fn new() -> Assignment {
        Assignment {
            assignment: Vec::new(),
            free_vars: Vec::new(),
            trail: Vec::new(),
            lim: Vec::new(),
            qhead: 0,
        }
    }


    #[inline]
    pub fn number_of_vars(&self) -> usize {
        self.assignment.len()
    }

    #[inline]
    pub fn number_of_assigns(&self) -> usize {
        self.trail.len()
    }

    #[inline]
    pub fn number_of_ground_assigns(&self) -> usize {
        match self.lim.first() {
            Some(&lim) => lim,
            None => self.trail.len(),
        }
    }


    pub fn new_var(&mut self) -> Var {
        let line = VarLine {
            assign: [LitVal::Undef, LitVal::Undef],
            vd: VarData {
                reason: None,
                level: GROUND_LEVEL,
            },
        };
        let vid = match self.free_vars.pop() {
            Some(v) => {
                self.assignment[v] = line;
                v
            }

            None => {
                self.assignment.push(line);
                self.assignment.len() - 1
            }
        };

        Var(vid)
    }

    pub fn free_var(&mut self, Var(v): Var) {
        self.free_vars.push(v);
    }


    #[inline]
    pub fn decision_level(&self) -> DecisionLevel {
        DecisionLevel(self.lim.len())
    }

    #[inline]
    pub fn is_ground_level(&self) -> bool {
        self.lim.is_empty()
    }

    #[inline]
    pub fn new_decision_level(&mut self) {
        self.lim.push(self.trail.len());
    }


    #[inline]
    pub fn assign_lit(&mut self, Lit(p): Lit, reason: Option<clause::ClauseRef>) {
        let line = unsafe { self.assignment.get_unchecked_mut(p >> 1) };

        assert!(line.assign[0].is_undef());
        line.assign[p & 1] = LitVal::True;
        line.assign[(p & 1) ^ 1] = LitVal::False;
        line.vd.level = DecisionLevel(self.lim.len());
        line.vd.reason = reason;
        self.trail.push(Lit(p));
    }

    #[inline]
    pub fn rewrite_lit(&mut self, Lit(p): Lit) {
        let ref mut line = self.assignment[p >> 1];
        line.assign[p & 1] = LitVal::True;
        line.assign[(p & 1) ^ 1] = LitVal::False;
    }

    #[inline]
    pub fn rewind_until_level<F: FnMut(DecisionLevel, Lit) -> ()>(
        &mut self,
        DecisionLevel(target_level): DecisionLevel,
        mut f: F,
    ) {
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
    pub fn inspect_until_level<F: FnMut(Lit) -> ()>(
        &self,
        DecisionLevel(target_level): DecisionLevel,
        mut f: F,
    ) {
        if self.lim.len() > target_level {
            for &lit in self.trail[self.lim[target_level]..].iter().rev() {
                f(lit);
            }
        }
    }

    #[inline]
    pub fn retain_assignments<F: Fn(&Lit) -> bool>(&mut self, f: F) {
        assert!(self.is_ground_level());
        self.trail.retain(f); // TODO: what to do with assigned values?
        self.qhead = self.trail.len();
    }


    #[inline]
    pub fn dequeue_all(&mut self) {
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
    pub fn assign_at(&self, index: usize) -> Lit {
        self.trail[index]
    }


    #[inline]
    pub fn is_undef(&self, Var(v): Var) -> bool {
        let ref line = self.assignment[v];
        line.assign[0].is_undef()
    }

    #[inline]
    pub fn is_assigned_pos(&self, p: Lit) -> bool {
        match self.of_lit(p) {
            LitVal::True => true,
            _ => false,
        }
    }

    #[inline]
    pub fn is_assigned_neg(&self, p: Lit) -> bool {
        match self.of_lit(p) {
            LitVal::False => true,
            _ => false,
        }
    }

    #[inline]
    pub fn of_lit(&self, Lit(p): Lit) -> LitVal {
        unsafe {
            *self.assignment
                .get_unchecked(p >> 1)
                .assign
                .get_unchecked(p & 1)
        }
    }

    #[inline]
    pub fn vardata(&self, Lit(p): Lit) -> &VarData {
        let ref line = unsafe { self.assignment.get_unchecked(p >> 1) };
        assert_eq!(line.assign[p & 1], LitVal::False);
        &line.vd
    }


    pub fn reloc_gc(
        &mut self,
        from: &mut clause::ClauseAllocator,
        to: &mut clause::ClauseAllocator,
    ) {
        for &Lit(p) in self.trail.iter() {
            let ref mut reason = self.assignment[p >> 1].vd.reason;
            *reason = reason.and_then(|cr| from.reloc_to(to, cr));
        }
    }

    pub fn is_locked(&self, ca: &clause::ClauseAllocator, cr: clause::ClauseRef) -> bool {
        let Lit(p) = ca.view(cr).head();
        let ref line = unsafe { self.assignment.get_unchecked(p >> 1) };

        if let LitVal::True = line.assign[p & 1] {
            line.vd.reason == Some(cr)
        } else {
            false
        }
    }
}

impl fmt::Debug for Assignment {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for level in 0..1 + self.lim.len() {
            let l = if level > 0 { self.lim[level - 1] } else { 0 };
            let r = if level < self.lim.len() {
                self.lim[level]
            } else {
                self.trail.len()
            };

            if r > l {
                write!(f, "[{}:", level)?;
                for lit in self.trail[l..r].iter() {
                    write!(f, " {:?}", lit)?;
                }
                write!(f, " ]")?;
            }
        }

        Ok(())
    }
}


pub fn progress_estimate(assigns: &Assignment) -> f64 {
    let f = 1.0 / (assigns.number_of_vars() as f64);
    let mut progress = 0.0;

    let cl = assigns.lim.len();
    for level in 0..cl + 1 {
        let l = if level == 0 {
            0
        } else {
            assigns.lim[level - 1]
        };
        let r = if level == cl {
            assigns.trail.len()
        } else {
            assigns.lim[level]
        };
        progress += f.powi(level as i32) * ((r - l) as f64);
    }
    progress * f
}


pub fn extract_model(assigns: &Assignment) -> Vec<Lit> {
    let mut model = Vec::new();
    for i in 0..assigns.assignment.len() {
        let v = Var(i);
        match assigns.assignment[i].assign[0] {
            LitVal::Undef => {}
            LitVal::False => {
                model.push(v.neg_lit());
            }
            LitVal::True => {
                model.push(v.pos_lit());
            }
        }
    }
    model
}


pub fn try_assign_lit(assigns: &mut Assignment, p: Lit, from: Option<clause::ClauseRef>) -> bool {
    match assigns.of_lit(p) {
        LitVal::True => true,
        LitVal::False => false,
        LitVal::Undef => {
            assigns.assign_lit(p, from);
            true
        }
    }
}
