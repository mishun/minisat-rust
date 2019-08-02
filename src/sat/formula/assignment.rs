use std::{cmp, fmt};
use super::{clause, LBool, Lit, Var};


#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct DecisionLevel(usize);

pub const GROUND_LEVEL: DecisionLevel = DecisionLevel(0);

impl DecisionLevel {
    pub fn offset(&self) -> usize {
        self.0
    }
}


pub struct VarData {
    pub reason: Option<clause::ClauseRef>,
    pub level: DecisionLevel,
}


struct VarLine {
    assign: [LBool; 2],
    vd: VarData,
}


pub struct Assignment {
    assignment: Vec<VarLine>,
    free_vars: Vec<Var>,
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
            assign: [LBool::Undef, LBool::Undef],
            vd: VarData {
                reason: None,
                level: GROUND_LEVEL,
            },
        };

        match self.free_vars.pop() {
            Some(var) => {
                self.assignment[var.index()] = line;
                var
            }

            None => {
                self.assignment.push(line);
                Var::from_index(self.assignment.len() - 1)
            }
        }
    }

    pub fn free_var(&mut self, v: Var) {
        // TODO: check that it's actually free
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
    pub fn assign_lit(&mut self, lit: Lit, reason: Option<clause::ClauseRef>) {
        let line = unsafe { self.assignment.get_unchecked_mut(lit.var_index()) };

        assert!(line.assign[0].is_undef());
        line.assign[lit.sign_index()] = LBool::True;
        line.assign[lit.sign_index() ^ 1] = LBool::False;
        line.vd.level = DecisionLevel(self.lim.len());
        line.vd.reason = reason;
        self.trail.push(lit);
    }

    #[inline]
    pub fn rewind_until_level<F>(&mut self, target_level: DecisionLevel, mut f: F)
        where F: FnMut(DecisionLevel, Lit) -> ()
    {
        while self.lim.len() > target_level.0 {
            let level = self.trail.len();
            let bottom = self.lim.pop().unwrap();
            while self.trail.len() > bottom {
                let lit = self.trail.pop().unwrap();

                f(DecisionLevel(level), lit);

                let ref mut line = self.assignment[lit.var_index()];
                line.assign = [LBool::Undef, LBool::Undef];
                line.vd.reason = None;
            }
        }

        self.qhead = cmp::min(self.qhead, self.trail.len());
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


    pub fn trail(&self) -> &[Lit] {
        &self.trail[..]
    }

    pub fn trail_at(&self, level: DecisionLevel) -> &[Lit] {
        assert!(level.0 <= self.lim.len());

        let head = if level.0 == 0 { 0 } else { self.lim[level.0 - 1] };
        if level.0 < self.lim.len() {
            let tail = self.lim[level.0];
            &self.trail[head..tail]
        } else {
            &self.trail[head..]
        }
    }

    pub fn trail_above(&self, level: DecisionLevel) -> &[Lit] {
        if level.0 < self.lim.len() {
            let head = self.lim[level.0];
            &self.trail[head..]
        } else {
            &[]
        }
    }


    #[inline]
    pub fn is_undef(&self, var: Var) -> bool {
        let ref line = self.assignment[var.index()];
        line.assign[0].is_undef()
    }

    #[inline]
    pub fn is_assigned_pos(&self, p: Lit) -> bool {
        unsafe {
            p.is_pos_at(self.assignment.get_unchecked(p.var_index()).assign[0])
        }
    }

    #[inline]
    pub fn is_assigned_neg(&self, p: Lit) -> bool {
        unsafe {
            p.is_neg_at(self.assignment.get_unchecked(p.var_index()).assign[0])
        }
    }

    #[inline]
    pub fn of_lit(&self, lit: Lit) -> LBool {
        unsafe {
            *self.assignment
                .get_unchecked(lit.var_index())
                .assign
                .get_unchecked(lit.sign_index())
        }
    }

    #[inline]
    pub fn vardata(&self, lit: Lit) -> &VarData {
        let ref line = unsafe { self.assignment.get_unchecked(lit.var_index()) };
        assert_eq!(line.assign[lit.sign_index()], LBool::False);
        &line.vd
    }


    pub fn reloc_gc(&mut self, from: &mut clause::ClauseAllocator, to: &mut clause::ClauseAllocator) {
        for lit in self.trail.iter() {
            let ref mut reason = self.assignment[lit.var_index()].vd.reason;
            *reason = reason.and_then(|cr| from.reloc_to(to, cr));
        }
    }

    pub fn is_locked(&self, ca: &clause::ClauseAllocator, cr: clause::ClauseRef) -> bool {
        let lit = ca.view(cr).head[0];
        let line = unsafe { self.assignment.get_unchecked(lit.var_index()) };

        if let LBool::True = line.assign[lit.sign_index()] {
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


pub fn try_assign_lit(assigns: &mut Assignment, p: Lit, from: Option<clause::ClauseRef>) -> bool {
    match assigns.of_lit(p) {
        LBool::True => true,
        LBool::False => false,
        LBool::Undef => {
            assigns.assign_lit(p, from);
            true
        }
    }
}
