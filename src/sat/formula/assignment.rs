use std::{cmp, fmt};
use super::{clause::*, LBool, Lit, Var};


type LevelIndex = usize;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct DecisionLevel(LevelIndex);

pub const GROUND_LEVEL: DecisionLevel = DecisionLevel(1);

impl DecisionLevel {
    pub fn is_ground(&self) -> bool {
        self.0 == 1
    }

    pub fn offset_from_ground(&self) -> usize {
        (self.0 - 1) as usize
    }
}


pub struct VarData {
    pub reason: Option<ClauseRef>,
    pub level: DecisionLevel,
}

pub struct Assignment {
    assign: Vec<LBool>,
    vd: Vec<VarData>,
    free_vars: Vec<Var>,
    trail: Vec<Lit>,
    lim: Vec<usize>,
    qhead: usize,
}

impl Assignment {
    pub fn new() -> Assignment {
        Assignment {
            assign: Vec::new(),
            vd: Vec::new(),
            free_vars: Vec::new(),
            trail: Vec::new(),
            lim: vec![0],
            qhead: 0,
        }
    }


    pub fn new_var(&mut self) -> Var {
        let vd = VarData { reason: None, level: GROUND_LEVEL };
        match self.free_vars.pop() {
            Some(var) => {
                self.assign[var.index()] = LBool::Undef;
                self.vd[var.index()] = vd;
                var
            }

            None => {
                let vi = self.assign.len();
                self.assign.push(LBool::Undef);
                self.vd.push(vd);
                Var::from_index(vi)
            }
        }
    }

    pub fn free_var(&mut self, v: Var) {
        // TODO: check that it's actually free
        self.free_vars.push(v);
    }


    pub fn current_level(&self) -> DecisionLevel {
        DecisionLevel(self.lim.len())
    }

    pub fn is_ground_level(&self) -> bool {
        self.current_level().is_ground()
    }

    pub fn number_of_vars(&self) -> usize {
        self.assign.len()
    }

    pub fn number_of_assigns(&self) -> usize {
        self.trail.len()
    }

    pub fn number_of_ground_assigns(&self) -> usize {
        match self.lim.get(1) {
            Some(&lim) => lim,
            None => self.trail.len(),
        }
    }


    #[inline]
    pub fn new_decision_level(&mut self) {
        self.lim.push(self.trail.len());
    }

    #[inline]
    pub fn assign_lit(&mut self, lit: Lit, reason: Option<ClauseRef>) {
        unsafe {
            let val = self.assign.get_unchecked_mut(lit.var_index());
            assert!(val.is_undef());
            *val = lit.pos_assignment();
            *self.vd.get_unchecked_mut(lit.var_index()) =
                VarData { reason: reason, level: DecisionLevel(self.lim.len()) };
            self.trail.push(lit);
        }
    }

    // Revert to the state at given level (keeping all assignment at 'level' but not beyond).
    pub fn backtrack_to(&mut self, target_level: DecisionLevel) {
        if let Some(&target) = self.lim.get(target_level.0) {
            for &lit in &self.trail[target..] {
                unsafe {
                    *self.assign.get_unchecked_mut(lit.var_index()) = LBool::Undef;
                    self.vd.get_unchecked_mut(lit.var_index()).reason = None;
                }
            }

            self.trail.truncate(target);
            self.lim.truncate(target_level.0);
        }

        self.qhead = cmp::min(self.qhead, self.trail.len());
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
        let head = self.lim[level.0 - 1];
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
    pub fn all_levels_dir(&self) -> DirIter {
        DirIter {
            assign: self,
            target: self.lim.len(),
            level: 1
        }
    }

    #[inline]
    pub fn levels_above_rev(&self, target_level: DecisionLevel) -> RevIter {
        RevIter {
            assign: self,
            target: target_level.0,
            level: self.lim.len()
        }
    }


    #[inline]
    pub fn is_undef(&self, var: Var) -> bool {
        unsafe {
            self.assign.get_unchecked(var.index()).is_undef()
        }
    }

    #[inline]
    pub fn is_assigned_pos(&self, p: Lit) -> bool {
        unsafe {
            p.is_pos_at(*self.assign.get_unchecked(p.var_index()))
        }
    }

    #[inline]
    pub fn is_assigned_neg(&self, p: Lit) -> bool {
        unsafe {
            p.is_neg_at(*self.assign.get_unchecked(p.var_index()))
        }
    }

    #[inline]
    pub fn of_lit(&self, p: Lit) -> LBool {
        unsafe {
            p.apply_sign(*self.assign.get_unchecked(p.var_index()))
        }
    }


    #[inline]
    pub fn vardata(&self, lit: Lit) -> &VarData {
        unsafe {
            assert!(lit.is_neg_at(*self.assign.get_unchecked(lit.var_index())));
            self.vd.get_unchecked(lit.var_index())
        }
    }

    pub fn is_reason_for(&self, cr: ClauseRef, lit: Lit) -> bool {
        unsafe {
            if lit.is_pos_at(*self.assign.get_unchecked(lit.var_index())) {
                self.vd.get_unchecked(lit.var_index()).reason == Some(cr)
            } else {
                false
            }
        }
    }


    pub fn gc(&mut self, gc: &mut ClauseGC) {
        unsafe {
            for lit in self.trail.iter() {
                let ref mut reason = self.vd.get_unchecked_mut(lit.var_index()).reason;
                *reason = reason.and_then(|cr| gc.relocate(cr));
            }
        }
    }
}

impl fmt::Debug for Assignment {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (level, level_trail) in self.all_levels_dir() {
            if level.is_ground() || level_trail.len() > 0 {
                if level.is_ground() {
                    write!(f, "[GROUND:")?;
                } else {
                    write!(f, "[{}:", level.offset_from_ground())?;
                }
                for lit in level_trail {
                    write!(f, " {:?}", lit)?;
                }
                write!(f, " ]")?;
            }
        }
        Ok(())
    }
}


pub struct DirIter<'a> {
    assign: &'a Assignment,
    target: usize,
    level: usize
}

impl<'a> Iterator for DirIter<'a> {
    type Item = (DecisionLevel, &'a [Lit]);

    #[inline]
    fn next(&mut self) -> Option<(DecisionLevel, &'a[Lit])> {
        if self.level <= self.target {
            let level = self.level;
            self.level += 1;

            let head = self.assign.lim[level - 1];
            if level < self.assign.lim.len() {
                let tail = self.assign.lim[level];
                Some((DecisionLevel(level), &self.assign.trail[head..tail]))
            } else {
                Some((DecisionLevel(level), &self.assign.trail[head..]))
            }
        } else {
            None
        }
    }
}


pub struct RevIter<'a> {
    assign: &'a Assignment,
    target: usize,
    level: usize
}

impl<'a> Iterator for RevIter<'a> {
    type Item = (DecisionLevel, &'a[Lit]);

    #[inline]
    fn next(&mut self) -> Option<(DecisionLevel, &'a[Lit])> {
        if self.level > self.target {
            let level = self.level;
            self.level -= 1;

            let head = self.assign.lim[level - 1];
            if level < self.assign.lim.len() {
                let tail = self.assign.lim[level];
                Some((DecisionLevel(level), &self.assign.trail[head..tail]))
            } else {
                Some((DecisionLevel(level), &self.assign.trail[head..]))
            }
        } else {
            None
        }
    }
}
