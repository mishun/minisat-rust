use std::{cmp, fmt};
use super::{clause, LBool, Lit, Var};


type LevelIndex = usize;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct DecisionLevel(LevelIndex);

pub const GROUND_LEVEL: DecisionLevel = DecisionLevel(0);

impl DecisionLevel {
    pub fn offset(&self) -> usize {
        self.0 as usize
    }
}


pub struct DecisionLevelUpIter {
    current: LevelIndex,
    bound: LevelIndex
}

impl Iterator for DecisionLevelUpIter {
    type Item = DecisionLevel;

    #[inline]
    fn next(&mut self) -> Option<DecisionLevel> {
        if self.current <= self.bound {
            let result = DecisionLevel(self.current);
            self.current += 1;
            Some(result)
        } else {
            None
        }
    }
}


pub struct BacktrackingIter<'a> {
    assign: &'a Assignment,
    target: usize,
    level: usize
}

impl<'a> Iterator for BacktrackingIter<'a> {
    type Item = (DecisionLevel, &'a[Lit]);

    #[inline]
    fn next(&mut self) -> Option<(DecisionLevel, &'a[Lit])> {
        if self.level > self.target {
            let level = self.level;
            self.level -= 1;

            let head = if level == 0 { 0 } else { self.assign.lim[level - 1] };
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


    pub fn current_level(&self) -> DecisionLevel {
        DecisionLevel(self.lim.len())
    }

    pub fn is_ground_level(&self) -> bool {
        self.lim.is_empty()
    }

    pub fn all_levels(&self) -> DecisionLevelUpIter {
        DecisionLevelUpIter { current: 0, bound: self.lim.len() }
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


    // Revert to the state at given level (keeping all assignment at 'level' but not beyond).
    pub fn backtrack_to(&mut self, target_level: DecisionLevel) {
        if target_level.0 < self.lim.len() {
            let target = self.lim[target_level.0];
            for &lit in &self.trail[target..] {
                let ref mut line = self.assignment[lit.var_index()];
                line.assign = [LBool::Undef, LBool::Undef];
                line.vd.reason = None;
            }

            self.trail.truncate(target);
            self.lim.truncate(target_level.0);
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
    pub fn trail_above_by_level(&self, target_level: DecisionLevel) -> BacktrackingIter {
        BacktrackingIter {
            assign: self,
            target: target_level.0,
            level: self.lim.len()
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
        for level in self.all_levels() {
            let level_trail = self.trail_at(level);
            if level_trail.len() > 0 {
                write!(f, "[{}:", level.offset())?;
                for lit in level_trail {
                    write!(f, " {:?}", lit)?;
                }
                write!(f, " ]")?;
            }
        }
        Ok(())
    }
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
