use std::ops;


#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct DecisionLevel(usize);

pub const GroundLevel : DecisionLevel = DecisionLevel(0);

impl DecisionLevel {
    pub fn offset(&self) -> usize {
        let DecisionLevel(level) = *self;
        level
    }
}


pub struct PropagationTrail<V> {
    qhead     : usize,
    pub trail : Vec<V>,
    lim       : Vec<usize>
}

impl<V> PropagationTrail<V> {
    pub fn new() -> PropagationTrail<V> {
        PropagationTrail {
            qhead : 0,
            trail : Vec::new(),
            lim   : Vec::new()
        }
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
    pub fn push(&mut self, v : V) {
        self.trail.push(v);
    }

    #[inline]
    pub fn dequeueAll(&mut self) {
        self.qhead = self.trail.len()
    }

    #[inline]
    pub fn retain<F : Fn(&V) -> bool>(&mut self, f : F) {
        assert!(self.isGroundLevel());
        self.trail.retain(f);
        self.qhead = self.trail.len();
    }

    #[inline]
    pub fn cancelUntil<F : FnMut(DecisionLevel, V) -> ()>(&mut self, DecisionLevel(target_level) : DecisionLevel, mut f : F) {
        while self.lim.len() > target_level {
            let level = self.trail.len();
            let bottom = self.lim.pop().unwrap();
            while self.trail.len() > bottom {
                let v = self.trail.pop().unwrap();
                f(DecisionLevel(level), v);
            }
        }

        self.qhead = self.trail.len();
    }

    #[inline]
    pub fn totalSize(&self) -> usize {
        self.trail.len()
    }

    pub fn levelSize(&self, DecisionLevel(level) : DecisionLevel) -> usize {
        let cl = self.lim.len();
        if level > cl {
            0
        } else {
            let l = if level == 0 { 0 } else { self.lim[level - 1] };
            let r = if level == cl { self.trail.len() } else { self.lim[level] };
            r - l
        }
    }
}

impl<V : Clone> PropagationTrail<V> {
    #[inline]
    pub fn dequeue(&mut self) -> Option<V> {
        if self.qhead < self.trail.len() {
            let p = self.trail[self.qhead].clone();
            self.qhead += 1;
            Some(p)
        } else {
            None
        }
    }

    #[inline]
    pub fn inspectAssignmentsUntilLevel<F : FnMut(V) -> ()>(&self, DecisionLevel(target_level) : DecisionLevel, mut f : F) {
        if self.lim.len() > target_level {
            for i in (self.lim[target_level] .. self.trail.len()).rev() {
                f(self.trail[i].clone());
            }
        }
    }
}

impl<V> ops::Index<usize> for PropagationTrail<V> {
    type Output = V;

    #[inline]
    fn index(&self, index : usize) -> &V {
        self.trail.index(index)
    }
}


pub fn progressEstimate<X>(vars : usize, trail : &PropagationTrail<X>) -> f64 {
    let F = 1.0 / (vars as f64);
    let mut progress = 0.0;
    let DecisionLevel(up) = trail.decisionLevel();
    for i in 0 .. up + 1 {
        progress += F.powi(i as i32) * (trail.levelSize(DecisionLevel(i)) as f64);
    }
    progress * F
}
