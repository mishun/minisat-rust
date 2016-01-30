use std::ops;

pub type DecisionLevel = usize;

pub struct PropagationTrail<V> {
    qhead     : usize,
    pub trail : Vec<V>,
    pub lim   : Vec<usize>
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
        self.lim.len()
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
    pub fn cancelUntil<F : FnMut(DecisionLevel, V) -> ()>(&mut self, target_level : DecisionLevel, mut f : F) {
        while self.lim.len() > target_level {
            let level = self.trail.len();
            let bottom = self.lim.pop().unwrap();
            while self.trail.len() > bottom {
                let v = self.trail.pop().unwrap();
                f(level, v);
            }
        }

        self.qhead = self.trail.len();
    }

    #[inline]
    pub fn totalSize(&self) -> usize {
        self.trail.len()
    }

    pub fn levelSize(&self, level : DecisionLevel) -> usize {
        let cl = self.decisionLevel();
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
}

impl<V> ops::Index<usize> for PropagationTrail<V> {
    type Output = V;

    #[inline]
    fn index(&self, index : usize) -> &V {
        self.trail.index(index)
    }
}
