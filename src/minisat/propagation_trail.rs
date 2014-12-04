
pub struct PropagationTrail<V> {
    pub qhead : uint,
    pub trail : Vec<V>,
    pub lim   : Vec<uint>,
}

impl<V> PropagationTrail<V> {
    pub fn new() -> PropagationTrail<V> {
        PropagationTrail {
            qhead : 0,
            trail : Vec::new(),
            lim   : Vec::new(),
        }
    }

    #[inline]
    pub fn totalSize(&self) -> uint {
        self.trail.len()
    }

    #[inline]
    pub fn levelSize(&self, level : uint) -> uint {
        let cl = self.decisionLevel();
        if level > cl {
            0
        } else {
            let l = if level == 0 { 0 } else { self.lim[level - 1] };
            let r = if level == cl { self.trail.len() } else { self.lim[level] };
            r - l
        }
    }

    #[inline]
    pub fn decisionLevel(&self) -> uint {
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
    pub fn retain(&mut self, f : |&V| -> bool) {
        assert!(self.isGroundLevel());
        self.trail.retain(f);
        self.qhead = self.trail.len();
    }

/*
    #[inline]
    pub fn popUntilLevel(&mut self, level : uint) {
        if self.decisionLevel() > level {
            let level_lim = self.lim[level];
            self.qhead = level_lim;
            self.trail.truncate(level_lim);
            self.lim.truncate(level);
        }
    }

    #[inline]
    pub fn iterFromLevel(&self, level : uint) -> TrailIterator<V> {
        let start = if level == 0 { 0 } else { self.lim[level - 1] };
        TrailIterator { owner : self, index : start }
    }

    #[inline]
    pub fn iter(&self) -> TrailIterator<V> {
        TrailIterator { owner : self, index : 0 }
    }
*/
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

impl<V> Index<uint, V> for PropagationTrail<V> {
    #[inline]
    fn index(&self, index : &uint) -> &V {
        self.trail.index(index)
    }
}

/*
struct TrailIterator<'t, V: 't> {
    owner : &'t PropagationTrail<V>,
    index : uint,
}

impl<'t, V> Iterator<&'t V> for TrailIterator<'t, V> {
    #[inline]
    fn next(&mut self) -> Option<&'t V> {
        if self.index < self.owner.trail.len() {
            let v = &self.owner.trail[self.index];
            self.index += 1;
            Some(v)
        } else {
            None
        }
    }
}
*/
