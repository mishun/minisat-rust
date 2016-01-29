use std::ops;
use super::index_map::{HasIndex, IndexMap};
use super::random;
use super::literal::{Var, Lit};
use super::lbool::LBool;
use super::assignment::*;


#[derive(PartialEq, Eq, Clone, Copy)]
pub enum PhaseSaving { None, Limited, Full }


#[derive(Clone, Copy)]
pub struct DecisionHeuristicSettings {
    pub var_decay         : f64,
    pub random_seed       : f64,
    pub random_var_freq   : f64,
    pub phase_saving      : PhaseSaving, // Controls the level of phase saving
    pub rnd_pol           : bool,        // Use random polarities for branching heuristics.
    pub rnd_init_act      : bool,        // Initialize variable activities with a small random value.
}

impl Default for DecisionHeuristicSettings {
    fn default() -> DecisionHeuristicSettings {
        DecisionHeuristicSettings { var_decay         : 0.95
                                  , random_seed       : 91648253.0
                                  , random_var_freq   : 0.0
                                  , phase_saving      : PhaseSaving::Full
                                  , rnd_pol           : false
                                  , rnd_init_act      : false
                                  }
    }
}


pub struct DecisionHeuristic {
    settings          : DecisionHeuristicSettings,
    var_inc           : f64,                         // Amount to bump next variable with.
    rand              : random::Random,
    polarity          : IndexMap<Var, bool>,         // The preferred polarity of each variable.
    user_pol          : IndexMap<Var, LBool>,        // The users preferred polarity of each variable.
    decision          : IndexMap<Var, bool>,         // Declares if a variable is eligible for selection in the decision heuristic.
    activity_queue    : ActivityQueue<Var>,          // A priority queue of variables ordered with respect to the variable activity.

    pub dec_vars      : usize,
    pub rnd_decisions : u64
}

impl DecisionHeuristic {
    pub fn new(settings : DecisionHeuristicSettings) -> DecisionHeuristic {
        DecisionHeuristic { settings       : settings
                          , var_inc        : 1.0
                          , rand           : random::Random::new(settings.random_seed)
                          , polarity       : IndexMap::new()
                          , user_pol       : IndexMap::new()
                          , decision       : IndexMap::new()
                          , activity_queue : ActivityQueue::new()
                          , dec_vars       : 0
                          , rnd_decisions  : 0
                          }
    }

    pub fn initVar(&mut self, v : Var, upol : LBool, dvar : bool) {
        self.activity_queue.setActivity(&v,
            if self.settings.rnd_init_act {
                self.rand.drand() * 0.00001
            } else {
                0.0
            });
        self.polarity.insert(&v, true);
        self.user_pol.insert(&v, upol);
        self.decision.insert(&v, false);
        self.setDecisionVar(v, dvar);
    }

    pub fn cancel(&mut self, lit : Lit, top_level : bool) {
        let x = lit.var();
        match self.settings.phase_saving {
            PhaseSaving::Full                 => { self.polarity[&x] = lit.sign(); }
            PhaseSaving::Limited if top_level => { self.polarity[&x] = lit.sign(); }
            _                                 => {}
        }
        if self.decision[&x] {
            self.activity_queue.insert(x);
        }
    }

    pub fn bumpActivity(&mut self, v : Var) {
        let new = self.activity_queue.getActivity(&v) + self.var_inc;
        if new > 1e100 {
            self.var_inc *= 1e-100;
            self.activity_queue.scaleActivity(1e-100);
            self.activity_queue.setActivity(&v, new * 1e-100);
        } else {
            self.activity_queue.setActivity(&v, new);
        }
    }

    pub fn decayActivity(&mut self) {
        self.var_inc *= 1.0 / self.settings.var_decay;
    }

    pub fn setDecisionVar(&mut self, v : Var, b : bool) {
        let pb = self.decision[&v];
        if b != pb {
            if b {
                self.dec_vars += 1;
                self.activity_queue.insert(v);
            } else {
                self.dec_vars -= 1;
            }
            self.decision[&v] = b;
        }
    }

    pub fn rebuildOrderHeap(&mut self, assigns : &Assignment) {
        let mut tmp = Vec::new();
        for vi in 0 .. assigns.nVars() {
            let v = Var::new(vi);
            if self.decision[&v] && assigns.undef(v) {
                tmp.push(v);
            }
        }
        self.activity_queue.heapifyFrom(tmp);
    }

    fn pickBranchVar(&mut self, assigns : &Assignment) -> Option<Var> {
        // Random decision:
        if self.rand.chance(self.settings.random_var_freq) && !self.activity_queue.is_empty() {
            let v = self.activity_queue[self.rand.irand(self.activity_queue.len())];
            if assigns.undef(v) && self.decision[&v] {
                self.rnd_decisions += 1;
                return Some(v);
            }
        }

        // Activity based decision:
        while let Some(v) = self.activity_queue.pop() {
            if assigns.undef(v) && self.decision[&v] {
                return Some(v);
            }
        }

        None
    }

    pub fn pickBranchLit(&mut self, assigns : &Assignment) -> Option<Lit> {
        // Choose polarity based on different polarity modes (global or per-variable):
        self.pickBranchVar(assigns).map(|v| {
            if !self.user_pol[&v].isUndef() {
                Lit::new(v, self.user_pol[&v].isTrue())
            } else if self.settings.rnd_pol {
                Lit::new(v, self.rand.chance(0.5))
            } else {
                Lit::new(v, self.polarity[&v])
            }
        })
    }

    // Insert a variable in the decision order priority queue.
//    fn insertVarOrder(&mut self, x : Var) {
//        if self.decision[&x] {
//            self.activity_queue.insert(x);
//        }
//    }
}


struct ActivityQueue<V : HasIndex> {
    heap     : Vec<V>,
    indices  : IndexMap<V, usize>,
    activity : IndexMap<V, f64>,
}

impl<V : HasIndex> ActivityQueue<V> {
    pub fn new() -> ActivityQueue<V> {
        ActivityQueue {
            heap     : Vec::new(),
            indices  : IndexMap::new(),
            activity : IndexMap::new(),
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.heap.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    #[inline]
    pub fn contains(&self, v : &V) -> bool {
        self.indices.contains_key(v)
    }

    #[inline]
    pub fn getActivity(&self, v : &V) -> f64 {
        self.activity[v]
    }

    pub fn scaleActivity(&mut self, factor : f64) {
        self.activity.modify_in_place(|act| { *act *= factor });
    }
}

impl<V : HasIndex + Clone> ActivityQueue<V> {
    pub fn setActivity(&mut self, v : &V, new : f64) {
        match self.activity.insert(v, new) {
            None      => {}
            Some(old) => {
                if self.indices.contains_key(v) {
                    let i = self.indices[v];
                    if new > old { self.sift_up(i) } else { self.sift_down(i) }
                }
            }
        }
    }

    pub fn insert(&mut self, v : V) {
        if !self.contains(&v) {
            if !self.activity.contains_key(&v) {
                self.activity.insert(&v, 0.0);
            }

            let i = self.heap.len();
            self.indices.insert(&v, i);
            self.heap.push(v);
            self.sift_up(i);
        }
    }

    pub fn pop(&mut self) -> Option<V>
    {
        match self.heap.len() {
            0 => { None }
            1 => {
                let h = self.heap.pop().unwrap();
                self.indices.remove(&h);
                Some(h)
            }
            _ => {
                let h = self.heap[0].clone();
                self.indices.remove(&h);

                let t = self.heap.pop().unwrap();
                self.set(0, t);

                self.sift_down(0);
                Some(h)
            }
        }
    }

    pub fn heapifyFrom(&mut self, from : Vec<V>) {
        self.heap = from;
        self.indices.clear();
        for i in 0 .. self.heap.len() {
            self.indices.insert(&self.heap[i], i);
        }

        for i in (0 .. self.heap.len() / 2).rev() {
            self.sift_down(i);
        }
    }


    fn sift_up(&mut self, mut i : usize) {
        let x = self.heap[i].clone();
        while i > 0 {
            let pi = (i - 1) >> 1;
            let p = self.heap[pi].clone();
            if self.activity[&x] > self.activity[&p] {
                self.set(i, p);
                i = pi;
            } else {
                break
            }
        }
        self.set(i, x);
    }

    fn sift_down(&mut self, mut i : usize) {
        let x = self.heap[i].clone();
        let len = self.heap.len();
        loop {
            let li = i + i + 1;
            if li >= len { break; }
            let ri = i + i + 2;
            let ci = if ri < len && self.activity[&self.heap[ri]] > self.activity[&self.heap[li]] { ri } else { li };
            let c = self.heap[ci].clone();
            if self.activity[&c] <= self.activity[&x] { break; }
            self.set(i, c);
            i = ci;
        }
        self.set(i, x);
    }

    #[inline]
    fn set(&mut self, i : usize, v : V) {
        self.indices.insert(&v, i);
        self.heap[i] = v;
    }
}

impl<V : HasIndex> ops::Index<usize> for ActivityQueue<V> {
    type Output = V;

    #[inline]
    fn index(&self, i : usize) -> &V {
        self.heap.index(i)
    }
}
