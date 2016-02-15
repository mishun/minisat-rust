use sat::formula::{Var, Lit, VarMap, VarHeap};
use sat::formula::assignment::Assignment;
use super::util;


#[derive(PartialEq, Eq)]
pub enum PhaseSaving { None, Limited, Full }


pub struct DecisionHeuristicSettings {
    pub var_decay       : f64,
    pub random_seed     : f64,
    pub random_var_freq : f64,
    pub phase_saving    : PhaseSaving, // Controls the level of phase saving
    pub rnd_pol         : bool,        // Use random polarities for branching heuristics.
    pub rnd_init_act    : bool,        // Initialize variable activities with a small random value.
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


#[derive(Debug)]
struct VarLine {
    polarity : bool,         // The preferred polarity of each variable.
    user_pol : Option<bool>, // The users preferred polarity of each variable.
    decision : bool          // Declares if a variable is eligible for selection in the decision heuristic.
}

pub struct DecisionHeuristic {
    settings          : DecisionHeuristicSettings,
    var_inc           : f64,                         // Amount to bump next variable with.
    rand              : util::Random,
    var               : VarMap<VarLine>,
    activity          : VarMap<f64>,
    queue             : VarHeap,                     // A priority queue of variables ordered with respect to the variable activity.

    pub dec_vars      : usize,
    pub rnd_decisions : u64
}

impl DecisionHeuristic {
    pub fn new(settings : DecisionHeuristicSettings) -> DecisionHeuristic {
        let seed = settings.random_seed;
        DecisionHeuristic { settings      : settings
                          , var_inc       : 1.0
                          , rand          : util::Random::new(seed)
                          , var           : VarMap::new()
                          , activity      : VarMap::new()
                          , queue         : VarHeap::new()
                          , dec_vars      : 0
                          , rnd_decisions : 0
                          }
    }

    pub fn initVar(&mut self, v : Var, upol : Option<bool>, dvar : bool) {
        self.activity.insert(&v, if self.settings.rnd_init_act { self.rand.drand() * 0.00001 } else { 0.0 });
        self.var.insert(&v, VarLine { polarity : true, user_pol : upol, decision : false });
        self.setDecisionVar(v, dvar);
    }

    pub fn setDecisionVar(&mut self, v : Var, b : bool) {
        let ref mut ln = self.var[&v];
        if b != ln.decision {
            if b {
                self.dec_vars += 1;
                let ref act = self.activity;
                self.queue.insert(v, |a, b| { act[a] > act[b] });
            } else {
                self.dec_vars -= 1;
            }
            ln.decision = b;
        }
    }

    pub fn cancel(&mut self, lit : Lit, top_level : bool) {
        let ref mut ln = self.var[&lit.var()];
        match self.settings.phase_saving {
            PhaseSaving::Full                 => { ln.polarity = lit.sign(); }
            PhaseSaving::Limited if top_level => { ln.polarity = lit.sign(); }
            _                                 => {}
        }
        if ln.decision {
            let ref act = self.activity;
            self.queue.insert(lit.var(), |a, b| { act[a] > act[b] });
        }
    }

    pub fn bumpActivity(&mut self, v : &Var) {
        let new = self.activity[v] + self.var_inc;
        if new > 1e100 {
            self.var_inc *= 1e-100;
            for (_, act) in self.activity.iter_mut() {
                *act *= 1e-100;
            }
            self.activity[v] = new * 1e-100;
        } else {
            self.activity[v] = new;
        }

        let ref act = self.activity;
        self.queue.update(v, |a, b| { act[a] > act[b] });
    }

    pub fn decayActivity(&mut self) {
        self.var_inc *= 1.0 / self.settings.var_decay;
    }

    pub fn rebuildOrderHeap(&mut self, assigns : &Assignment) {
        let mut tmp = Vec::with_capacity(self.queue.len());
        for (v, vl) in self.var.iter() {
            if vl.decision && assigns.isUndef(v) {
                tmp.push(v);
            }
        }

        let ref act = self.activity;
        self.queue.heapifyFrom(tmp, |a, b| { act[a] > act[b] });
    }

    fn pickBranchVar(&mut self, assigns : &Assignment) -> Option<Var> {
        // Random decision:
        if self.rand.chance(self.settings.random_var_freq) && !self.queue.is_empty() {
            let v = self.queue[self.rand.irand(self.queue.len())];
            if assigns.isUndef(v) && self.var[&v].decision {
                self.rnd_decisions += 1;
                return Some(v);
            }
        }

        // Activity based decision:
        while let Some(v) = { let ref act = self.activity; self.queue.pop(|a, b| { act[a] > act[b] }) } {
            if assigns.isUndef(v) && self.var[&v].decision {
                return Some(v);
            }
        }

        None
    }

    pub fn pickBranchLit(&mut self, assigns : &Assignment) -> Option<Lit> {
        // Choose polarity based on different polarity modes (global or per-variable):
        self.pickBranchVar(assigns).map(|v| {
            let ref ln = self.var[&v];
            let s = match ln.user_pol {
                Some(s)                       => { s }
                None if self.settings.rnd_pol => { self.rand.chance(0.5) }
                None                          => { ln.polarity }
            };
            v.lit(s)
        })
    }
}
