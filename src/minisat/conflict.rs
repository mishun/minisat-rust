use super::index_map::IndexMap;
use super::literal::{Var, Lit};
use super::clause::*;
use super::propagation_trail::*;
use super::assignment::*;
use super::clause_db::*;
use super::decision_heuristic::*;


#[derive(PartialEq, Eq)]
pub enum CCMinMode { None, Basic, Deep }


#[derive(PartialEq, Eq)]
#[repr(u8)]
pub enum Seen {
    Undef     = 0,
    Source    = 1,
    Removable = 2,
    Failed    = 3
}


pub struct AnalyzeContext {
    ccmin_mode       : CCMinMode,    // Controls conflict clause minimization
    pub seen         : IndexMap<Var, Seen>,
    analyze_toclear  : Vec<Lit>,
    pub max_literals : u64,
    pub tot_literals : u64
}

impl AnalyzeContext {
    pub fn new(ccmin_mode : CCMinMode) -> AnalyzeContext {
        AnalyzeContext { ccmin_mode      : ccmin_mode
                       , seen            : IndexMap::new()
                       , analyze_toclear : Vec::new()
                       , max_literals    : 0
                       , tot_literals    : 0
                       }
    }

    pub fn initVar(&mut self, v : Var) {
        self.seen.insert(&v, Seen::Undef);
    }

    // Description:
    //   Analyze conflict and produce a reason clause.
    //
    //   Pre-conditions:
    //     * 'out_learnt' is assumed to be cleared.
    //     * Current decision level must be greater than root level.
    //
    //   Post-conditions:
    //     * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
    //     * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the
    //       rest of literals. There may be others from the same level though.
    //
    pub fn analyze(&mut self, db : &mut ClauseDB, heur : &mut DecisionHeuristic, assigns : &Assignment, trail : &PropagationTrail<Lit>, confl_param : ClauseRef) -> (DecisionLevel, Vec<Lit>) {
        assert!(trail.decisionLevel() > 0);
        // Generate conflict clause:
        let mut out_learnt = Vec::new();

        {
            let mut pathC = 0i32;
            let mut p = None;
            let mut index = trail.totalSize();
            let mut confl = Some(confl_param);

            loop {
                assert!(confl.is_some()); // (otherwise should be UIP)
                db.bumpActivity(confl.unwrap());

                let ref c = db.ca[confl.unwrap()];

                for j in match p { None => 0, Some(_) => 1 } .. c.len() {
                    let q = c[j];
                    let v = q.var();

                    if self.seen[&v] == Seen::Undef && assigns.vardata(v).level > 0 {
                        heur.bumpActivity(v);

                        self.seen[&v] = Seen::Source;
                        if assigns.vardata(v).level >= trail.decisionLevel() {
                            pathC += 1;
                        } else {
                            out_learnt.push(q);
                        }
                    }
                }

                // Select next clause to look at:
                loop {
                    index -= 1;
                    if self.seen[&trail[index].var()] != Seen::Undef { break; }
                }
                let pl = trail[index];
                confl = assigns.vardata(pl.var()).reason;
                self.seen[&pl.var()] = Seen::Undef;
                p = Some(pl);

                pathC -= 1;
                if pathC <= 0 { break; }
            }

            out_learnt.insert(0, !p.unwrap());
        }


        // Simplify conflict clause:
        self.analyze_toclear = out_learnt.clone();
        {
            self.max_literals += out_learnt.len() as u64;

            match self.ccmin_mode {
                CCMinMode::Deep  => {
                    let mut j = 1;
                    for i in 1 .. out_learnt.len() {
                        let l = out_learnt[i];
                        if assigns.vardata(l.var()).reason.is_none() || !self.litRedundant(db, assigns, l) {
                            out_learnt[j] = out_learnt[i];
                            j += 1;
                        }
                    }
                    out_learnt.truncate(j);
                }

                CCMinMode::Basic => {
                    let mut j = 1;
                    for i in 1 .. out_learnt.len() {
                        let x = out_learnt[i].var();
                        match assigns.vardata(x).reason {
                            None     => { out_learnt[j] = out_learnt[i]; j += 1; }
                            Some(cr) => {
                                let ref c = db.ca[cr];
                                for k in 1 .. c.len() {
                                    let y = c[k].var();
                                    if self.seen[&y] == Seen::Undef && assigns.vardata(y).level > 0 {
                                        out_learnt[j] = out_learnt[i];
                                        j += 1;
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    out_learnt.truncate(j);
                }

                CCMinMode::None  => {}
            }

            self.tot_literals += out_learnt.len() as u64;
        }

        // Find correct backtrack level:
        let out_btlevel =
            if out_learnt.len() == 1 {
                0
            } else {
                // Find the first literal assigned at the next-highest level:
                let mut max_i = 1;
                let mut max_level = assigns.vardata(out_learnt[1].var()).level;
                for i in 2 .. out_learnt.len() {
                    let level = assigns.vardata(out_learnt[i].var()).level;
                    if level > max_level {
                        max_i = i;
                        max_level = level;
                    }
                }

                // Swap-in this literal at index 1:
                out_learnt.swap(1, max_i);
                max_level
            };

        for l in self.analyze_toclear.iter() {
            self.seen[&l.var()] = Seen::Undef;    // ('seen[]' is now cleared)
        }

        (out_btlevel, out_learnt)
    }

    // Check if 'p' can be removed from a conflict clause.
    fn litRedundant(&mut self, db : &ClauseDB, assigns : &Assignment, mut p : Lit) -> bool {
        assert!(self.seen[&p.var()] == Seen::Undef || self.seen[&p.var()] == Seen::Source);

        let mut stack = Vec::new();
        let mut i = 0;
        loop {
            i += 1;

            assert!(assigns.vardata(p.var()).reason.is_some());
            let ref c = db.ca[assigns.vardata(p.var()).reason.unwrap()];

            if i < c.len() {
                // Checking 'p'-parents 'l':
                let l = c[i];

                // Variable at level 0 or previously removable:
                if assigns.vardata(l.var()).level == 0 || self.seen[&l.var()] == Seen::Source || self.seen[&l.var()] == Seen::Removable {
                    continue;
                }

                // Check variable can not be removed for some local reason:
                if assigns.vardata(l.var()).reason.is_none() || self.seen[&l.var()] == Seen::Failed {
                    stack.push((0, p));
                    for &(_, l) in stack.iter() {
                        if self.seen[&l.var()] == Seen::Undef {
                            self.seen[&l.var()] = Seen::Failed;
                            self.analyze_toclear.push(l);
                        }
                    }
                    return false;
                }

                // Recursively check 'l':
                stack.push((i, p));
                i  = 0;
                p  = l;
            } else {
                // Finished with current element 'p' and reason 'c':
                if self.seen[&p.var()] == Seen::Undef {
                    self.seen[&p.var()] = Seen::Removable;
                    self.analyze_toclear.push(p);
                }

                match stack.pop() {
                    None           => { break; } // Terminate with success if stack is empty:
                    Some((ni, nl)) => {
                        // Continue with top element on stack:
                        i = ni;
                        p = nl;
                    }
                }
            }
        }

        true
    }

    // Description:
    //   Specialized analysis procedure to express the final conflict in terms of assumptions.
    //   Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
    //   stores the result in 'out_conflict'.
    pub fn analyzeFinal(&mut self, db : &ClauseDB, assigns : &Assignment, trail : &PropagationTrail<Lit>, p : Lit) -> IndexMap<Lit, ()> {
        let mut out_conflict = IndexMap::new();
        out_conflict.insert(&p, ());

        trail.inspectAssignmentsUntilLevel(0, |lit| {
            let x = lit.var();
            if self.seen[&x] != Seen::Undef {
                match assigns.vardata(x).reason {
                    None     => {
                        assert!(assigns.vardata(x).level > 0);
                        out_conflict.insert(&!lit, ());
                    }

                    Some(cr) => {
                        let ref c = db.ca[cr];
                        for j in 1 .. c.len() {
                            let v = c[j].var();
                            if assigns.vardata(v).level > 0 {
                                self.seen[&v] = Seen::Source;
                            }
                        }
                    }
                }
            }
        });

        out_conflict
    }
}
