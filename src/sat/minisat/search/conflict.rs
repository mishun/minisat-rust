use sat::formula::{Var, Lit, VarMap, LitMap};
use sat::formula::clause::*;
use sat::formula::assignment::*;


#[derive(PartialEq, Eq)]
pub enum CCMinMode {
    None,
    Basic,
    Deep
}

impl Default for CCMinMode {
    fn default() -> Self {
        CCMinMode::Deep
    }
}


#[derive(PartialEq, Eq, Clone, Copy, Debug)]
#[repr(u8)]
enum Seen {
    Undef     = 0,
    Source    = 1,
    Removable = 2,
    Failed    = 3
}


pub enum Conflict {
    Ground,
    Unit(DecisionLevel, Lit),
    Learned(DecisionLevel, Lit, Box<[Lit]>)
}


pub struct AnalyzeContext {
    ccmin_mode       : CCMinMode,    // Controls conflict clause minimization
    seen             : VarMap<Seen>,
    analyze_toclear  : Vec<Lit>,
    pub max_literals : u64,
    pub tot_literals : u64
}

impl AnalyzeContext {
    pub fn new(ccmin_mode : CCMinMode) -> AnalyzeContext {
        AnalyzeContext { ccmin_mode      : ccmin_mode
                       , seen            : VarMap::new()
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
    pub fn analyze<BV, BC>(&mut self, assigns : &Assignment, ca : &mut ClauseAllocator, confl0 : ClauseRef, mut bumpVar : BV, mut bumpCla : BC) -> Conflict
        where BV : FnMut(Var) -> (), BC : FnMut(&mut ClauseAllocator, ClauseRef) -> () {
        if assigns.isGroundLevel() {
            return Conflict::Ground;
        }

        // Generate conflict clause:
        let mut out_learnt = Vec::new();

        {
            let mut confl = confl0;
            let mut pathC = 0;
            let mut index = assigns.numberOfAssigns();
            loop {
                bumpCla(ca, confl);

                for &q in ca.view(confl).litsFrom(if confl == confl0 { 0 } else { 1 }) {
                    let v = q.var();
                    if self.seen[&v] == Seen::Undef {
                        let level = assigns.vardata(q).level;
                        if level > GroundLevel {
                            self.seen[&v] = Seen::Source;
                            bumpVar(v);
                            if level >= assigns.decisionLevel() {
                                pathC += 1;
                            } else {
                                out_learnt.push(q);
                            }
                        }
                    }
                }

                // Select next clause to look at:
                let pl = {
                    loop {
                        index -= 1;
                        if self.seen[&assigns.assignAt(index).var()] != Seen::Undef { break; }
                    }
                    assigns.assignAt(index)
                };

                self.seen[&pl.var()] = Seen::Undef;

                pathC -= 1;
                if pathC <= 0 {
                    out_learnt.insert(0, !pl);
                    break;
                }

                confl = assigns.vardata(!pl).reason.unwrap();
            }
        }


        // Simplify conflict clause:
        self.analyze_toclear = out_learnt.clone();
        self.max_literals += out_learnt.len() as u64;
        match self.ccmin_mode {
            CCMinMode::Deep  => { out_learnt.retain(|&l| { !self.litRedundant(ca, assigns, l) }); }
            CCMinMode::Basic => { out_learnt.retain(|&l| { !self.litRedundantBasic(ca, assigns, l) }); }
            CCMinMode::None  => {}
        }
        self.tot_literals += out_learnt.len() as u64;

        for l in self.analyze_toclear.iter() {
            self.seen[&l.var()] = Seen::Undef;    // ('seen[]' is now cleared)
        }

        // Find correct backtrack level:
        if out_learnt.len() == 1 {
            Conflict::Unit(GroundLevel, out_learnt[0])
        } else {
            // Find the first literal assigned at the next-highest level:
            let mut max_i = 1;
            let mut max_level = assigns.vardata(out_learnt[1]).level;
            for i in 2 .. out_learnt.len() {
                let level = assigns.vardata(out_learnt[i]).level;
                if level > max_level {
                    max_i = i;
                    max_level = level;
                }
            }

            // Swap-in this literal at index 1:
            out_learnt.swap(1, max_i);
            Conflict::Learned(max_level, out_learnt[0], out_learnt.into_boxed_slice())
        }
    }

    fn litRedundantBasic(&self, ca : &ClauseAllocator, assigns : &Assignment, literal : Lit) -> bool {
        match assigns.vardata(literal).reason {
            None     => { false }
            Some(cr) => {
                for &lit in ca.view(cr).litsFrom(1) {
                    if self.seen[&lit.var()] == Seen::Undef && assigns.vardata(lit).level > GroundLevel {
                        return false;
                    }
                }
                true
            }
        }
    }

    // Check if 'p' can be removed from a conflict clause.
    fn litRedundant(&mut self, ca : &ClauseAllocator, assigns : &Assignment, literal : Lit) -> bool {
        assert!({ let s = self.seen[&literal.var()]; s == Seen::Undef || s == Seen::Source });

        let mut analyze_stack =
            match assigns.vardata(literal).reason {
                None     => { return false; }
                Some(cr) => { vec![(literal, ca.view(cr).litsFrom(1))] }
            };

        while let Some((p, lits)) = analyze_stack.pop() {
            match lits.split_first() {
                Some((&l, tail)) => {
                    analyze_stack.push((p, tail));
                    let ref vd = assigns.vardata(l);
                    let seen = self.seen[&l.var()];

                    // Variable at level 0 or previously removable:
                    if vd.level == GroundLevel || seen == Seen::Source || seen == Seen::Removable {
                        continue;
                    }

                    match vd.reason {
                        // Recursively check 'l':
                        Some(cr) if seen == Seen::Undef => {
                            analyze_stack.push((l, ca.view(cr).litsFrom(1)));
                        }

                        // Check variable can not be removed for some local reason:
                        _                                => {
                            for &(l, _) in analyze_stack.iter() {
                                if self.seen[&l.var()] == Seen::Undef {
                                    self.seen[&l.var()] = Seen::Failed;
                                    self.analyze_toclear.push(l);
                                }
                            }
                            return false;
                        }
                    }
                }

                None             => {
                    // Finished with current element 'p' and reason 'c':
                    if self.seen[&p.var()] == Seen::Undef {
                        self.seen[&p.var()] = Seen::Removable;
                        self.analyze_toclear.push(p);
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
    pub fn analyzeFinal(&mut self, ca : &ClauseAllocator, assigns : &Assignment, p : Lit) -> LitMap<()> {
        let mut out_conflict = LitMap::new();
        out_conflict.insert(&p, ());

        assigns.inspectUntilLevel(GroundLevel, |lit| {
            if self.seen[&lit.var()] != Seen::Undef {
                match assigns.vardata(lit).reason {
                    None     => {
                        assert!(assigns.vardata(lit).level > GroundLevel);
                        out_conflict.insert(&!lit, ());
                    }

                    Some(cr) => {
                        for &lit in ca.view(cr).litsFrom(1) {
                            if assigns.vardata(lit).level > GroundLevel {
                                self.seen[&lit.var()] = Seen::Source;
                            }
                        }
                    }
                }
            }
        });

        out_conflict
    }
}
