use crate::sat::formula::{assignment::*, clause::*, Lit, LitMap, Var, VarMap};


#[derive(PartialEq, Eq)]
pub enum CCMinMode {
    None,
    Basic,
    Deep,
}

impl Default for CCMinMode {
    fn default() -> Self {
        CCMinMode::Deep
    }
}


#[derive(PartialEq, Eq, Clone, Copy, Debug)]
#[repr(u8)]
enum Seen {
    Undef = 0,
    Source = 1,
    Removable = 2,
    Failed = 3,
}


pub enum Conflict {
    Ground,
    Unit(DecisionLevel, Lit),
    Learned(DecisionLevel, Lit, Vec<Lit>),
}


pub struct AnalyzeContext {
    ccmin_mode: CCMinMode, // Controls conflict clause minimization
    seen: VarMap<Seen>,
    analyze_toclear: Vec<Lit>,
    pub max_literals: u64,
    pub tot_literals: u64,
}

impl AnalyzeContext {
    pub fn new(ccmin_mode: CCMinMode) -> AnalyzeContext {
        AnalyzeContext {
            ccmin_mode,
            seen: VarMap::new(),
            analyze_toclear: Vec::new(),
            max_literals: 0,
            tot_literals: 0,
        }
    }

    pub fn init_var(&mut self, v: Var) {
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
    pub fn analyze<BV, BC>(
        &mut self,
        assigns: &Assignment,
        ca: &mut ClauseAllocator,
        confl0: ClauseRef,
        mut bump_var: BV,
        mut bump_cla: BC,
    ) -> Conflict
    where
        BV: FnMut(Var) -> (),
        BC: FnMut(&mut ClauseAllocator, ClauseRef) -> (),
    {
        if assigns.is_ground_level() {
            return Conflict::Ground;
        }

        // Generate conflict clause:
        let mut out_learnt = Vec::with_capacity(assigns.number_of_assigns());

        {
            let mut confl = confl0;
            let mut path_c = 0;

            let trail = assigns.trail();
            let mut index = trail.len();
            loop {
                bump_cla(ca, confl);

                let base = if confl == confl0 { 0 } else { 1 };
                for &q in &ca.view(confl).lits()[base..] {
                    let v = q.var();
                    if self.seen[&v] == Seen::Undef {
                        let level = assigns.vardata(q).level;
                        if level > GROUND_LEVEL {
                            self.seen[&v] = Seen::Source;
                            bump_var(v);
                            if level >= assigns.current_level() {
                                path_c += 1;
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
                        if self.seen[ &trail[index].var() ] != Seen::Undef {
                            break;
                        }
                    }
                    trail[index]
                };

                self.seen[&pl.var()] = Seen::Undef;

                path_c -= 1;
                if path_c <= 0 {
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
            CCMinMode::Deep => {
                out_learnt.retain(|&l| !self.lit_redundant(ca, assigns, l));
            }
            CCMinMode::Basic => {
                out_learnt.retain(|&l| !self.lit_redundant_basic(ca, assigns, l));
            }
            CCMinMode::None => {}
        }
        self.tot_literals += out_learnt.len() as u64;

        for l in self.analyze_toclear.iter() {
            self.seen[&l.var()] = Seen::Undef; // ('seen[]' is now cleared)
        }

        // Find correct backtrack level:
        if out_learnt.len() == 1 {
            Conflict::Unit(GROUND_LEVEL, out_learnt[0])
        } else {
            // Find the first literal assigned at the next-highest level:
            let mut max_i = 1;
            let mut max_level = assigns.vardata(out_learnt[1]).level;
            for i in 2..out_learnt.len() {
                let level = assigns.vardata(out_learnt[i]).level;
                if level > max_level {
                    max_i = i;
                    max_level = level;
                }
            }

            // Swap-in this literal at index 1:
            out_learnt.swap(1, max_i);
            Conflict::Learned(max_level, out_learnt[0], out_learnt)
        }
    }

    fn lit_redundant_basic(&self, ca: &ClauseAllocator, assigns: &Assignment, literal: Lit) -> bool {
        match assigns.vardata(literal).reason {
            None => false,
            Some(cr) => {
                for &lit in &ca.view(cr).lits()[1..] {
                    if self.seen[&lit.var()] == Seen::Undef
                        && assigns.vardata(lit).level > GROUND_LEVEL
                    {
                        return false;
                    }
                }
                true
            }
        }
    }

    // Check if 'p' can be removed from a conflict clause.
    fn lit_redundant(&mut self, ca: &ClauseAllocator, assigns: &Assignment, literal: Lit) -> bool {
        assert!({
            let s = self.seen[&literal.var()];
            s == Seen::Undef || s == Seen::Source
        });

        let mut analyze_stack =
            match assigns.vardata(literal).reason {
                None => return false,
                Some(cr) => vec![(literal, &ca.view(cr).lits()[1..])],
            };

        while let Some((p, lits)) = analyze_stack.pop() {
            match lits.split_first() {
                Some((&l, tail)) => {
                    analyze_stack.push((p, tail));
                    let ref vd = assigns.vardata(l);
                    let seen = self.seen[&l.var()];

                    // Variable at level 0 or previously removable:
                    if vd.level == GROUND_LEVEL || seen == Seen::Source || seen == Seen::Removable {
                        continue;
                    }

                    match vd.reason {
                        // Recursively check 'l':
                        Some(cr) if seen == Seen::Undef => {
                            analyze_stack.push((l, &ca.view(cr).lits()[1..]));
                        }

                        // Check variable can not be removed for some local reason:
                        _ => {
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

                None => {
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
    pub fn analyze_final(&mut self, ca: &ClauseAllocator, assigns: &Assignment, p: Lit) -> LitMap<()> {
        let mut out_conflict = LitMap::new();
        out_conflict.insert(&p, ());

        for &lit in assigns.trail_above(GROUND_LEVEL).iter().rev() {
            if self.seen[&lit.var()] != Seen::Undef {
                match assigns.vardata(lit).reason {
                    None => {
                        assert!(assigns.vardata(lit).level > GROUND_LEVEL);
                        out_conflict.insert(&!lit, ());
                    }

                    Some(cr) => {
                        for &lit in &ca.view(cr).lits()[1..] {
                            if assigns.vardata(lit).level > GROUND_LEVEL {
                                self.seen[&lit.var()] = Seen::Source;
                            }
                        }
                    }
                }
            }
        }

        out_conflict
    }
}
