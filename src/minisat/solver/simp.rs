use std::default::{Default};
use std::collections::vec_deque::{VecDeque};
use std::mem;
use minisat::index_map::{IndexMap};
use minisat::lbool::{LBool};
use minisat::literal::{Var, Lit};
use minisat::clause::{Clause, ClauseRef};
use minisat::assignment::{Assignment};
use super::{Solver, CoreSolver};


struct SimpSettings {
    grow              : bool, // Allow a variable elimination step to grow by a number of clauses (default to zero).
    clause_lim        : i32,  // Variables are not eliminated if it produces a resolvent with a length above this limit. -1 means no limit.
    subsumption_lim   : i32,  // Do not check if subsumption against a clause larger than this. -1 means no limit.
    simp_garbage_frac : f64,  // A different limit for when to issue a GC during simplification (Also see 'garbage_frac').
    use_asymm         : bool, // Shrink clauses by asymmetric branching.
    use_rcheck        : bool, // Check if a clause is already implied. Prett costly, and subsumes subsumptions :)
    use_elim          : bool, // Perform variable elimination.
    extend_model      : bool, // Flag to indicate whether the user needs to look at the full model.
}

impl Default for SimpSettings {
    fn default() -> SimpSettings {
        SimpSettings {
            grow              : false,
            clause_lim        : 20,
            subsumption_lim   : 1000,
            simp_garbage_frac : 0.5,
            use_asymm         : false,
            use_rcheck        : false,
            use_elim          : true,
            extend_model      : true,
        }
    }
}


struct ElimQueue {
    heap    : Vec<Var>,
    indices : IndexMap<Var, usize>,
    n_occ   : IndexMap<Lit, i32>,
}

impl ElimQueue {
    pub fn new() -> ElimQueue {
        ElimQueue {
            heap    : Vec::new(),
            indices : IndexMap::new(),
            n_occ   : IndexMap::new()
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.heap.len()
    }

    #[inline]
    fn inHeap(&self, v : &Var) -> bool {
        self.indices.contains_key(v)
    }

    fn update(&mut self, v : Var) {
        if !self.inHeap(&v) {
            self.insert(v);
        } else {
            {
                let i = self.indices[&v];
                self.sift_up(i);
            }
            {
                let i = self.indices[&v];
                self.sift_down(i);
            }
        }
    }

    fn insert(&mut self, v : Var) {
        if !self.inHeap(&v) {
            let i = self.heap.len();
            self.indices.insert(&v, i);
            self.heap.push(v);
            self.sift_up(i);
        }
    }

    fn updateElimHeap(&mut self, v : &Var, frozen : &IndexMap<Var, i8>, eliminated : &IndexMap<Var, i8>, assigns : &Assignment) {
        if self.inHeap(&v) || (frozen[v] == 0 && eliminated[v] == 0 && assigns.undef(*v)) {
            self.update(*v);
        }
    }

//    pub fn clear(&mut self) {
//        self.heap.clear();
//        self.indices.clear();
//    }

    pub fn bumpLitOcc(&mut self, lit : &Lit, delta : i32) {
        self.n_occ[lit] += delta;
        if self.inHeap(&lit.var()) {
            self.update(lit.var());
        }
    }

    pub fn addVar(&mut self, v : Var) {
        self.n_occ.insert(&Lit::new(v, false), 0);
        self.n_occ.insert(&Lit::new(v, true ), 0);
        self.insert(v);
    }

    pub fn pop(&mut self) -> Option<Var>
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

    fn cost(&self, x : Var) -> u64 {
        (self.n_occ[&Lit::new(x, false)] as u64) * (self.n_occ[&Lit::new(x, true)] as u64)
    }

    fn sift_up(&mut self, mut i : usize) {
        let x = self.heap[i].clone();
        while i > 0 {
            let pi = (i - 1) >> 1;
            let p = self.heap[pi].clone();
            if self.cost(x) < self.cost(p) {
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
            let ci = if ri < len && self.cost(self.heap[ri]) < self.cost(self.heap[li]) { ri } else { li };
            let c = self.heap[ci].clone();
            if self.cost(c) >= self.cost(x) { break; }
            self.set(i, c);
            i = ci;
        }
        self.set(i, x);
    }

    #[inline]
    fn set(&mut self, i : usize, v : Var) {
            self.indices.insert(&v, i);
            self.heap[i] = v;
    }
}



pub struct SimpSolver {
    core               : CoreSolver,
    set                : SimpSettings,

    // Statistics:
    merges             : i32,
    asymm_lits         : i32,
    eliminated_vars    : i32,

    // Solver state:
    elimorder          : i32,
    use_simplification : bool,
    max_simp_var       : Var,        // Max variable at the point simplification was turned off.
    elimclauses        : Vec<u32>,
    touched            : IndexMap<Var, i8>,

    // TODO: OccLists<Var, vec<CRef>, ClauseDeleted> occurs;
    elim               : ElimQueue,
    subsumption_queue  : VecDeque<ClauseRef>,
    frozen             : IndexMap<Var, i8>,
    frozen_vars        : Vec<Var>,
    eliminated         : IndexMap<Var, i8>,
    bwdsub_assigns     : i32,
    n_touched          : i32,

    // Temporaries:
    bwdsub_tmpunit     : ClauseRef,
}

impl SimpSolver {

    fn newVar(&mut self, upol : LBool, dvar : bool) -> Var {
        let v = self.core.newVar(upol, dvar);

        self.frozen.insert(&v, 0);
        self.eliminated.insert(&v, 0);

        if self.use_simplification {
            // TODO: self.occurs.init(v);
            self.touched.insert(&v, 0);
            self.elim.addVar(v);
        }

        v
    }

    fn addClause(&mut self, ps : &[Lit]) -> bool {
        //#ifndef NDEBUG
        for l in ps.iter() {
            assert!(self.eliminated[&l.var()] == 0);
        }
        //#endif

        let nclauses = self.core.clauses.len();

        if self.set.use_rcheck && self.implied(ps) { return true; }

        if !self.core.addClause(ps) { return false; }

        if self.use_simplification && self.core.clauses.len() == nclauses + 1 {
            let cr = *self.core.clauses.last().unwrap();
            let c  = &mut self.core.ca[cr];

            // NOTE: the clause is added to the queue immediately and then
            // again during 'gatherTouchedClauses()'. If nothing happens
            // in between, it will only be checked once. Otherwise, it may
            // be checked twice unnecessarily. This is an unfortunate
            // consequence of how backward subsumption is used to mimic
            // forward subsumption.
            self.subsumption_queue.push_back(cr);
            for i in 0 .. c.len() {
                // TODO: self.occurs[var(c[i])].push(cr);
                self.touched[&c[i].var()] = 1;
                self.n_touched += 1;
                self.elim.bumpLitOcc(&c[i], 1);
            }
        }

        true
    }

    fn implied(&mut self, c : &[Lit]) -> bool {
        assert!(self.core.trail.isGroundLevel());

        self.core.trail.newDecisionLevel();
        for i in 0 .. c.len() {
            let l = c[i];
            if self.core.assigns.sat(l) {
                self.core.cancelUntil(0);
                return true;
            } else if !self.core.assigns.unsat(l) {
                assert!(self.core.assigns.undef(l.var()));
                self.core.uncheckedEnqueue(!l, None);
            }
        }

        let result = self.core.propagate().is_some();
        self.core.cancelUntil(0);
        return result;
    }

    fn solve_(&mut self, mut do_simp : bool, turn_off_simp : bool) -> LBool {
        let mut extra_frozen : Vec<Var> = Vec::new();
        let mut result = LBool::True();

        do_simp &= self.use_simplification;
        if do_simp {
            // Assumptions must be temporarily frozen to run variable elimination:
            for lit in self.core.assumptions.iter() {
                let v = lit.var();

                // If an assumption has been eliminated, remember it.
                assert!(self.eliminated[&v] == 0);

                if self.frozen[&v] == 0 {
                    // Freeze and store.
                    self.frozen[&v] = 1;
                    extra_frozen.push(v);
                }
            }

            result = LBool::new(self.eliminate(turn_off_simp));
        }

        if result.isTrue() {
            result = self.core.solve_();
        } else {
            info!("===============================================================================");
        }

        if result.isTrue() && self.set.extend_model {
            self.extendModel();
        }

        if do_simp {
            // Unfreeze the assumptions that were frozen:
            for v in extra_frozen.iter() {
                self.frozen[v] = 0;
                if self.use_simplification {
                    self.elim.updateElimHeap(v, &self.frozen, &self.eliminated, &self.core.assigns);
                }
            }
        }

        result
    }

    fn extendModel(&mut self) {
        let mut i = self.elimclauses.len() - 1;
        while i > 0 {
            let mut j = self.elimclauses[i];
            i -= 1;
            while j > 1 {
                //

                j -= 1;
                i -= 1;
            }

            //let x = toLit(elimclauses[i]);
            //self.model[x.var()] = LBool::new(!x.sign());
        }

/*
        int i, j;
        Lit x;

        for (i = elimclauses.size() - 1; i > 0; i -= j){
            for (j = elimclauses[i--]; j > 1; j--, i--)
                if (modelValue(toLit(elimclauses[i])) != l_False)
                    goto next;

            x = toLit(elimclauses[i]);
            model[var(x)] = lbool(!sign(x));
        next:;
        }
        */
    }

    fn eliminate(&mut self, turn_off_elim : bool) -> bool {
        if !self.core.simplify() {
            return false;
        } else if !self.use_simplification {
            return true;
        }

        // Main simplification loop:
        'cleanup: while self.n_touched > 0 || self.bwdsub_assigns < self.core.trail.totalSize() as i32 || self.elim.len() > 0 {

            self.gatherTouchedClauses();
            // printf("  ## (time = %6.2f s) BWD-SUB: queue = %d, trail = %d\n", cpuTime(), subsumption_queue.size(), trail.size() - bwdsub_assigns);
            if (self.subsumption_queue.len() > 0 || self.bwdsub_assigns < self.core.trail.totalSize() as i32) && !self.backwardSubsumptionCheck(true) {
                self.core.ok = false;
                break 'cleanup;
            }

            // Empty elim_heap and return immediately on user-interrupt:
            if self.core.asynch_interrupt {
                assert!(self.bwdsub_assigns == self.core.trail.totalSize() as i32);
                assert!(self.subsumption_queue.len() == 0);
                assert!(self.n_touched == 0);
                //elim_heap.clear();
                break 'cleanup;
            }

            // printf("  ## (time = %6.2f s) ELIM: vars = %d\n", cpuTime(), elim_heap.size());
            let mut cnt = 0;
            loop {
                match self.elim.pop() {
                    None       => { break; }
                    Some(elim) => {
                        if self.core.asynch_interrupt { break; }
                        if self.eliminated[&elim] == 0 && self.core.assigns.undef(elim) {
                            if cnt % 100 == 0 {
                                trace!("elimination left: {:10}", self.elim.len());
                            }

                            if self.set.use_asymm {
                                // Temporarily freeze variable. Otherwise, it would immediately end up on the queue again:
                                let was_frozen = self.frozen[&elim];
                                self.frozen[&elim] = 1;
                                if !self.asymmVar(elim) {
                                    self.core.ok = false;
                                    break 'cleanup;
                                }
                                self.frozen[&elim] = was_frozen;
                            }

                            // At this point, the variable may have been set by assymetric branching, so check it
                            // again. Also, don't eliminate frozen variables:
                            if self.set.use_elim && self.core.assigns.undef(elim) && self.frozen[&elim] == 0 && !self.eliminateVar(elim) {
                                self.core.ok = false;
                                break 'cleanup;
                            }

                            self.core.checkGarbage(self.set.simp_garbage_frac);
                        }
                        cnt += 1;
                    }
                }


            }

            assert!(self.subsumption_queue.len() == 0);
        }

        // If no more simplification is needed, free all simplification-related data structures:
        if turn_off_elim {
            self.touched.clear();
            //occurs   .clear(true);
            //n_occ    .clear(true);
            //elim_heap.clear(true);
            self.subsumption_queue.clear();

            self.use_simplification    = false;
            self.core.set.remove_satisfied      = true;
            //ca.extra_clause_field = false;
            //self.max_simp_var          = self.core.nVars();

            // Force full cleanup (this is safe and desirable since it only happens once):
            //rebuildOrderHeap();
            //garbageCollect();
        } else {
            // Cheaper cleanup:
            self.core.checkGarbageDef();
        }

        if self.elimclauses.len() > 0 {
            info!("|  Eliminated clauses:     {:10.2} Mb                                      |\n",
                  ((self.elimclauses.len() * mem::size_of::<u32>()) as f64) / (1024.0 * 1024.0));
        }

        self.core.ok
    }

    fn asymmVar(&mut self, v : Var) -> bool {
        assert!(self.use_simplification);

/*
        const vec<CRef>& cls = occurs.lookup(v);

        if (value(v) != l_Undef || cls.size() == 0)
        return true;

        for (int i = 0; i < cls.size(); i++)
        if (!asymm(v, cls[i]))
        return false;
*/
        self.backwardSubsumptionCheck(false)
    }

    fn asymm(&mut self, v : Var, cr : ClauseRef) -> bool {
        assert!(self.core.trail.decisionLevel() == 0);
/*        Clause& c = ca[cr];
        if (c.mark() || satisfied(c)) return true;

        trail_lim.push(trail.size());
        Lit l = lit_Undef;
        for (int i = 0; i < c.size(); i++)
        if (var(c[i]) != v && value(c[i]) != l_False)
        uncheckedEnqueue(~c[i]);
        else
        l = c[i];

        if (propagate() != CRef_Undef){
        cancelUntil(0);
        asymm_lits++;
        if (!strengthenClause(cr, l))
        return false;
        }else
        cancelUntil(0);
*/
        true
    }

    fn eliminateVar(&mut self, v : Var) -> bool {
        assert!(self.frozen[&v] == 0);
        assert!(self.eliminated[&v] == 0);
        assert!(self.core.assigns.undef(v));

/*
        // Split the occurrences into positive and negative:
        //
        const vec<CRef>& cls = occurs.lookup(v);
        vec<CRef>        pos, neg;
        for (int i = 0; i < cls.size(); i++)
        (find(ca[cls[i]], mkLit(v)) ? pos : neg).push(cls[i]);

        // Check wether the increase in number of clauses stays within the allowed ('grow'). Moreover, no
        // clause must exceed the limit on the maximal clause size (if it is set):
        //
        int cnt         = 0;
        int clause_size = 0;

        for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++)
        if (merge(ca[pos[i]], ca[neg[j]], v, clause_size) &&
        (++cnt > cls.size() + grow || (clause_lim != -1 && clause_size > clause_lim)))
        return true;

        // Delete and store old clauses:
        eliminated[v] = true;
        setDecisionVar(v, false);
        eliminated_vars++;

        if (pos.size() > neg.size()){
        for (int i = 0; i < neg.size(); i++)
        mkElimClause(elimclauses, v, ca[neg[i]]);
        mkElimClause(elimclauses, mkLit(v));
        }else{
        for (int i = 0; i < pos.size(); i++)
        mkElimClause(elimclauses, v, ca[pos[i]]);
        mkElimClause(elimclauses, ~mkLit(v));
        }

        for (int i = 0; i < cls.size(); i++)
        removeClause(cls[i]);

        // Produce clauses in cross product:
        vec<Lit>& resolvent = add_tmp;
        for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++)
        if (merge(ca[pos[i]], ca[neg[j]], v, resolvent) && !addClause_(resolvent))
        return false;

        // Free occurs list for this variable:
        occurs[v].clear(true);

        // Free watchers lists for this variable, if possible:
        if (watches[ mkLit(v)].size() == 0) watches[ mkLit(v)].clear(true);
        if (watches[~mkLit(v)].size() == 0) watches[~mkLit(v)].clear(true);
*/
        self.backwardSubsumptionCheck(false)
    }

    // Backward subsumption + backward subsumption resolution
    fn backwardSubsumptionCheck(&mut self, verbose : bool) -> bool {
        assert!(self.core.trail.decisionLevel() == 0);
/*
        int cnt = 0;
        int subsumed = 0;
        int deleted_literals = 0;

        while (subsumption_queue.size() > 0 || bwdsub_assigns < trail.size()){

        // Empty subsumption queue and return immediately on user-interrupt:
        if (asynch_interrupt){
        subsumption_queue.clear();
        bwdsub_assigns = trail.size();
        break; }

        // Check top-level assignments by creating a dummy clause and placing it in the queue:
        if (subsumption_queue.size() == 0 && bwdsub_assigns < trail.size()){
        Lit l = trail[bwdsub_assigns++];
        ca[bwdsub_tmpunit][0] = l;
        ca[bwdsub_tmpunit].calcAbstraction();
        subsumption_queue.insert(bwdsub_tmpunit); }

        CRef    cr = subsumption_queue.peek(); subsumption_queue.pop();
        Clause& c  = ca[cr];

        if (c.mark()) continue;

        if (verbose && verbosity >= 2 && cnt++ % 1000 == 0)
        printf("subsumption left: %10d (%10d subsumed, %10d deleted literals)\r", subsumption_queue.size(), subsumed, deleted_literals);

        assert(c.size() > 1 || value(c[0]) == l_True);    // Unit-clauses should have been propagated before this point.

        // Find best variable to scan:
        Var best = var(c[0]);
        for (int i = 1; i < c.size(); i++)
        if (occurs[var(c[i])].size() < occurs[best].size())
        best = var(c[i]);

        // Search all candidates:
        vec<CRef>& _cs = occurs.lookup(best);
        CRef*       cs = (CRef*)_cs;

        for (int j = 0; j < _cs.size(); j++)
        if (c.mark())
        break;
        else if (!ca[cs[j]].mark() &&  cs[j] != cr && (subsumption_lim == -1 || ca[cs[j]].size() < subsumption_lim)){
        Lit l = c.subsumes(ca[cs[j]]);

        if (l == lit_Undef)
        subsumed++, removeClause(cs[j]);
        else if (l != lit_Error){
        deleted_literals++;

        if (!strengthenClause(cs[j], ~l))
        return false;

        // Did current candidate get deleted from cs? Then check candidate at index j again:
        if (var(l) == best)
        j--;
        }
        }
        }
*/
        true
    }

    fn gatherTouchedClauses(&mut self) {
        if self.n_touched == 0 { return; }
/*
        int i,j;
        for (i = j = 0; i < subsumption_queue.size(); i++)
        if (ca[subsumption_queue[i]].mark() == 0)
        ca[subsumption_queue[i]].mark(2);

        for (i = 0; i < nVars(); i++)
        if (touched[i]){
        const vec<CRef>& cs = occurs.lookup(i);
        for (j = 0; j < cs.size(); j++)
        if (ca[cs[j]].mark() == 0){
        subsumption_queue.insert(cs[j]);
        ca[cs[j]].mark(2);
        }
        touched[i] = 0;
        }

        for (i = 0; i < subsumption_queue.size(); i++)
        if (ca[subsumption_queue[i]].mark() == 2)
        ca[subsumption_queue[i]].mark(0);
*/
        self.n_touched = 0;
    }

}
