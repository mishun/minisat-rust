use std::default::{Default};
use std::collections::vec_deque::{VecDeque};
use std::mem;
use std::borrow::Borrow;
use minisat::index_map::{HasIndex, IndexMap};
use minisat::lbool::{LBool};
use minisat::literal::{Var, Lit};
use minisat::clause::{Clause, ClauseRef, SubsumesRes, subsumes};
use minisat::assignment::{Assignment};
use super::Solver;


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

    pub fn clearHeap(&mut self) {
        self.heap.clear();
        self.indices.clear();
    }

    pub fn clearAll(&mut self) {
        self.clearHeap();
        self.n_occ.clear();
    }

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


struct OccLists<V> {
    occs    : IndexMap<Var, Vec<V>>,
    dirty   : IndexMap<Var, bool>,
    dirties : Vec<Var>
//Deleted                  deleted;
}

impl<V> OccLists<V> {
    pub fn initVar(&mut self, v : &Var) {
        self.occs.insert(v, Vec::new());
        self.dirty.insert(v, false);
    }

    pub fn clearVar(&mut self, v : &Var) {
        self.occs.remove(v);
    }

    pub fn pushOcc(&mut self, v : &Var, x : V) {
        self.occs[v].push(x);
    }

    pub fn clear(&mut self) {
        self.occs.clear();
        self.dirty.clear();
        self.dirties.clear();
    }

    pub fn lookup(&mut self, v : &Var) -> &Vec<V> {
        if self.dirty[v] {
            self.cleanVar(v);
        }
        &self.occs[v]
    }

    pub fn get(&self, v : &Var) -> &Vec<V> {
        &self.occs[v]
    }

    fn  smudge(&mut self, v : Var) {
        if !self.dirty[&v] {
            self.dirty[&v] = true;
            self.dirties.push(v);
        }
    }

    pub fn cleanVar(&mut self, v : &Var) {
// TODO:
//        Vec& vec = occs[idx];
//        int  i, j;
//        for (i = j = 0; i < vec.size(); i++)
//        if (!deleted(vec[i]))
//        vec[j++] = vec[i];
//        vec.shrink(i - j);
        self.dirty[v] = false;
    }
}

impl<V : PartialEq> OccLists<V> {
    pub fn removeOcc(&mut self, v : &Var, x : V) {
        self.occs[v].retain(|y| { *y != x })
    }
}


pub struct SimpSolver {
    core               : super::CoreSolver,
    set                : SimpSettings,

    // Statistics:
    merges             : i32,
    asymm_lits         : i32,
    eliminated_vars    : i32,

    // Solver state:
    use_simplification : bool,
    max_simp_var       : Var,        // Max variable at the point simplification was turned off.
    elimclauses        : Vec<u32>,
    touched            : IndexMap<Var, i8>,

    occurs             : OccLists<ClauseRef>,
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
            self.occurs.initVar(&v);
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
                self.occurs.pushOcc(&c[i].var(), cr);
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
            let mut j = self.elimclauses[i] as usize    ;
            i -= 1;
            let mut skip = false;

            while j > 1 {
                let x = Lit::fromIndex(self.elimclauses[i] as usize);
                if !(self.core.model[x.var().toIndex()] ^ x.sign()).isFalse() {
                    skip = true;
                    break;
                }

                j -= 1;
                i -= 1;
            }

            if !skip {
                let x = Lit::fromIndex(self.elimclauses[i] as usize);
                self.core.model[x.var().toIndex()] = LBool::new(!x.sign());
            }

            i -= j;
        }
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
                self.elim.clearHeap();
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
            self.occurs.clear();
            self.elim.clearAll();
            self.subsumption_queue.clear();

            self.use_simplification = false;
            self.core.set.remove_satisfied = true;
            //ca.extra_clause_field = false;
            self.max_simp_var = Var::new(self.core.nVars());

            // Force full cleanup (this is safe and desirable since it only happens once):
            self.core.rebuildOrderHeap();
            //self.core.garbageCollect(); // TODO: override
        } else {
            // Cheaper cleanup:
            //self.core.checkGarbageDef();
        }

        if self.elimclauses.len() > 0 {
            info!("|  Eliminated clauses:     {:10.2} Mb                                      |\n",
                  ((self.elimclauses.len() * mem::size_of::<u32>()) as f64) / (1024.0 * 1024.0));
        }

        self.core.ok
    }

    fn asymmVar(&mut self, v : Var) -> bool {
        assert!(self.use_simplification);

        let cls = {
            let cls = self.occurs.lookup(&v);
            if !self.core.assigns.undef(v) || cls.len() == 0 {
                return true;
            }
            cls.clone()
        };

        for cr in cls.iter() {
            if !self.asymm(v, *cr) {
                return false;
            }
        }

        self.backwardSubsumptionCheck(false)
    }

    fn asymm(&mut self, v : Var, cr : ClauseRef) -> bool {
        assert!(self.core.trail.isGroundLevel());

        let c = {
            let c = &mut self.core.ca[cr];
            if c.mark() != 0 || super::satisfiedWith(c, &self.core.assigns) {
                return true;
            }

            c.to_vec()
        };

        self.core.trail.newDecisionLevel();

        let mut l = None;
        for lit in c.iter() {
            if v != lit.var() && !self.core.assigns.unsat(*lit) {
                self.core.uncheckedEnqueue(!*lit, None);
            } else {
                l = Some(*lit);
            }
        }

        if self.core.propagate().is_some() {
            self.core.cancelUntil(0);
            self.asymm_lits += 1;
            if !self.strengthenClause(cr, l.unwrap()) {
                return false;
            }
        } else {
            self.core.cancelUntil(0);
        }

        true
    }

    fn removeClause(&mut self, cr : ClauseRef) {
        if self.use_simplification {
            let c = &self.core.ca[cr];

            for i in 0 .. c.len() {
                self.elim.bumpLitOcc(&c[i], -1);
                self.elim.updateElimHeap(&c[i].var(), &self.frozen, &self.eliminated, &self.core.assigns);
                self.occurs.smudge(c[i].var());
            }
        }

        super::removeClause(&mut self.core.ca, &mut self.core.watches, &mut self.core.stats, &mut self.core.vardata, &self.core.assigns, cr);
    }

    fn strengthenClause(&mut self, cr : ClauseRef, l : Lit) -> bool {
        assert!(self.core.trail.isGroundLevel());
        assert!(self.use_simplification);

        // FIX: this is too inefficient but would be nice to have (properly implemented)
        // if (!find(subsumption_queue, &c))
        self.subsumption_queue.push_back(cr);

        if self.core.ca[cr].len() == 2 {
            self.removeClause(cr);
            self.core.ca[cr].strengthen(l);
        } else {
            super::detachClause(&mut self.core.ca, &mut self.core.stats, &mut self.core.watches, cr, true);
            self.core.ca[cr].strengthen(l);
            self.core.attachClause(cr);
            self.occurs.removeOcc(&l.var(), cr);
            self.elim.bumpLitOcc(&l, -1);
            self.elim.updateElimHeap(&l.var(), &self.frozen, &self.eliminated, &self.core.assigns);
        }

        match self.core.ca[cr].as_unit_clause() {
            None    => { true }
            Some(l) => { self.core.enqueue(l, None) && self.core.propagate().is_none() }
        }
    }

    fn merge(&mut self, _ps : ClauseRef, _qs : ClauseRef, v : Var) -> Option<Vec<Lit>> {
        self.merges += 1;

        let ps_smallest = self.core.ca[_ps].len() < self.core.ca[_qs].len();
        let ps = if ps_smallest { &self.core.ca[_qs] } else { &self.core.ca[_ps] };
        let qs = if ps_smallest { &self.core.ca[_ps] } else { &self.core.ca[_qs] };

        let mut res = Vec::new();
        for i in 0 .. qs.len() {
            if qs[i].var() != v {
                let mut ok = true;

                for j in 0 .. ps.len() {
                    if ps[j].var() == qs[i].var() {
                        if ps[j] == !qs[i] {
                            return None;
                        } else {
                            ok = false;
                            break;
                        }
                    }
                }

                if ok {
                    res.push(qs[i]);
                }
            }
        }

        for i in 0 .. ps.len() {
            if ps[i].var() != v {
                res.push(ps[i]);
            }
        }

        Some(res)
    }

    fn eliminateVar(&mut self, v : Var) -> bool {
        assert!(self.frozen[&v] == 0);
        assert!(self.eliminated[&v] == 0);
        assert!(self.core.assigns.undef(v));

        // Split the occurrences into positive and negative:
        let cls = self.occurs.lookup(&v).clone();
        let mut pos = Vec::new();
        let mut neg = Vec::new();
        for cr in cls.iter() {
            let c = &self.core.ca[*cr];
            for i in 0 .. c.len() {
                let l = c[i];
                if l.var() == v {
                    if l.sign() { neg.push(*cr); } else { pos.push(*cr); }
                    break;
                }
            }
        }

        // Check wether the increase in number of clauses stays within the allowed ('grow'). Moreover, no
        // clause must exceed the limit on the maximal clause size (if it is set):
        let mut cnt         = 0;

        for pr in pos.iter() {
            for nr in neg.iter() {
                match self.merge(*pr, *nr, v) {
                    None            => {}
                    Some(resolvent) => {
                        cnt += 1;
                        if cnt > cls.len() + (self.set.grow as usize) || (self.set.clause_lim != -1 && (resolvent.len() as i32) > self.set.clause_lim) {
                            return true;
                        }
                    }
                }
            }
        }

        // Delete and store old clauses:
        self.eliminated[&v] = 1;
        self.core.setDecisionVar(v, false);
        self.eliminated_vars += 1;

        if pos.len() > neg.len() {
            for cr in neg.iter() {
                mkElimClause(&mut self.elimclauses, v, &self.core.ca[*cr]);
            }
            mkElimClause2(&mut self.elimclauses, Lit::new(v, false));
        } else {
            for cr in pos.iter() {
                mkElimClause(&mut self.elimclauses, v, &self.core.ca[*cr]);
            }
            mkElimClause2(&mut self.elimclauses, Lit::new(v, true));
        }

        for cr in cls.iter() {
            self.removeClause(*cr);
        }

        // Produce clauses in cross product:
        //vec<Lit>& resolvent = add_tmp;
        for pr in pos.iter() {
            for nr in neg.iter() {
                match self.merge(*pr, *nr, v) {
                    None            => {}
                    Some(resolvent) => {
                        if !self.addClause(resolvent.borrow()) {
                            return false;
                        }
                    }
                }
            }
        }

        // Free occurs list for this variable:
        self.occurs.clearVar(&v);

        // Free watchers lists for this variable, if possible:
//        if (watches[ mkLit(v)].size() == 0) watches[ mkLit(v)].clear(true);
//        if (watches[~mkLit(v)].size() == 0) watches[~mkLit(v)].clear(true);

        self.backwardSubsumptionCheck(false)
    }

    // Backward subsumption + backward subsumption resolution
    fn backwardSubsumptionCheck(&mut self, verbose : bool) -> bool {
        assert!(self.core.trail.decisionLevel() == 0);

        let mut cnt = 0i32;
        let mut subsumed = 0i32;
        let mut deleted_literals = 0i32;

        while self.subsumption_queue.len() > 0 || self.bwdsub_assigns < self.core.trail.totalSize() as i32 {

            // Empty subsumption queue and return immediately on user-interrupt:
            if self.core.asynch_interrupt {
                self.subsumption_queue.clear();
                self.bwdsub_assigns = self.core.trail.totalSize() as i32;
                break;
            }

            // Check top-level assignments by creating a dummy clause and placing it in the queue:
            if self.subsumption_queue.len() == 0 && self.bwdsub_assigns < self.core.trail.totalSize() as i32 {
                let l = self.core.trail[self.bwdsub_assigns as usize];
                self.bwdsub_assigns += 1;

                self.core.ca[self.bwdsub_tmpunit][0] = l;
                self.core.ca[self.bwdsub_tmpunit].calcAbstraction();
                self.subsumption_queue.push_back(self.bwdsub_tmpunit);
            }

            let cr = self.subsumption_queue.pop_front().unwrap();

            let best = {
                let c = &self.core.ca[cr];

                if c.mark() != 0 {
                    continue;
                }

                if verbose && cnt % 1000 == 0 {
                    trace!("subsumption left: {:10} ({:10} subsumed, {:10} deleted literals)\r",
                        self.subsumption_queue.len(), subsumed, deleted_literals);
                }
                cnt += 1;

                assert!(c.len() > 1 || self.core.assigns.sat(c[0])); // Unit-clauses should have been propagated before this point.

                // Find best variable to scan:
                let mut best = c[0].var();
                for i in 1 .. c.len() {
                    if self.occurs.get(&c[i].var()).len() < self.occurs.get(&best).len() {
                        best = c[i].var();
                    }
                }

                best
            };

            // Search all candidates:
            //let _cs = self.occurs.lookup(&best);
            //CRef*       cs = (CRef*)_cs;

            let mut j = 0;
            while j < self.occurs.lookup(&best).len() {
                let cj = self.occurs.lookup(&best)[j];

                if self.core.ca[cr].mark() != 0 {
                    break;
                } else if self.core.ca[cj].mark() == 0 && cj != cr && (self.set.subsumption_lim == -1 || (self.core.ca[cj].len() as i32) < self.set.subsumption_lim) {
                    match subsumes(&self.core.ca[cr], &self.core.ca[cj]) {
                        SubsumesRes::Undef      => {
                            subsumed += 1;
                            self.removeClause(cj);
                        }

                        SubsumesRes::Literal(l) => {
                            deleted_literals += 1;
                            if !self.strengthenClause(cj, l) {
                                return false;
                            }

                            // Did current candidate get deleted from cs? Then check candidate at index j again:
                            if l.var() == best {
                                j -= 1;
                            }
                        }

                        SubsumesRes::Error      => {}
                    }
                }

                j += 1;
            }
        }

        true
    }

    fn gatherTouchedClauses(&mut self) {
        if self.n_touched == 0 { return; }

        for cr in self.subsumption_queue.iter() {
            let c = &mut self.core.ca[*cr];
            if c.mark() == 0 {
                c.setMark(2);
            }
        }

        for i in 0 .. self.core.nVars() {
            let v = Var::new(i);
            if self.touched[&v] != 0 {
                for cr in self.occurs.lookup(&v) {
                    let c = &mut self.core.ca[*cr];
                    if c.mark() == 0 {
                        self.subsumption_queue.push_back(*cr);
                        c.setMark(2);
                    }
                }
                self.touched[&v] = 0;
            }
        }

        for cr in self.subsumption_queue.iter() {
            let c = &mut self.core.ca[*cr];
            if c.mark() == 2 {
                c.setMark(0);
            }
        }

        self.n_touched = 0;
    }

}


fn mkElimClause2(elimclauses : &mut Vec<u32>, x : Lit) {
    elimclauses.push(x.toIndex() as u32);
    elimclauses.push(1);
}


fn mkElimClause(elimclauses : &mut Vec<u32>, v : Var, c : &Clause) {
    let first = elimclauses.len();
    let mut v_pos = 0;

    // Copy clause to elimclauses-vector. Remember position where the
    // variable 'v' occurs:
    for i in 0 .. c.len() {
        elimclauses.push(c[i].toIndex() as u32);
        if c[i].var() == v {
            v_pos = i + first;
        }
    }
    assert!(v_pos > 0);

    // Swap the first literal with the 'v' literal, so that the literal
    // containing 'v' will occur first in the clause:
    elimclauses.swap(first, v_pos);

    // Store the length of the clause last:
    elimclauses.push(c.len() as u32);
}
