use std::default::{Default};
use std::collections::vec_deque::{VecDeque};
use std::mem;
use std::borrow::Borrow;
use std::sync::atomic;
use minisat::index_map::{HasIndex, IndexMap};
use minisat::lbool::{LBool};
use minisat::literal::{Var, Lit};
use minisat::clause::{Clause, ClauseRef, ClauseAllocator, SubsumesRes, subsumes};
use minisat::assignment::*;
use super::Solver;


#[derive(Clone, Copy)]
pub struct SimpSettings {
    pub grow              : usize, // Allow a variable elimination step to grow by a number of clauses (default to zero).
    pub clause_lim        : i32,   // Variables are not eliminated if it produces a resolvent with a length above this limit. -1 means no limit.
    pub subsumption_lim   : i32,   // Do not check if subsumption against a clause larger than this. -1 means no limit.
    pub simp_garbage_frac : f64,   // A different limit for when to issue a GC during simplification (Also see 'garbage_frac').
    pub use_asymm         : bool,  // Shrink clauses by asymmetric branching.
    pub use_rcheck        : bool,  // Check if a clause is already implied. Prett costly, and subsumes subsumptions :)
    pub use_elim          : bool,  // Perform variable elimination.
    pub extend_model      : bool,  // Flag to indicate whether the user needs to look at the full model.
}

impl Default for SimpSettings {
    fn default() -> SimpSettings {
        SimpSettings {
            grow              : 0,
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


struct OccLine {
    occs  : Vec<ClauseRef>,
    dirty : bool
}

struct OccLists {
    occs : IndexMap<Var, OccLine>
}

impl OccLists {
    pub fn new() -> OccLists {
        OccLists { occs : IndexMap::new() }
    }

    pub fn initVar(&mut self, v : &Var) {
        self.occs.insert(v, OccLine { occs : Vec::new(), dirty : false });
    }

    pub fn clearVar(&mut self, v : &Var) {
        self.occs.remove(v);
    }

    pub fn pushOcc(&mut self, v : &Var, x : ClauseRef) {
        self.occs[v].occs.push(x);
    }

    pub fn removeOcc(&mut self, v : &Var, x : ClauseRef) {
        self.occs[v].occs.retain(|y| { *y != x })
    }

    pub fn lookup(&mut self, v : &Var, ca : &ClauseAllocator) -> &Vec<ClauseRef> {
        let ol = &mut self.occs[v];
        if ol.dirty {
            ol.occs.retain(|cr| { !ca[*cr].is_deleted() });
            ol.dirty = false;
        }
        &ol.occs
    }

    pub fn getDirty(&self, v : &Var) -> &Vec<ClauseRef> {
        &self.occs[v].occs
    }

    pub fn smudge(&mut self, v : &Var) {
        let ol = &mut self.occs[v];
        if !ol.dirty {
            ol.dirty = true;
        }
    }

    pub fn clear(&mut self) {
        self.occs.clear();
    }

    pub fn relocGC(&mut self, from : &mut ClauseAllocator, to : &mut ClauseAllocator) {
        self.occs.modify_in_place(|ol| {
            if ol.dirty {
                ol.occs.retain(|cr| { !from[*cr].is_deleted() });
                ol.dirty = false;
            }

            for occ in ol.occs.iter_mut() {
                *occ = from.relocTo(to, *occ);
            }
        });
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

    occurs             : OccLists,
    elim               : ElimQueue,
    subsumption_queue  : VecDeque<ClauseRef>,
    frozen             : IndexMap<Var, i8>,
    frozen_vars        : Vec<Var>,
    eliminated         : IndexMap<Var, i8>,
    bwdsub_assigns     : usize,
    n_touched          : usize,

    // Temporaries:
    bwdsub_tmpunit     : ClauseRef,
}

impl Solver for SimpSolver {
    fn nVars(&self) -> usize {
        self.core.nVars()
    }

    fn nClauses(&self) -> usize {
        self.core.nClauses()
    }

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

    fn getModel(&self) -> &Vec<LBool> {
        self.core.getModel()
    }

    fn printStats(&self) {
        self.core.printStats();
    }
}

impl SimpSolver {

    pub fn new(core_s : super::CoreSettings, simp_s : SimpSettings) -> SimpSolver {
        let mut s = super::CoreSolver::new(core_s);
        s.ca.set_extra_clause_field(true); // NOTE: must happen before allocating the dummy clause below.
        s.set.remove_satisfied = false;
        let temp_clause = s.ca.alloc(&vec![Lit::fromIndex(0)], false);
        SimpSolver { core               : s
                   , set                : simp_s

                   , merges             : 0
                   , asymm_lits         : 0
                   , eliminated_vars    : 0

                   , use_simplification : true
                   , max_simp_var       : Var::new(0)
                   , elimclauses        : Vec::new()
                   , touched            : IndexMap::new()

                   , occurs             : OccLists::new()
                   , elim               : ElimQueue::new()
                   , subsumption_queue  : VecDeque::new()
                   , frozen             : IndexMap::new()
                   , frozen_vars        : Vec::new()
                   , eliminated         : IndexMap::new()
                   , bwdsub_assigns     : 0
                   , n_touched          : 0

                   , bwdsub_tmpunit     : temp_clause
                   }
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

    pub fn solveLimited(&mut self, assumps : &[Lit], do_simp : bool, turn_off_simp : bool) -> LBool {
        self.core.assumptions = assumps.to_vec();
        return self.solve_(do_simp, turn_off_simp);
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
        if self.elimclauses.is_empty() { return; }

        let mut i = self.elimclauses.len() - 1;
        while i > 0 {
            let mut j = self.elimclauses[i] as usize;
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

    pub fn eliminate(&mut self, turn_off_elim : bool) -> bool {
        if !self.core.simplify() {
            return false;
        } else if !self.use_simplification {
            return true;
        }

        // Main simplification loop:
        'cleanup: while self.n_touched > 0 || self.bwdsub_assigns < self.core.trail.totalSize() || self.elim.len() > 0 {
            self.gatherTouchedClauses();

            trace!("BWD-SUB: queue = {}, trail = {}", self.subsumption_queue.len(), self.core.trail.totalSize() - self.bwdsub_assigns);
            if (self.subsumption_queue.len() > 0 || self.bwdsub_assigns < self.core.trail.totalSize()) && !self.backwardSubsumptionCheck(true) {
                self.core.ok = false;
                break 'cleanup;
            }

            // Empty elim_heap and return immediately on user-interrupt:
            if self.core.asynch_interrupt.load(atomic::Ordering::Relaxed) {
                assert!(self.bwdsub_assigns == self.core.trail.totalSize());
                assert!(self.subsumption_queue.len() == 0);
                assert!(self.n_touched == 0);
                self.elim.clearHeap();
                break 'cleanup;
            }

            trace!("ELIM: vars = {}", self.elim.len());
            let mut cnt = 0;
            loop {
                match self.elim.pop() {
                    None       => { break; }
                    Some(elim) => {
                        if self.core.asynch_interrupt.load(atomic::Ordering::Relaxed) { break; }
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

                            if self.core.ca.checkGarbage(self.set.simp_garbage_frac) {
                                self.garbageCollect();
                            }
                        }
                    }
                }
                cnt += 1;
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
            self.core.ca.set_extra_clause_field(false);
            self.max_simp_var = Var::new(self.core.nVars());

            // Force full cleanup (this is safe and desirable since it only happens once):
            self.core.heur.rebuildOrderHeap(&self.core.assigns);
            self.core.garbageCollect();
        } else {
            // Cheaper cleanup:
            if self.core.ca.checkGarbage(self.core.set.garbage_frac) {
                self.garbageCollect();
            }
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
            let cls = self.occurs.lookup(&v, &self.core.ca);
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
                self.occurs.smudge(&c[i].var());
            }
        }

        super::removeClause(&mut self.core.ca, &mut self.core.watches, &mut self.core.stats, &mut self.core.assigns, cr);
    }

    fn strengthenClause(&mut self, cr : ClauseRef, l : Lit) -> bool {
        assert!(self.core.trail.isGroundLevel());
        assert!(self.use_simplification);

        // FIX: this is too inefficient but would be nice to have (properly implemented)
        // if (!find(subsumption_queue, &c))
        self.subsumption_queue.push_back(cr);

        let len = self.core.ca[cr].len();
        if len == 2 {
            self.removeClause(cr);
            let unit = {
                let ref mut c = self.core.ca[cr];
                c.strengthen(l);
                c[0]
            };
            self.core.enqueue(unit, None) && self.core.propagate().is_none()
        } else {
            super::detachClause(&mut self.core.ca, &mut self.core.stats, &mut self.core.watches, cr, true);
            self.core.ca[cr].strengthen(l);
            assert!(self.core.ca[cr].len() == len - 1);
            self.core.attachClause(cr);
            self.occurs.removeOcc(&l.var(), cr);
            self.elim.bumpLitOcc(&l, -1);
            self.elim.updateElimHeap(&l.var(), &self.frozen, &self.eliminated, &self.core.assigns);
            true
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
        let cls = self.occurs.lookup(&v, &self.core.ca).clone();
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
        let mut cnt = 0;
        for pr in pos.iter() {
            for nr in neg.iter() {
                match self.merge(*pr, *nr, v) {
                    None            => {}
                    Some(resolvent) => {
                        cnt += 1;
                        if cnt > cls.len() + self.set.grow || (self.set.clause_lim != -1 && (resolvent.len() as i32) > self.set.clause_lim) {
                            return true;
                        }
                    }
                }
            }
        }

        // Delete and store old clauses:
        self.eliminated[&v] = 1;
        self.core.heur.setDecisionVar(v, false);
        self.eliminated_vars += 1;

        if pos.len() > neg.len() {
            for cr in neg.iter() {
                mkElimClause(&mut self.elimclauses, v, &self.core.ca[*cr]);
            }
            mkElimUnit(&mut self.elimclauses, Lit::new(v, false));
        } else {
            for cr in pos.iter() {
                mkElimClause(&mut self.elimclauses, v, &self.core.ca[*cr]);
            }
            mkElimUnit(&mut self.elimclauses, Lit::new(v, true));
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
        self.core.watches.tryClearVar(v);

        self.backwardSubsumptionCheck(false)
    }

    // Backward subsumption + backward subsumption resolution
    fn backwardSubsumptionCheck(&mut self, verbose : bool) -> bool {
        assert!(self.core.trail.isGroundLevel());

        let mut cnt = 0i32;
        let mut subsumed = 0i32;
        let mut deleted_literals = 0i32;

        loop {
            // Empty subsumption queue and return immediately on user-interrupt:
            if self.core.asynch_interrupt.load(atomic::Ordering::Relaxed) {
                self.subsumption_queue.clear();
                self.bwdsub_assigns = self.core.trail.totalSize();
                break;
            }

            let cr =
                match self.subsumption_queue.pop_front() {
                    Some(cr) => { cr }

                    // Check top-level assignments by creating a dummy clause and placing it in the queue:
                    None if self.bwdsub_assigns < self.core.trail.totalSize() => {
                        let ref mut c = self.core.ca[self.bwdsub_tmpunit];
                        c[0] = self.core.trail[self.bwdsub_assigns];
                        c.calcAbstraction();

                        self.bwdsub_assigns += 1;
                        self.bwdsub_tmpunit
                    }

                    None => { break }
                };

            let best = {
                let c = &self.core.ca[cr];

                if c.mark() != 0 {
                    continue;
                }

                if verbose && cnt % 1000 == 0 {
                    trace!("subsumption left: {:10} ({:10} subsumed, {:10} deleted literals)",
                        self.subsumption_queue.len(), subsumed, deleted_literals);
                }
                cnt += 1;

                assert!(c.len() > 1 || self.core.assigns.sat(c[0])); // Unit-clauses should have been propagated before this point.

                // Find best variable to scan:
                let mut best = c[0].var();
                for i in 1 .. c.len() {
                    if self.occurs.getDirty(&c[i].var()).len() < self.occurs.getDirty(&best).len() {
                        best = c[i].var();
                    }
                }

                best
            };

            // Search all candidates:
            for cj in self.occurs.lookup(&best, &self.core.ca).clone().iter() {
                if self.core.ca[cr].mark() != 0 {
                    break;
                } else if self.core.ca[*cj].mark() == 0 && *cj != cr && (self.set.subsumption_lim == -1 || (self.core.ca[*cj].len() as i32) < self.set.subsumption_lim) {
                    match subsumes(&self.core.ca[cr], &self.core.ca[*cj]) {
                        SubsumesRes::Undef      => {
                            subsumed += 1;
                            self.removeClause(*cj);
                        }

                        SubsumesRes::Literal(l) => {
                            deleted_literals += 1;
                            if !self.strengthenClause(*cj, !l) {
                                return false;
                            }
                        }

                        SubsumesRes::Error      => {}
                    }
                }
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
                for cr in self.occurs.lookup(&v, &self.core.ca) {
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

    fn garbageCollect(&mut self) {
        let mut to = ClauseAllocator::newForGC(&self.core.ca);
        self.relocAll(&mut to);
        self.core.relocAll(&mut to);
        debug!("|  Garbage collection:   {:12} bytes => {:12} bytes             |", self.core.ca.size(), to.size());
        self.core.ca = to;
    }

    fn relocAll(&mut self, to : &mut ClauseAllocator) {
        if !self.use_simplification { return; }

        // All occurs lists:
        self.occurs.relocGC(&mut self.core.ca, to);

        // Subsumption queue:
        {
            let ref mut from = self.core.ca;
            self.subsumption_queue.retain(|cr| { !from[*cr].is_deleted() });
            for cr in self.subsumption_queue.iter_mut() {
                *cr = from.relocTo(to, *cr);
            }
        }

        // Temporary clause:
        self.bwdsub_tmpunit = self.core.ca.relocTo(to, self.bwdsub_tmpunit);
    }
}


fn mkElimUnit(elimclauses : &mut Vec<u32>, x : Lit) {
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
