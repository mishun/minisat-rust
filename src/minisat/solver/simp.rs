use std::borrow::Borrow;
use std::default::Default;
use std::collections::vec_deque::VecDeque;
use std::mem;
use minisat::formula::{Var, Lit, TempLit};
use minisat::formula::assignment::*;
use minisat::formula::clause::*;
use minisat::formula::index_map::{VarMap, LitMap};
use minisat::formula::util::*;
use super::Solver;


pub struct Settings {
    pub simp         : SimpSettings,
    pub extend_model : bool // Flag to indicate whether the user needs to look at the full model.
}

impl Default for Settings {
    fn default() -> Settings {
        Settings {
            simp         : Default::default(),
            extend_model : true
        }
    }
}


struct VarStatus {
    frozen     : i8,
    eliminated : i8
}


struct ElimQueue {
    heap    : Vec<Var>,
    indices : VarMap<usize>,
    n_occ   : LitMap<i32>
}

impl ElimQueue {
    pub fn new() -> ElimQueue {
        ElimQueue {
            heap    : Vec::new(),
            indices : VarMap::new(),
            n_occ   : LitMap::new()
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

    fn updateElimHeap(&mut self, v : &Var, var_status : &VarMap<VarStatus>, assigns : &Assignment) {
        if self.inHeap(&v) || (var_status[v].frozen == 0 && var_status[v].eliminated == 0 && assigns.undef(*v)) {
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
    occs : VarMap<OccLine>
}

impl OccLists {
    pub fn new() -> OccLists {
        OccLists { occs : VarMap::new() }
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
        for (_, ol) in self.occs.iter_mut() {
            if ol.dirty {
                ol.occs.retain(|cr| { !from[*cr].is_deleted() });
                ol.dirty = false;
            }

            for occ in ol.occs.iter_mut() {
                *occ = from.relocTo(to, *occ);
            }
        }
    }
}


pub struct SimpSettings {
    pub grow              : usize, // Allow a variable elimination step to grow by a number of clauses (default to zero).
    pub clause_lim        : i32,   // Variables are not eliminated if it produces a resolvent with a length above this limit. -1 means no limit.
    pub subsumption_lim   : i32,   // Do not check if subsumption against a clause larger than this. -1 means no limit.
    pub simp_garbage_frac : f64,   // A different limit for when to issue a GC during simplification (Also see 'garbage_frac').
    pub use_asymm         : bool,  // Shrink clauses by asymmetric branching.
    pub use_rcheck        : bool,  // Check if a clause is already implied. Prett costly, and subsumes subsumptions :)
    pub use_elim          : bool   // Perform variable elimination.
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
            use_elim          : true
        }
    }
}


pub struct SimpSolver {
    core               : super::CoreSolver,
    set                : SimpSettings,

    // Statistics:
    merges             : u64,
    asymm_lits         : u64,
    eliminated_vars    : u64,

    // Solver state:
    var_status         : VarMap<VarStatus>,

    use_simplification : bool,
    elimclauses        : ElimClauses,
    touched            : VarMap<i8>,
    occurs             : OccLists,
    elim               : ElimQueue,
    subsumption_queue  : VecDeque<ClauseRef>,
    bwdsub_assigns     : usize,
    n_touched          : usize,
    bwdsub_tmpunit     : ClauseRef,
}

impl Solver for SimpSolver {
    fn nVars(&self) -> usize {
        self.core.nVars()
    }

    fn nClauses(&self) -> usize {
        self.core.nClauses()
    }

    fn newVar(&mut self, upol : Option<bool>, dvar : bool) -> Var {
        let v = self.core.newVar(upol, dvar);

        self.var_status.insert(&v, VarStatus { frozen : 0, eliminated : 0 });
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
            assert!(self.var_status[&l.var()].eliminated == 0);
        }
        //#endif

        if self.set.use_rcheck && implied(&mut self.core, ps) {
            return true;
        }

        match self.core.addClause_(ps) {
            super::AddClause::UnSAT     => { false }
            super::AddClause::Consumed  => { true }
            super::AddClause::Added(cr) => {
                if self.use_simplification {
                    // NOTE: the clause is added to the queue immediately and then
                    // again during 'gatherTouchedClauses()'. If nothing happens
                    // in between, it will only be checked once. Otherwise, it may
                    // be checked twice unnecessarily. This is an unfortunate
                    // consequence of how backward subsumption is used to mimic
                    // forward subsumption.
                    self.subsumption_queue.push_back(cr);

                    let ref c = self.core.db.ca[cr];
                    for i in 0 .. c.len() {
                        self.occurs.pushOcc(&c[i].var(), cr);
                        self.touched[&c[i].var()] = 1;
                        self.n_touched += 1;
                        self.elim.bumpLitOcc(&c[i], 1);
                    }
                }

                true
            }
        }
    }

    fn printStats(&self) {
        self.core.printStats();
    }
}

impl SimpSolver {
    pub fn new(core_s : super::Settings, simp_s : Settings) -> SimpSolver {
        let mut s = super::CoreSolver::new(core_s);
        s.db.ca.set_extra_clause_field(true); // NOTE: must happen before allocating the dummy clause below.
        s.db.settings.remove_satisfied = false;
        let (_, temp_clause) = s.db.ca.alloc(Box::new([TempLit]), false); // TODO: be ready to unexpected consequences
        SimpSolver { core               : s
                   , set                : simp_s.simp
                   , merges             : 0
                   , asymm_lits         : 0
                   , eliminated_vars    : 0
                   , var_status         : VarMap::new()
                   , use_simplification : true
                   , elimclauses        : ElimClauses::new(simp_s.extend_model)
                   , touched            : VarMap::new()
                   , occurs             : OccLists::new()
                   , elim               : ElimQueue::new()
                   , subsumption_queue  : VecDeque::new()
                   , bwdsub_assigns     : 0
                   , n_touched          : 0
                   , bwdsub_tmpunit     : temp_clause
                   }
    }

    pub fn solveLimited(&mut self, assumptions : &[Lit], do_simp_param : bool, turn_off_simp : bool) -> super::PartialResult {
        let do_simp = do_simp_param && self.use_simplification;
        let mut extra_frozen : Vec<Var> = Vec::new();

        let elim_result =
            if do_simp {
                // Assumptions must be temporarily frozen to run variable elimination:
                for lit in assumptions.iter() {
                    let ref mut st = self.var_status[&lit.var()];

                    // If an assumption has been eliminated, remember it.
                    assert!(st.eliminated == 0);
                    if st.frozen == 0 {
                        // Freeze and store.
                        st.frozen = 1;
                        extra_frozen.push(lit.var());
                    }
                }

                self.eliminate(turn_off_simp)
            } else {
                true
            };

        let result =
            if elim_result {
                let mut result = self.core.solveLimited(assumptions);
                if let super::PartialResult::SAT(ref mut model) = result {
                    self.elimclauses.extendModel(model);
                }
                result
            } else {
                info!("===============================================================================");
                super::PartialResult::UnSAT
            };

        if do_simp {
            // Unfreeze the assumptions that were frozen:
            for v in extra_frozen.iter() {
                self.var_status[v].frozen = 0;
                if self.use_simplification {
                    self.elim.updateElimHeap(v, &self.var_status, &self.core.assigns);
                }
            }
        }

        result
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
            if self.core.budget.interrupted() {
                assert!(self.bwdsub_assigns == self.core.trail.totalSize());
                assert!(self.subsumption_queue.len() == 0);
                assert!(self.n_touched == 0);
                self.elim.clearHeap();
                break 'cleanup;
            }

            trace!("ELIM: vars = {}", self.elim.len());
            let mut cnt = 0;
            while let Some(elim) = self.elim.pop() {
                if self.core.budget.interrupted() { break; }
                if self.var_status[&elim].eliminated == 0 && self.core.assigns.undef(elim) {
                    if cnt % 100 == 0 {
                        trace!("elimination left: {:10}", self.elim.len());
                    }

                    if self.set.use_asymm {
                        // Temporarily freeze variable. Otherwise, it would immediately end up on the queue again:
                        let was_frozen = self.var_status[&elim].frozen;
                        self.var_status[&elim].frozen = 1;
                        if !self.asymmVar(elim) {
                            self.core.ok = false;
                            break 'cleanup;
                        }
                        self.var_status[&elim].frozen = was_frozen;
                    }

                    // At this point, the variable may have been set by assymetric branching, so check it
                    // again. Also, don't eliminate frozen variables:
                    if self.set.use_elim && self.core.assigns.undef(elim) && self.var_status[&elim].frozen == 0 && !self.eliminateVar(elim) {
                        self.core.ok = false;
                        break 'cleanup;
                    }

                    if self.core.db.ca.checkGarbage(self.set.simp_garbage_frac) {
                        self.garbageCollect();
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
            self.core.db.settings.remove_satisfied = true;
            self.core.db.ca.set_extra_clause_field(false);

            // Force full cleanup (this is safe and desirable since it only happens once):
            self.core.heur.rebuildOrderHeap(&self.core.assigns);
            self.core.garbageCollect();
        } else {
            // Cheaper cleanup:
            if self.core.db.ca.checkGarbage(self.core.settings.garbage_frac) {
                self.garbageCollect();
            }
        }

        self.elimclauses.logSize();
        self.core.ok
    }

    fn asymmVar(&mut self, v : Var) -> bool {
        assert!(self.use_simplification);

        let cls = {
            let cls = self.occurs.lookup(&v, &self.core.db.ca);
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
            let ref c = self.core.db.ca[cr];
            if c.mark() != 0 || satisfiedWith(c, &self.core.assigns) {
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

        match self.core.propagate() {
            None    => { self.core.cancelUntil(0); true }
            Some(_) => {
                self.core.cancelUntil(0);
                self.asymm_lits += 1;
                self.strengthenClause(cr, l.unwrap())
            }
        }
    }

    fn removeClause(&mut self, cr : ClauseRef) {
        if self.use_simplification {
            let ref c = self.core.db.ca[cr];

            for i in 0 .. c.len() {
                self.elim.bumpLitOcc(&c[i], -1);
                self.elim.updateElimHeap(&c[i].var(), &self.var_status, &self.core.assigns);
                self.occurs.smudge(&c[i].var());
            }
        }

        self.core.watches.unwatchClauseLazy(&self.core.db.ca[cr]);
        self.core.db.removeClause(&mut self.core.assigns, cr);
    }

    fn strengthenClause(&mut self, cr : ClauseRef, l : Lit) -> bool {
        assert!(self.core.trail.isGroundLevel());
        assert!(self.use_simplification);

        // FIX: this is too inefficient but would be nice to have (properly implemented)
        // if (!find(subsumption_queue, &c))
        self.subsumption_queue.push_back(cr);

        let len = self.core.db.ca[cr].len();
        if len == 2 {
            self.removeClause(cr);
            let unit = {
                let c = self.core.db.ca.edit(cr);
                c.strengthen(l);
                c[0]
            };
            self.core.enqueue(unit, None) && self.core.propagate().is_none()
        } else {
            self.core.watches.unwatchClauseStrict(&self.core.db.ca[cr], cr);
            self.core.db.editClause(cr, |c| { c.strengthen(l); assert!(c.len() == len - 1); });
            self.core.watches.watchClause(&self.core.db.ca[cr], cr);

            self.occurs.removeOcc(&l.var(), cr);
            self.elim.bumpLitOcc(&l, -1);
            self.elim.updateElimHeap(&l.var(), &self.var_status, &self.core.assigns);
            true
        }
    }

    fn eliminateVar(&mut self, v : Var) -> bool {
        assert!({ let ref st = self.var_status[&v]; st.frozen == 0 && st.eliminated == 0 });
        assert!(self.core.assigns.undef(v));

        // Split the occurrences into positive and negative:
        let cls = self.occurs.lookup(&v, &self.core.db.ca).clone();
        let mut pos = Vec::new();
        let mut neg = Vec::new();
        for cr in cls.iter() {
            let c = &self.core.db.ca[*cr];
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
                self.merges += 1;
                if let Some(resolvent) = merge(v, &self.core.db.ca[*pr], &self.core.db.ca[*nr]) {
                    cnt += 1;
                    if cnt > cls.len() + self.set.grow || (self.set.clause_lim != -1 && (resolvent.len() as i32) > self.set.clause_lim) {
                        return true;
                    }
                }
            }
        }

        // Delete and store old clauses:
        self.var_status[&v].eliminated = 1;
        self.core.heur.setDecisionVar(v, false);
        self.eliminated_vars += 1;

        if pos.len() > neg.len() {
            for cr in neg.iter() {
                self.elimclauses.mkElimClause(v, &self.core.db.ca[*cr]);
            }
            self.elimclauses.mkElimUnit(Lit::new(v, false));
        } else {
            for cr in pos.iter() {
                self.elimclauses.mkElimClause(v, &self.core.db.ca[*cr]);
            }
            self.elimclauses.mkElimUnit(Lit::new(v, true));
        }

        for cr in cls.iter() {
            self.removeClause(*cr);
        }

        // Produce clauses in cross product:
        for pr in pos.iter() {
            for nr in neg.iter() {
                self.merges += 1;
                if let Some(resolvent) = merge(v, &self.core.db.ca[*pr], &self.core.db.ca[*nr]) {
                    if !self.addClause(resolvent.borrow()) {
                        return false;
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
            if self.core.budget.interrupted() {
                self.subsumption_queue.clear();
                self.bwdsub_assigns = self.core.trail.totalSize();
                break;
            }

            let cr =
                match self.subsumption_queue.pop_front() {
                    Some(cr) => { cr }

                    // Check top-level assignments by creating a dummy clause and placing it in the queue:
                    None if self.bwdsub_assigns < self.core.trail.totalSize() => {
                        let c = self.core.db.ca.edit(self.bwdsub_tmpunit);
                        c[0] = self.core.trail[self.bwdsub_assigns];
                        c.calcAbstraction();

                        self.bwdsub_assigns += 1;
                        self.bwdsub_tmpunit
                    }

                    None => { break }
                };

            let best = {
                let ref c = self.core.db.ca[cr];

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
            for cj in self.occurs.lookup(&best, &self.core.db.ca).clone().iter() {
                if self.core.db.ca[cr].mark() != 0 {
                    break;
                } else if self.core.db.ca[*cj].mark() == 0 && *cj != cr && (self.set.subsumption_lim == -1 || (self.core.db.ca[*cj].len() as i32) < self.set.subsumption_lim) {
                    match subsumes(&self.core.db.ca[cr], &self.core.db.ca[*cj]) {
                        Subsumes::Different  => {}

                        Subsumes::Exact      => {
                            subsumed += 1;
                            self.removeClause(*cj);
                        }

                        Subsumes::LitSign(l) => {
                            deleted_literals += 1;
                            if !self.strengthenClause(*cj, !l) {
                                return false;
                            }
                        }
                    }
                }
            }
        }

        true
    }

    fn gatherTouchedClauses(&mut self) {
        if self.n_touched == 0 { return; }

        for cr in self.subsumption_queue.iter() {
            let c = self.core.db.ca.edit(*cr);
            if c.mark() == 0 {
                c.setMark(2);
            }
        }

        for (v, touched) in self.touched.iter_mut() {
            if *touched != 0 {
                for cr in self.occurs.lookup(&v, &self.core.db.ca) {
                    let c = self.core.db.ca.edit(*cr);
                    if c.mark() == 0 {
                        self.subsumption_queue.push_back(*cr);
                        c.setMark(2);
                    }
                }
                *touched = 0;
            }
        }

        for cr in self.subsumption_queue.iter() {
            let c = self.core.db.ca.edit(*cr);
            if c.mark() == 2 {
                c.setMark(0);
            }
        }

        self.n_touched = 0;
    }

    fn garbageCollect(&mut self) {
        let mut to = ClauseAllocator::newForGC(&self.core.db.ca);
        self.relocAll(&mut to);
        self.core.relocAll(to);
    }

    fn relocAll(&mut self, to : &mut ClauseAllocator) {
        if !self.use_simplification { return; }

        // All occurs lists:
        self.occurs.relocGC(&mut self.core.db.ca, to);

        // Subsumption queue:
        {
            let ref mut from = self.core.db.ca;
            self.subsumption_queue.retain(|cr| { !from[*cr].is_deleted() });
            for cr in self.subsumption_queue.iter_mut() {
                *cr = from.relocTo(to, *cr);
            }
        }

        // Temporary clause:
        self.bwdsub_tmpunit = self.core.db.ca.relocTo(to, self.bwdsub_tmpunit);
    }
}


fn implied(core : &mut super::CoreSolver, c : &[Lit]) -> bool {
    assert!(core.trail.isGroundLevel());

    core.trail.newDecisionLevel();
    for lit in c.iter() {
        match core.assigns.ofLit(*lit) {
            LitVal::True  => { core.cancelUntil(0); return true; }
            LitVal::Undef => { core.uncheckedEnqueue(!*lit, None); }
            LitVal::False => {}
        }
    }

    let result = core.propagate().is_some();
    core.cancelUntil(0);
    return result;
}


// Returns None if clause is always satisfied
fn merge(v : Var, _ps : &Clause, _qs : &Clause) -> Option<Vec<Lit>> {
    let ps_smallest = _ps.len() < _qs.len();
    let ref ps = if ps_smallest { _qs } else { _ps };
    let ref qs = if ps_smallest { _ps } else { _qs };

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


struct ElimClauses {
    extend_model : bool,
    literals     : Vec<Lit>,
    sizes        : Vec<usize>
}

impl ElimClauses {
    pub fn new(extend_model : bool) -> ElimClauses {
        ElimClauses { extend_model : extend_model
                    , literals     : Vec::new()
                    , sizes        : Vec::new()
                    }
    }

    pub fn mkElimUnit(&mut self, x : Lit) {
        self.literals.push(x);
        self.sizes.push(1);
    }

    pub fn mkElimClause(&mut self, v : Var, c : &Clause) {
        let first = self.literals.len();

        // Copy clause to elimclauses-vector. Remember position where the
        // variable 'v' occurs:
        let mut v_pos = 0;
        let mut v_found = false;
        for i in 0 .. c.len() {
            self.literals.push(c[i]);
            if c[i].var() == v {
                v_pos = i + first;
                v_found = true;
            }
        }
        assert!(v_found);

        // Swap the first literal with the 'v' literal, so that the literal
        // containing 'v' will occur first in the clause:
        self.literals.swap(first, v_pos);

        // Store the length of the clause last:
        self.sizes.push(c.len());
    }

    pub fn extendModel(&self, model : &mut VarMap<bool>) {
        if !self.extend_model { return; }

        let mut i = self.literals.len();
        let mut cl = self.sizes.len();
        while cl > 0 && i > 0 {
            cl -= 1;
            let mut j = self.sizes[cl];
            assert!(j > 0);

            i -= 1;
            let mut skip = false;
            while j > 1 {
                let x = self.literals[i];
                match model.get(&x.var()) {
                    Some(s) if *s == x.sign() => {}
                    _                         => { skip = true; break; }
                }

                j -= 1;
                i -= 1;
            }

            if !skip {
                let x = self.literals[i];
                model.insert(&x.var(), !x.sign());
            }

            if i > j - 1 {
                i -= j - 1;
            } else {
                i = 0
            }
        }
    }

    pub fn logSize(&self) {
        let sz = self.literals.len() + self.sizes.len();
        if sz > 0 {
            info!("|  Eliminated clauses:     {:10.2} Mb                                      |", ((sz * mem::size_of::<u32>()) as f64) / (1024.0 * 1024.0));
        }
    }
}
