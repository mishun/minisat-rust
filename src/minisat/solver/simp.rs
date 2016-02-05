use std::borrow::Borrow;
use std::default::Default;
use std::collections::vec_deque::VecDeque;
use std::mem;
use minisat::formula::{Var, Lit};
use minisat::formula::assignment::*;
use minisat::formula::clause::*;
use minisat::formula::index_map::{VarMap, LitMap, VarHeap};
use minisat::formula::util::*;
use super::{Solver, CoreSolver};


pub struct Settings {
    pub core         : super::Settings,
    pub simp         : SimpSettings,
    pub extend_model : bool // Flag to indicate whether the user needs to look at the full model.
}

impl Default for Settings {
    fn default() -> Settings {
        Settings {
            core         : Default::default(),
            simp         : Default::default(),
            extend_model : true
        }
    }
}


struct ElimQueue {
    heap  : VarHeap,
    n_occ : LitMap<i32>
}

impl ElimQueue {
    pub fn new() -> ElimQueue {
        ElimQueue {
            heap  : VarHeap::new(),
            n_occ : LitMap::new()
        }
    }

    pub fn initVar(&mut self, v : Var) {
        self.n_occ.insert(&v.posLit(), 0);
        self.n_occ.insert(&v.negLit(), 0);

        let ref n_occ = self.n_occ;
        self.heap.insert(v, |a, b| { Self::before(n_occ, a, b) });
    }

    #[inline]
    fn before(n_occ : &LitMap<i32>, a : &Var, b : &Var) -> bool {
        let costA = (n_occ[&a.posLit()] as u64) * (n_occ[&a.negLit()] as u64);
        let costB = (n_occ[&b.posLit()] as u64) * (n_occ[&b.negLit()] as u64);
        costA < costB
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.heap.len()
    }

    fn updateElimHeap(&mut self, v : Var, var_status : &VarMap<VarStatus>, assigns : &Assignment) {
        let ref n_occ = self.n_occ;
        if self.heap.contains(&v) {
            self.heap.update(&v, |a, b| { Self::before(n_occ, a, b) });
        } else if var_status[&v].frozen == 0 && var_status[&v].eliminated == 0 && assigns.isUndef(v) {
            self.heap.insert(v, |a, b| { Self::before(n_occ, a, b) });
        }
    }

    pub fn clear(&mut self) {
        self.heap.clear();
    }

    pub fn bumpLitOcc(&mut self, lit : &Lit, delta : i32) {
        self.n_occ[lit] += delta;

        let ref n_occ = self.n_occ;
        self.heap.update(&lit.var(), |a, b| { Self::before(n_occ, a, b) });
    }

    pub fn pop(&mut self) -> Option<Var>
    {
        let ref n_occ = self.n_occ;
        self.heap.pop(|a, b| { Self::before(n_occ, a, b) })
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
            ol.occs.retain(|cr| { !ca.isDeleted(*cr) });
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

    pub fn relocGC(&mut self, from : &mut ClauseAllocator, to : &mut ClauseAllocator) {
        for (_, ol) in self.occs.iter_mut() {
            if ol.dirty {
                ol.occs.retain(|cr| { !from.isDeleted(*cr) });
                ol.dirty = false;
            }

            for occ in ol.occs.iter_mut() {
                *occ = from.relocTo(to, *occ);
            }
        }
    }
}


pub struct SimpSolver {
    core        : CoreSolver,
    elimclauses : ElimClauses,
    simp        : Option<Simplificator>
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
        if let Some(ref mut simp) = self.simp {
            simp.initVar(v);
        }
        v
    }

    fn addClause(&mut self, ps : &[Lit]) -> bool {
        match self.simp {
            Some(ref mut simp) => { simp.addClause(&mut self.core, ps) }
            None               => { self.core.addClause(ps) }
        }
    }

    fn printStats(&self) {
        self.core.printStats();
    }
}

impl SimpSolver {
    pub fn new(settings : Settings) -> SimpSolver {
        let mut core = CoreSolver::new(settings.core);
        core.db.ca.set_extra_clause_field(true);
        core.db.settings.remove_satisfied = false;
        SimpSolver { core        : core
                   , elimclauses : ElimClauses::new(settings.extend_model)
                   , simp        : Some(Simplificator::new(settings.simp))
                   }
    }

    pub fn solveLimited(&mut self, assumptions : &[Lit], do_simp : bool, turn_off_simp : bool) -> super::PartialResult {
        let mut result =
            match self.simp {
                Some(ref mut simp) if do_simp => {
                    simp.solveLimited(&mut self.core, &mut self.elimclauses, assumptions)
                }

                _ => {
                    self.core.solveLimited(assumptions)
                }
            };

        if let super::PartialResult::SAT(ref mut model) = result {
            self.elimclauses.extendModel(model);
        }

        if turn_off_simp {
            self.simpOff();
        }

        result
    }

    pub fn eliminate(&mut self, turn_off_elim : bool) -> bool {
        if !self.core.simplify() {
            return false;
        }

        let result =
            if let Some(ref mut simp) = self.simp {
                let result = simp.eliminate(&mut self.core, &mut self .elimclauses);
                if !turn_off_elim && self.core.db.ca.checkGarbage(self.core.settings.garbage_frac) {
                    simp.garbageCollect(&mut self.core);
                }
                result
            } else {
                return true;
            };

        if turn_off_elim {
            self.simpOff();
        }

        self.elimclauses.logSize();
        result
    }

    fn simpOff(&mut self) {
        if let Some(_) = self.simp {
            self.simp = None;
            self.core.db.settings.remove_satisfied = true;
            self.core.db.ca.set_extra_clause_field(false);

            // Force full cleanup (this is safe and desirable since it only happens once):
            self.core.heur.rebuildOrderHeap(&self.core.assigns);
            self.core.garbageCollect();
        }
    }
}


pub struct SimpSettings {
    pub grow              : usize, // Allow a variable elimination step to grow by a number of clauses (default to zero).
    pub clause_lim        : i32,   // Variables are not eliminated if it produces a resolvent with a length above this limit. -1 means no limit.
    pub subsumption_lim   : i32,   // Do not check if subsumption against a clause larger than this. -1 means no limit.
    pub simp_garbage_frac : f64,   // A different limit for when to issue a GC during simplification (Also see 'garbage_frac').
    pub use_asymm         : bool,  // Shrink clauses by asymmetric branching.
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
            use_elim          : true
        }
    }
}


struct VarStatus {
    frozen     : i8,
    eliminated : i8
}

struct Simplificator {
    settings          : SimpSettings,

    // Statistics:
    merges            : u64,
    asymm_lits        : u64,
    eliminated_vars   : u64,

    var_status        : VarMap<VarStatus>,
    occurs            : OccLists,
    elim              : ElimQueue,
    touched           : VarMap<i8>,
    n_touched         : usize,
    subsumption_queue : SubsumptionQueue
}

impl Simplificator {
    pub fn new(settings : SimpSettings) -> Simplificator {
        Simplificator { settings           : settings
                      , merges             : 0
                      , asymm_lits         : 0
                      , eliminated_vars    : 0
                      , var_status         : VarMap::new()
                      , occurs             : OccLists::new()
                      , elim               : ElimQueue::new()
                      , touched            : VarMap::new()
                      , n_touched          : 0
                      , subsumption_queue  : SubsumptionQueue::new()
                      }
    }

    fn initVar(&mut self, v : Var) {
        self.var_status.insert(&v, VarStatus { frozen : 0, eliminated : 0 });
        self.occurs.initVar(&v);
        self.touched.insert(&v, 0);
        self.elim.initVar(v);
    }

    fn addClause(&mut self, core : &mut CoreSolver, ps : &[Lit]) -> bool {
        //#ifndef NDEBUG
        for l in ps.iter() {
            assert!(self.var_status[&l.var()].eliminated == 0);
        }
        //#endif

        match core.addClause_(ps) {
            super::AddClause::UnSAT     => { false }
            super::AddClause::Consumed  => { true }
            super::AddClause::Added(cr) => {
                // NOTE: the clause is added to the queue immediately and then
                // again during 'gatherTouchedClauses()'. If nothing happens
                // in between, it will only be checked once. Otherwise, it may
                // be checked twice unnecessarily. This is an unfortunate
                // consequence of how backward subsumption is used to mimic
                // forward subsumption.
                self.subsumption_queue.push(cr);

                for lit in core.db.ca.view(cr).iter() {
                    self.occurs.pushOcc(&lit.var(), cr);
                    self.touched[&lit.var()] = 1;
                    self.n_touched += 1;
                    self.elim.bumpLitOcc(&lit, 1);
                }

                true
            }
        }
    }

    fn solveLimited(&mut self, core : &mut CoreSolver, elimclauses : &mut ElimClauses, assumptions : &[Lit]) -> super::PartialResult {
        let mut extra_frozen : Vec<Var> = Vec::new();

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

        let result =
            if core.simplify() && self.eliminate(core, elimclauses) {
                core.solveLimited(assumptions)
            } else {
                info!("===============================================================================");
                super::PartialResult::UnSAT
            };

        // Unfreeze the assumptions that were frozen:
        for v in extra_frozen.iter() {
            self.var_status[v].frozen = 0;
            self.elim.updateElimHeap(*v, &self.var_status, &core.assigns);
        }

        result
    }

    fn eliminate(&mut self, core : &mut CoreSolver, elimclauses : &mut ElimClauses) -> bool {
        // Main simplification loop:
        'cleanup: while self.n_touched > 0 || self.subsumption_queue.bwdsub_assigns < core.assigns.numberOfAssigns() || self.elim.len() > 0 {
            self.gatherTouchedClauses(&mut core.db.ca);

            if !self.backwardSubsumptionCheck(core, true) {
                core.ok = false;
                break 'cleanup;
            }

            // Empty elim_heap and return immediately on user-interrupt:
            if core.budget.interrupted() {
                assert!(self.subsumption_queue.bwdsub_assigns == core.assigns.numberOfAssigns());
                assert!(self.subsumption_queue.len() == 0);
                assert!(self.n_touched == 0);
                self.elim.clear();
                break 'cleanup;
            }

            trace!("ELIM: vars = {}", self.elim.len());
            let mut cnt = 0;
            while let Some(elim) = self.elim.pop() {
                if core.budget.interrupted() { break; }
                if self.var_status[&elim].eliminated == 0 && core.assigns.isUndef(elim) {
                    if cnt % 100 == 0 {
                        trace!("elimination left: {:10}", self.elim.len());
                    }

                    if self.settings.use_asymm {
                        // Temporarily freeze variable. Otherwise, it would immediately end up on the queue again:
                        let was_frozen = self.var_status[&elim].frozen;
                        self.var_status[&elim].frozen = 1;
                        if !self.asymmVar(core, elim) {
                            core.ok = false;
                            break 'cleanup;
                        }
                        self.var_status[&elim].frozen = was_frozen;
                    }

                    // At this point, the variable may have been set by assymetric branching, so check it
                    // again. Also, don't eliminate frozen variables:
                    if self.settings.use_elim && core.assigns.isUndef(elim) && self.var_status[&elim].frozen == 0 && !self.eliminateVar(core, elimclauses, elim) {
                        core.ok = false;
                        break 'cleanup;
                    }

                    if core.db.ca.checkGarbage(self.settings.simp_garbage_frac) {
                        self.garbageCollect(core);
                    }
                }

                cnt += 1;
            }

            assert!(self.subsumption_queue.len() == 0);
        }

        core.ok
    }

    fn asymmVar(&mut self, core : &mut CoreSolver, v : Var) -> bool {
        let cls = {
            let cls = self.occurs.lookup(&v, &core.db.ca);
            if !core.assigns.isUndef(v) || cls.len() == 0 {
                return true;
            }
            cls.clone()
        };

        let mut bug = false;
        for cr in cls.iter() {
            // TODO: this mimics original MiniSat bug. Fix it?
            if bug { bug = false; continue; }

            if let Some(l) = asymmetricBranching(core, v, *cr) {
                if core.db.ca.view(*cr).len() > 2 { bug = true; }

                self.asymm_lits += 1;
                if !self.strengthenClause(core, *cr, l) {
                    return false;
                }
            }
        }

        self.backwardSubsumptionCheck(core, false)
    }

    fn removeClause(&mut self, core : &mut CoreSolver, cr : ClauseRef) {
        for lit in core.db.ca.view(cr).iter() {
            self.elim.bumpLitOcc(&lit, -1);
            self.elim.updateElimHeap(lit.var(), &self.var_status, &core.assigns);
            self.occurs.smudge(&lit.var());
        }

        core.watches.unwatchClauseLazy(core.db.ca.view(cr));
        core.db.removeClause(&mut core.assigns, cr);
    }

    fn strengthenClause(&mut self, core : &mut CoreSolver, cr : ClauseRef, l : Lit) -> bool {
        assert!(core.assigns.isGroundLevel());

        // FIX: this is too inefficient but would be nice to have (properly implemented)
        // if (!find(subsumption_queue, &c))
        self.subsumption_queue.push(cr);

        let len = core.db.ca.view(cr).len();
        if len == 2 {
            self.removeClause(core, cr);
            let unit = { let c = core.db.ca.edit(cr); c.strengthen(l); c.head() }; // TODO: it produces clauses of length 1. Not good.
            tryAssignLit(&mut core.assigns, unit, None) && core.watches.propagate(&mut core.db.ca, &mut core.assigns).is_none()
        } else {
            core.watches.unwatchClauseStrict(core.db.ca.view(cr), cr);
            core.db.editClause(cr, |c| { c.strengthen(l); assert!(c.len() == len - 1); });
            core.watches.watchClause(core.db.ca.view(cr), cr);

            self.occurs.removeOcc(&l.var(), cr);
            self.elim.bumpLitOcc(&l, -1);
            self.elim.updateElimHeap(l.var(), &self.var_status, &core.assigns);
            true
        }
    }

    fn eliminateVar(&mut self, core : &mut CoreSolver, elimclauses : &mut ElimClauses, v : Var) -> bool {
        assert!({ let ref st = self.var_status[&v]; st.frozen == 0 && st.eliminated == 0 });
        assert!(core.assigns.isUndef(v));

        // Split the occurrences into positive and negative:
        let cls = self.occurs.lookup(&v, &core.db.ca).clone();
        let mut pos = Vec::new();
        let mut neg = Vec::new();
        for cr in cls.iter() {
            for l in core.db.ca.view(*cr).iter() {
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
                if let Some(resolvent) = merge(v, core.db.ca.view(*pr), core.db.ca.view(*nr)) {
                    cnt += 1;
                    if cnt > cls.len() + self.settings.grow || (self.settings.clause_lim != -1 && (resolvent.len() as i32) > self.settings.clause_lim) {
                        return true;
                    }
                }
            }
        }

        // Delete and store old clauses:
        self.var_status[&v].eliminated = 1;
        core.heur.setDecisionVar(v, false);
        self.eliminated_vars += 1;

        if pos.len() > neg.len() {
            for cr in neg.iter() {
                elimclauses.mkElimClause(v, core.db.ca.view(*cr));
            }
            elimclauses.mkElimUnit(v.posLit());
        } else {
            for cr in pos.iter() {
                elimclauses.mkElimClause(v, core.db.ca.view(*cr));
            }
            elimclauses.mkElimUnit(v.negLit());
        }

        for cr in cls.iter() {
            self.removeClause(core, *cr);
        }

        // Produce clauses in cross product:
        for pr in pos.iter() {
            for nr in neg.iter() {
                self.merges += 1;
                if let Some(resolvent) = merge(v, core.db.ca.view(*pr), core.db.ca.view(*nr)) {
                    if !self.addClause(core, resolvent.borrow()) {
                        return false;
                    }
                }
            }
        }

        // Free occurs list for this variable:
        self.occurs.clearVar(&v);

        // Free watchers lists for this variable, if possible:
        core.watches.tryClearVar(v);

        self.backwardSubsumptionCheck(core, false)
    }

    // Backward subsumption + backward subsumption resolution
    fn backwardSubsumptionCheck(&mut self, core : &mut CoreSolver, verbose : bool) -> bool {
        assert!(core.assigns.isGroundLevel());

        if verbose {
            trace!("BWD-SUB: queue = {}, trail = {}", self.subsumption_queue.len()
                                                    , core.assigns.numberOfAssigns() - self.subsumption_queue.bwdsub_assigns);
        }

        let mut cnt = 0u64;
        let mut subsumed = 0u64;
        let mut deleted_literals = 0u64;

        while let Some(job) = self.subsumption_queue.pop(&core.db.ca, &core.assigns) {
            // Empty subsumption queue and return immediately on user-interrupt:
            if core.budget.interrupted() {
                self.subsumption_queue.clear(&core.assigns);
                break;
            }

            if verbose && cnt % 1000 == 0 {
                trace!("subsumption left: {:10} ({:10} subsumed, {:10} deleted literals)",
                    self.subsumption_queue.len(), subsumed, deleted_literals);
            }
            cnt += 1;

            match job {
                SubsumptionJob::Assign(unit) => {
                    for cj in self.occurs.lookup(&unit.var(), &core.db.ca).clone().iter() {
                        if { let c = core.db.ca.view(*cj); c.mark() == 0 && (self.settings.subsumption_lim == -1 || (c.len() as i32) < self.settings.subsumption_lim) } {
                            match unitSubsumes(unit, core.db.ca.view(*cj)) {
                                Subsumes::Different  => {}

                                Subsumes::Exact      => {
                                    subsumed += 1;
                                    self.removeClause(core, *cj);
                                }

                                Subsumes::LitSign(l) => {
                                    deleted_literals += 1;
                                    if !self.strengthenClause(core, *cj, !l) {
                                        return false;
                                    }
                                }
                            }
                        }
                    }
                }

                SubsumptionJob::Clause(cr)  => {
                    let best = {
                        let c = core.db.ca.view(cr);
                        let mut best = c.head().var();
                        for lit in c.iterFrom(1) {
                            // TODO: why not use n_occ?
                            if self.occurs.getDirty(&lit.var()).len() < self.occurs.getDirty(&best).len() {
                                best = lit.var();
                            }
                        }
                        best
                    };

                    for cj in self.occurs.lookup(&best, &core.db.ca).clone().iter() {
                        if core.db.ca.isDeleted(cr) {
                            break;
                        }

                        if *cj != cr && { let c = core.db.ca.view(*cj); c.mark() == 0 && (self.settings.subsumption_lim == -1 || (c.len() as i32) < self.settings.subsumption_lim) } {
                            match subsumes(core.db.ca.view(cr), core.db.ca.view(*cj)) {
                                Subsumes::Different  => {}

                                Subsumes::Exact      => {
                                    subsumed += 1;
                                    self.removeClause(core, *cj);
                                }

                                Subsumes::LitSign(l) => {
                                    deleted_literals += 1;
                                    if !self.strengthenClause(core, *cj, !l) {
                                        return false;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        true
    }

    fn gatherTouchedClauses(&mut self, ca : &mut ClauseAllocator) {
        if self.n_touched == 0 { return; }

        self.subsumption_queue.remarkQueued(ca, 0, 2);

        for (v, touched) in self.touched.iter_mut() {
            if *touched != 0 {
                for cr in self.occurs.lookup(&v, ca) {
                    let c = ca.edit(*cr);
                    if c.mark() == 0 {
                        self.subsumption_queue.push(*cr);
                        c.setMark(2);
                    }
                }
                *touched = 0;
            }
        }

        self.subsumption_queue.remarkQueued(ca, 2, 0);
        self.n_touched = 0;
    }

    fn garbageCollect(&mut self, core : &mut CoreSolver) {
        let mut to = ClauseAllocator::newForGC(&core.db.ca);
        self.relocAll(&mut core.db.ca, &mut to);
        core.relocAll(to);
    }

    fn relocAll(&mut self, from : &mut ClauseAllocator, to : &mut ClauseAllocator) {
        self.occurs.relocGC(from, to);
        self.subsumption_queue.relocGC(from, to);
    }
}


fn asymmetricBranching(core : &mut CoreSolver, v : Var, cr : ClauseRef) -> Option<Lit> {
    assert!(core.assigns.isGroundLevel());

    let l = {
        let c = core.db.ca.view(cr);
        if c.mark() != 0 || satisfiedWith(c, &core.assigns) {
            return None;
        }

        core.assigns.newDecisionLevel();

        let mut vl = None;
        for lit in c.iter() {
            if v == lit.var() {
                vl = Some(lit);
            } else if core.assigns.isUndef(lit.var()) {
                core.assigns.assignLit(!lit, None);
            }
        }

        vl.unwrap()
    };

    let res = core.watches.propagate(&mut core.db.ca, &mut core.assigns);
    core.cancelUntil(GroundLevel);
    res.map(|_| l)
}


struct SubsumptionQueue {
    subsumption_queue : VecDeque<ClauseRef>,
    bwdsub_assigns    : usize
}

enum SubsumptionJob {
    Clause(ClauseRef),
    Assign(Lit)
}

impl SubsumptionQueue {
    pub fn new() -> Self {
        SubsumptionQueue { subsumption_queue : VecDeque::new()
                         , bwdsub_assigns    : 0
                         }
    }

    pub fn pop(&mut self, ca : &ClauseAllocator, assigns : &Assignment) -> Option<SubsumptionJob> {
        loop {
            match self.subsumption_queue.pop_front() {
                Some(cr) => {
                    if !ca.isDeleted(cr) {
                        return Some(SubsumptionJob::Clause(cr));
                    }
                }

                None if self.bwdsub_assigns < assigns.numberOfAssigns() => {
                    let lit = assigns.assignAt(self.bwdsub_assigns);
                    self.bwdsub_assigns += 1;
                    return Some(SubsumptionJob::Assign(lit));
                }

                None => {
                    return None;
                }
            }
        }
    }

    pub fn push(&mut self, cr : ClauseRef) {
        self.subsumption_queue.push_back(cr);
    }

    pub fn len(&self) -> usize {
        self.subsumption_queue.len()
    }

    pub fn clear(&mut self, assigns : &Assignment) {
        self.subsumption_queue.clear();
        self.bwdsub_assigns = assigns.numberOfAssigns();
    }

    pub fn remarkQueued(&mut self, ca : &mut ClauseAllocator, src : u32, dst : u32) {
        for cr in self.subsumption_queue.iter() {
            let c = ca.edit(*cr);
            if c.mark() == src {
                c.setMark(dst);
            }
        }
    }

    pub fn relocGC(&mut self, from : &mut ClauseAllocator, to : &mut ClauseAllocator) {
        self.subsumption_queue.retain(|cr| { !from.isDeleted(*cr) });
        for cr in self.subsumption_queue.iter_mut() {
            *cr = from.relocTo(to, *cr);
        }
    }
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
        let mut v_pos = first;
        let mut v_found = false;
        for lit in c.iter() {
            self.literals.push(lit);
            if lit.var() == v {
                v_found = true;
            } else if !v_found {
                v_pos += 1;
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
