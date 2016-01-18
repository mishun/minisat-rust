use std::default::{Default};
use minisat::index_map::{IndexMap};
use minisat::lbool::{LBool};
use minisat::literal::{Var, Lit};
use minisat::clause::{Clause, ClauseRef};
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


struct SimpSolver {
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

    //OccLists<Var, vec<CRef>, ClauseDeleted> occurs;
    n_occ              : IndexMap<Lit, i32>,
    //Heap<Var,ElimLt>    elim_heap;
    //Queue<CRef>         subsumption_queue;
    frozen             : IndexMap<Var, i8>,
    frozen_vars        : Vec<Var>,
    eliminated         : IndexMap<Var, i8>,
    bwdsub_assigns     : i32,
    n_touched          : i32,

    // Temporaries:
    bwdsub_tmpunit     : ClauseRef,
}

impl SimpSolver {

    fn solve_(&mut self, mut do_simp : bool, turn_off_simp : bool) -> LBool {
        let mut extra_frozen : Vec<Var> = Vec::new();
        let mut result = LBool::True();

        do_simp &= self.use_simplification;
        if do_simp {
            // Assumptions must be temporarily frozen to run variable elimination:
            for lit in self.core.assumptions.iter() {
                let v = lit.var();

                // If an assumption has been eliminated, remember it.
                assert!(!self.isEliminated(&v));

                if self.frozen[&v] == 0 {
                    // Freeze and store.
                    //self.setFrozen(v, true);
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
                self.setFrozen(v, false);
            }
        }

        result
    }

    fn isEliminated(&self, v : &Var) -> bool {
        self.eliminated[v] != 0
    }

    fn setFrozen(&mut self, v : &Var, b : bool) {
        self.frozen[v] = b as i8;
        if self.use_simplification && !b {
            //self.updateElimHeap(v);
        }
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
/*
        // Main simplification loop:
        //
        while (n_touched > 0 || bwdsub_assigns < trail.size() || elim_heap.size() > 0){

            gatherTouchedClauses();
            // printf("  ## (time = %6.2f s) BWD-SUB: queue = %d, trail = %d\n", cpuTime(), subsumption_queue.size(), trail.size() - bwdsub_assigns);
            if ((subsumption_queue.size() > 0 || bwdsub_assigns < trail.size()) &&
                !backwardSubsumptionCheck(true)){
                ok = false; goto cleanup; }

            // Empty elim_heap and return immediately on user-interrupt:
            if (asynch_interrupt){
                assert(bwdsub_assigns == trail.size());
                assert(subsumption_queue.size() == 0);
                assert(n_touched == 0);
                elim_heap.clear();
                goto cleanup; }

            // printf("  ## (time = %6.2f s) ELIM: vars = %d\n", cpuTime(), elim_heap.size());
            for (int cnt = 0; !elim_heap.empty(); cnt++){
                Var elim = elim_heap.removeMin();

                if (asynch_interrupt) break;

                if (isEliminated(elim) || value(elim) != l_Undef) continue;

                if (verbosity >= 2 && cnt % 100 == 0)
                    printf("elimination left: %10d\r", elim_heap.size());

                if (use_asymm){
                    // Temporarily freeze variable. Otherwise, it would immediately end up on the queue again:
                    bool was_frozen = frozen[elim];
                    frozen[elim] = true;
                    if (!asymmVar(elim)){
                        ok = false; goto cleanup; }
                    frozen[elim] = was_frozen; }

                // At this point, the variable may have been set by assymetric branching, so check it
                // again. Also, don't eliminate frozen variables:
                if (use_elim && value(elim) == l_Undef && !frozen[elim] && !eliminateVar(elim)){
                    ok = false; goto cleanup; }

                checkGarbage(simp_garbage_frac);
            }

            assert(subsumption_queue.size() == 0);
        }
    cleanup:

        // If no more simplification is needed, free all simplification-related data structures:
        if (turn_off_elim){
            touched  .clear(true);
            occurs   .clear(true);
            n_occ    .clear(true);
            elim_heap.clear(true);
            subsumption_queue.clear(true);

            use_simplification    = false;
            remove_satisfied      = true;
            ca.extra_clause_field = false;
            max_simp_var          = nVars();

            // Force full cleanup (this is safe and desirable since it only happens once):
            rebuildOrderHeap();
            garbageCollect();
        }else{
            // Cheaper cleanup:
            checkGarbage();
        }

        if (verbosity >= 1 && elimclauses.size() > 0)
            printf("|  Eliminated clauses:     %10.2f Mb                                      |\n",
                   double(elimclauses.size() * sizeof(uint32_t)) / (1024*1024));
*/
        self.core.ok
    }

}
