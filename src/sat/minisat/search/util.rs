use crate::sat::formula::{assignment::*, clause::*, util::*, LBool, Lit, Var};
use super::{backtrack::*, decision_heuristic::*};


pub fn progress_estimate(assigns: &Assignment) -> f64 {
    let vars = 1.0 / (assigns.number_of_vars() as f64);
    let mut progress = 0.0;
    let mut factor = vars;
    for (_, level_trail) in assigns.all_levels_dir() {
        progress += factor * (level_trail.len() as f64);
        factor *= vars;
    }
    progress
}

pub fn is_implied(bt: &mut BacktrackableFormula, heur: &mut DecisionHeuristic, c: &[Lit]) -> bool {
    assert!(bt.is_ground_level());

    bt.assigns.new_decision_level();
    for &lit in c.iter() {
        match bt.assigns.of_lit(lit) {
            LBool::True => {
                for &lit in bt.assigns.trail_above(GROUND_LEVEL) {
                    heur.save_phase(lit, true);
                }
                bt.assigns.backtrack_to(GROUND_LEVEL);
                return true;
            }
            LBool::Undef => {
                bt.assigns.assign_lit(!lit, None);
            }
            LBool::False => {}
        }
    }

    let result = bt.propagate().is_some();
    for &lit in bt.assigns.trail_above(GROUND_LEVEL) {
        heur.save_phase(lit, true);
    }
    bt.assigns.backtrack_to(GROUND_LEVEL);
    return result;
}

pub fn asymmetric_branching(bt: &mut BacktrackableFormula, heur: &mut DecisionHeuristic, v: Var, cr: ClauseRef) -> Option<Lit> {
    assert!(bt.is_ground_level());

    let l = {
        let c = bt.ca.view(cr);
        if c.is_deleted() || satisfied_with_assignment(c.lits(), &bt.assigns) {
            return None;
        }

        bt.assigns.new_decision_level();

        let mut vl = None;
        for &lit in c.lits() {
            if v == lit.var() {
                vl = Some(lit);
            } else if bt.assigns.is_undef(lit.var()) {
                bt.assigns.assign_lit(!lit, None);
            }
        }

        vl.unwrap()
    };

    let confl = bt.propagate();
    for &lit in bt.assigns.trail_above(GROUND_LEVEL) {
        heur.save_phase(lit, true);
    }
    bt.assigns.backtrack_to(GROUND_LEVEL);
    confl.map(|_| l)
}
