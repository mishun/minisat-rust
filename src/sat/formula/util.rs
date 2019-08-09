use std::num;
use super::{assignment::Assignment, Lit, Var, VarMap};


pub fn calc_abstraction(lits: &[Lit]) -> num::NonZeroU32 {
    let mut abstraction: u32 = 0;
    for lit in lits {
        abstraction |= lit.abstraction();
    }
    num::NonZeroU32::new(abstraction).unwrap()
}


// Returns true if a clause is satisfied with assignment
pub fn satisfied_with_assignment(clause: &[Lit], assignment: &Assignment) -> bool {
    for &lit in clause {
        if assignment.is_assigned_pos(lit) {
            return true;
        }
    }
    false
}

pub fn satisfied_with_model(clause: &[Lit], model: &VarMap<bool>) -> bool {
    for &lit in clause {
        match model.get(&lit.var()) {
            Some(sign) if *sign != lit.sign() => return true,
            _ => {}
        }
    }
    false
}


pub fn extract_model(assigns: &Assignment) -> VarMap<bool> {
    let mut model = VarMap::new();
    for lit in assigns.trail() {
        model.insert(&lit.var(), !lit.sign());
    }
    model
}


// Returns None if clause is always satisfied
pub fn merge(v: Var, _ps: &[Lit], _qs: &[Lit]) -> Option<Vec<Lit>> {
    let (longer, shorter) = if _ps.len() < _qs.len() { (_qs, _ps) } else { (_ps, _qs) };

    let mut res = Vec::with_capacity(longer.len() + shorter.len());
    for &qsi in shorter {
        if qsi.var() != v {
            let mut ok = true;

            for &psj in longer {
                if psj.var() == qsi.var() {
                    if psj == !qsi {
                        return None;
                    } else {
                        ok = false;
                        break;
                    }
                }
            }

            if ok {
                res.push(qsi);
            }
        }
    }

    for &lit in longer {
        if lit.var() != v {
            res.push(lit);
        }
    }

    Some(res)
}
