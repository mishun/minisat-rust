use super::{assignment::Assignment, Lit, Var};


pub fn calc_abstraction(lits: &[Lit]) -> u32 {
    let mut abstraction: u32 = 0;
    for lit in lits {
        abstraction |= lit.abstraction();
    }
    abstraction
}


// Returns true if a clause is satisfied with assignment
pub fn satisfied_with(clause: &[Lit], s: &Assignment) -> bool {
    for &lit in clause {
        if s.is_assigned_pos(lit) {
            return true;
        }
    }
    false
}


// Returns None if clause is always satisfied
pub fn merge(v: Var, _ps: &[Lit], _qs: &[Lit]) -> Option<Vec<Lit>> {
    let (ps, qs) = if _ps.len() < _qs.len() { (_qs, _ps) } else { (_ps, _qs) };

    let mut res = Vec::new();
    for &qsi in qs {
        if qsi.var() != v {
            let mut ok = true;

            for &psj in ps {
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

    for &psi in ps {
        if psi.var() != v {
            res.push(psi);
        }
    }

    Some(res)
}
