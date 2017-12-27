use super::{Lit, Var};
use super::assignment::*;
use super::clause::*;


// Returns true if a clause is satisfied with assignment
pub fn satisfied_with(c: &Clause, s: &Assignment) -> bool {
    for &lit in c.lits() {
        if s.is_assigned_pos(lit) {
            return true;
        }
    }
    false
}


// Returns None if clause is always satisfied
pub fn merge(v: Var, _ps: &Clause, _qs: &Clause) -> Option<Vec<Lit>> {
    let (ps, qs) = if _ps.len() < _qs.len() {
        (_qs, _ps)
    } else {
        (_ps, _qs)
    };

    let mut res = Vec::new();
    for &qsi in qs.lits() {
        if qsi.var() != v {
            let mut ok = true;

            for &psj in ps.lits() {
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

    for &psi in ps.lits() {
        if psi.var() != v {
            res.push(psi);
        }
    }

    Some(res)
}
