use super::{Var, Lit};
use super::assignment::*;
use super::clause::*;


// Returns true if a clause is satisfied with assignment
pub fn satisfiedWith(c : &Clause, s : &Assignment) -> bool {
    for lit in c.iter() {
        if s.isSat(lit) {
            return true;
        }
    }
    false
}


pub enum Subsumes {
    Different,
    Exact,
    LitSign(Lit)
}

pub fn subsumes(this : &Clause, other : &Clause) -> Subsumes {
    assert!(!this.is_learnt());
    assert!(!other.is_learnt());

    if other.len() < this.len() || (this.abstraction() & !other.abstraction()) != 0 {
        return Subsumes::Different;
    }

    let mut ret = Subsumes::Exact;
    for lit in this.iter() {
        // search for lit or ¬lit
        let mut found = false;
        for cur in other.iter() {
            if lit == cur {
                found = true;
                break;
            } else if lit == !cur {
                if let Subsumes::Exact = ret {
                    ret = Subsumes::LitSign(lit);
                    found = true;
                    break;
                } else {
                    return Subsumes::Different;
                }
            }
        }

        // did not find it
        if !found {
            return Subsumes::Different;
        }
    }

    return ret;
}


// Returns None if clause is always satisfied
pub fn merge(v : Var, _ps : &Clause, _qs : &Clause) -> Option<Vec<Lit>> {
    let ps_smallest = _ps.len() < _qs.len();
    let ref ps = if ps_smallest { _qs } else { _ps };
    let ref qs = if ps_smallest { _ps } else { _qs };

    let mut res = Vec::new();
    for qsi in qs.iter() {
        if qsi.var() != v {
            let mut ok = true;

            for psj in ps.iter() {
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

    for psi in ps.iter() {
        if psi.var() != v {
            res.push(psi);
        }
    }

    Some(res)
}
