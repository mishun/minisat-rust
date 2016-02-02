use super::{Var, Lit};
use super::assignment::*;
use super::clause::*;


// Returns true if a clause is satisfied with assignment
pub fn satisfiedWith(c : &Clause, s : &Assignment) -> bool {
    for i in 0 .. c.len() {
        if s.isSat(c[i]) {
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
    for i in 0 .. this.len() {
        let lit = this[i];

        // search for lit or ¬lit
        let mut found = false;
        for j in 0 .. other.len() {
            let cur = other[j];
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
