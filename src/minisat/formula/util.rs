use super::Lit;
use super::assignment::*;
use super::clause::*;


// Returns true if a clause is satisfied with assignment
pub fn satisfiedWith(c : &Clause, s : &Assignment) -> bool {
    for i in 0 .. c.len() {
        if s.sat(c[i]) {
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
