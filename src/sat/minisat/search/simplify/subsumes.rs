use crate::formula::{clause::*, Lit};


pub enum Subsumes {
    Different,
    Exact,
    LitSign(Lit),
}

pub fn subsumes(this: &Clause, other: &Clause) -> Subsumes {
    assert!(!this.header.learnt);
    assert!(!other.header.learnt);

    if other.len() < this.len() || (this.header.abstraction & !other.header.abstraction) != 0 {
        return Subsumes::Different;
    }

    let mut ret = Subsumes::Exact;
    for &lit in this.lits() {
        // search for lit or ¬lit
        let mut found = false;
        for &cur in other.lits() {
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

pub fn unit_subsumes(unit: Lit, c: &Clause) -> Subsumes {
    assert!(!c.header.learnt);

    if unit.abstraction() & !c.header.abstraction != 0 {
        return Subsumes::Different;
    }

    for &cur in c.lits() {
        if unit == cur {
            return Subsumes::Exact;
        } else if unit == !cur {
            return Subsumes::LitSign(unit);
        }
    }

    return Subsumes::Different;
}
