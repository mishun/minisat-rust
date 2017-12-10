use std::mem;
use sat::formula::{Lit, Var};
use sat::formula::assignment::*;
use sat::formula::clause::Clause;


pub struct ElimClauses {
    extend_model: bool,
    literals: Vec<Lit>,
    sizes: Vec<usize>,
}

impl ElimClauses {
    pub fn new(extend_model: bool) -> ElimClauses {
        ElimClauses {
            extend_model: extend_model,
            literals: Vec::new(),
            sizes: Vec::new(),
        }
    }

    pub fn mk_elim_unit(&mut self, x: Lit) {
        self.literals.push(x);
        self.sizes.push(1);
    }

    pub fn mk_elim_clause(&mut self, v: Var, c: &Clause) {
        let first = self.literals.len();

        // Copy clause to elimclauses-vector. Remember position where the
        // variable 'v' occurs:
        let mut v_pos = first;
        let mut v_found = false;
        for &lit in c.lits() {
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

    pub fn extend(&self, assigns: &mut Assignment) {
        if !self.extend_model {
            return;
        }

        let mut i = self.literals.len();
        let mut cl = self.sizes.len();
        while cl > 0 && i > 0 {
            cl -= 1;
            let mut j = self.sizes[cl];
            assert!(j > 0);

            i -= 1;
            let mut skip = false;
            while j > 1 {
                if assigns.is_assigned_pos(self.literals[i]) {
                    skip = true;
                    break;
                }

                j -= 1;
                i -= 1;
            }

            if !skip {
                assigns.rewrite_lit(self.literals[i]);
            }

            if i > j - 1 {
                i -= j - 1;
            } else {
                i = 0
            }
        }
    }

    pub fn log_size(&self) {
        let sz = self.literals.len() + self.sizes.len();
        if sz > 0 {
            info!(
                "|  Eliminated clauses:     {:10.2} Mb                                      |",
                ((sz * mem::size_of::<u32>()) as f64) / (1024.0 * 1024.0)
            );
        }
    }
}
