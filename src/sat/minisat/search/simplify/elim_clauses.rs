use std::mem;
use crate::sat::formula::{Lit, Var, VarMap};


pub struct ElimClauses {
    extend_model: bool,
    literals: Vec<Lit>,
    sizes: Vec<usize>,
}

impl ElimClauses {
    pub fn new(extend_model: bool) -> ElimClauses {
        ElimClauses {
            extend_model,
            literals: Vec::new(),
            sizes: Vec::new(),
        }
    }

    pub fn mk_elim_unit(&mut self, x: Lit) {
        self.literals.push(x);
        self.sizes.push(1);
    }

    pub fn mk_elim_clause(&mut self, v: Var, clause: &[Lit]) {
        assert!(clause.len() > 1);
        let first = self.literals.len();

        // Copy clause to elimclauses-vector. Remember position where the
        // variable 'v' occurs:
        let mut v_pos = first;
        let mut v_found = false;
        for &lit in clause {
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
        self.sizes.push(clause.len());
    }

    pub fn extend(&self, assigns: &mut VarMap<bool>) {
        if !self.extend_model {
            return;
        }

        let mut i = self.literals.len();
        let mut c_index = self.sizes.len();
        while c_index > 0 && i > 0 {
            c_index -= 1;
            let mut cur_size = self.sizes[c_index];
            assert!(cur_size > 0);

            i -= 1;
            let mut skip = false;
            while cur_size > 1 {
                let lit = self.literals[i];
                match assigns.get(&lit.var()) {
                    Some(sign) if *sign != lit.sign() => {
                        skip = true;
                        break;
                    }
                    _ => {}
                }

                cur_size -= 1;
                i -= 1;
            }

            if !skip {
                let lit = self.literals[i];
                assigns.insert(&lit.var(), !lit.sign());
            }

            if i > cur_size - 1 {
                i -= cur_size - 1;
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
