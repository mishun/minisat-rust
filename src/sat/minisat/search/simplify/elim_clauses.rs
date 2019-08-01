use std::mem;
use crate::sat::formula::{util, Lit, Var, VarMap};


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
        self.sizes.push(self.literals.len());
    }

    pub fn mk_elim_clause(&mut self, v: Var, clause: &[Lit]) {
        assert!(clause.len() > 1);
        match clause.iter().enumerate().find(|(_, lit)| lit.var() == v) {
            None => panic!("{:#?} is't present in {:#?}", v, clause),
            Some((index, _)) => {
                // Copy clause to elimclauses-vector. Remember position where the
                // variable 'v' occurs:
                let first = self.literals.len();
                self.literals.extend_from_slice(clause);
                self.sizes.push(self.literals.len());

                // Swap the first literal with the 'v' literal, so that the literal
                // containing 'v' will occur first in the clause:
                self.literals.swap(first, first + index);
            }
        }
    }

    pub fn extend_model(&self, model: &mut VarMap<bool>) {
        if !self.extend_model {
            return;
        }

        let mut i = self.sizes.len();
        while i > 0 {
            i -= 1;
            let clause = {
                let head = if i > 0 { self.sizes[i - 1] } else { 0 };
                let tail = self.sizes[i];
                &self.literals[head..tail]
            };

            assert!(clause.len() > 0);
            if !util::satisfied_with_model(clause, model) {
                let lit = clause[0];
                model.insert(&lit.var(), !lit.sign());
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
