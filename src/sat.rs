use crate::sat::formula::{Lit, Var};

pub mod dimacs;
pub mod formula;
pub mod minisat;


#[derive(Default, Debug)]
pub struct Stats {
    pub solves: u64,
    pub restarts: u64,
    pub decisions: u64,
    pub rnd_decisions: u64,
    pub conflicts: u64,
    pub propagations: u64,
    pub tot_literals: u64,
    pub del_literals: u64,
}


pub enum SolveRes<Solver> {
    UnSAT(Stats),
    SAT(Vec<Lit>, Stats),
    Interrupted(f64, Solver),
}


pub trait Solver: Sized {
    fn n_vars(&self) -> usize;
    fn n_clauses(&self) -> usize;
    fn new_var(&mut self, upol: Option<bool>, dvar: bool) -> Var;
    fn add_clause(&mut self, clause: &[Lit]) -> bool;
    fn preprocess(&mut self, _: &minisat::budget::Budget) -> bool;
    fn solve_limited(self, _: &minisat::budget::Budget, _: &[Lit]) -> SolveRes<Self>;
    fn stats(&self) -> Stats;
}
