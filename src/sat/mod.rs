use sat::formula::{Var, Lit};

pub mod dimacs;
pub mod formula;
pub mod minisat;


#[derive(Default)]
pub struct Stats {
    pub solves        : u64,
    pub restarts      : u64,
    pub decisions     : u64,
    pub rnd_decisions : u64,
    pub conflicts     : u64,
    pub propagations  : u64,
    pub tot_literals  : u64,
    pub del_literals  : u64
}


pub enum SolveRes {
    UnSAT(Stats),
    SAT(Vec<Lit>, Stats),
    Interrupted(f64, Stats)
}


pub trait Solver {
    fn nVars(&self) -> usize;
    fn nClauses(&self) -> usize;
    fn newVar(&mut self, upol : Option<bool>, dvar : bool) -> Var;
    fn addClause(&mut self, clause : &[Lit]) -> bool;
    fn preprocess(&mut self) -> bool;
    fn solveLimited(self, &[Lit]) -> SolveRes;
}
