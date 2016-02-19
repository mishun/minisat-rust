use sat::formula::{Var, Lit, VarMap};

pub mod dimacs;
pub mod formula;
pub mod minisat;


pub enum PartialResult {
    UnSAT,
    SAT(VarMap<bool>),
    Interrupted(f64)
}


pub enum TotalResult {
    UnSAT,
    SAT(VarMap<bool>),
    Interrupted
}


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


pub trait Solver {
    fn nVars(&self) -> usize;
    fn nClauses(&self) -> usize;
    fn newVar(&mut self, upol : Option<bool>, dvar : bool) -> Var;
    fn addClause(&mut self, clause : &[Lit]) -> bool;
    fn preprocess(&mut self) -> bool;
    fn solve(&mut self) -> TotalResult;
    fn stats(&self) -> Stats;
}
