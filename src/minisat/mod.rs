use minisat::formula::{Var, Lit};
use minisat::formula::index_map::VarMap;

pub mod decision_heuristic;
pub mod formula;
pub mod dimacs;
mod random;
pub mod solver;
mod watches;
mod util;
pub mod conflict;
pub mod clause_db;


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


pub trait Solver {
    fn nVars(&self) -> usize;
    fn nClauses(&self) -> usize;
    fn newVar(&mut self, upol : Option<bool>, dvar : bool) -> Var;
    fn addClause(&mut self, clause : &[Lit]) -> bool;
    fn solve(&mut self) -> TotalResult;
    fn printStats(&self);
}
