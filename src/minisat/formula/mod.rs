use std::fmt;
use std::ops;

pub mod assignment;
pub mod clause;
pub mod index_map;
pub mod util;


#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
pub struct Var(usize);

impl fmt::Debug for Var {
    fn fmt(&self, f : &mut fmt::Formatter) -> fmt::Result {
        write!(f, "x{}", self.0)
    }
}


#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
pub struct Lit(usize);

impl Lit {
    #[inline]
    pub fn new(Var(v) : Var, sign : bool) -> Lit {
        Lit(v + v + (sign as usize))
    }

    #[inline]
    pub fn sign(&self) -> bool {
        (self.0 & 1) != 0
    }

    #[inline]
    pub fn var(&self) -> Var {
        Var(self.0 >> 1)
    }

    #[inline]
    pub fn abstraction(&self) -> u32 {
        1 << ((self.0 >> 1) & 31)
    }
}

impl ops::Not for Lit {
    type Output = Lit;

    #[inline]
    fn not(self) -> Lit {
        Lit(self.0 ^ 1)
    }
}

impl fmt::Debug for Lit {
    fn fmt(&self, f : &mut fmt::Formatter) -> fmt::Result {
        if self.sign() { try!(write!(f, "¬")); }
        write!(f, "{:?}", self.var())
    }
}
