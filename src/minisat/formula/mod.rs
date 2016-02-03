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
        let Var(ref v) = *self;
        write!(f, "x{}", v)
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
        let Lit(l) = *self;
        (l & 1) != 0
    }

    #[inline]
    pub fn var(&self) -> Var {
        let Lit(l) = *self;
        Var(l >> 1)
    }
}

impl ops::Not for Lit {
    type Output = Lit;

    #[inline]
    fn not(self) -> Lit {
        let Lit(l) = self;
        Lit(l ^ 1)
    }
}

impl ops::BitXor<bool> for Lit {
    type Output = Lit;

    #[inline]
    fn bitxor(self, b : bool) -> Lit {
        let Lit(l) = self;
        Lit(l ^ (b as usize))
    }
}

impl fmt::Debug for Lit {
    fn fmt(&self, f : &mut fmt::Formatter) -> fmt::Result {
        if self.sign() { try!(write!(f, "¬")); }
        write!(f, "{:?}", self.var())
    }
}


// TODO: remove
pub const TempLit : Lit = Lit(0);
