use std::fmt;
use super::index_map::{HasIndex};


#[deriving(PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
pub struct Var(uint);

impl Var {
    #[inline]
    pub fn new(v : uint) -> Var {
        Var(v)
    }
}

impl HasIndex for Var {
    #[inline]
    fn toIndex(&self) -> uint {
        let Var(ref idx) = *self;
        *idx
    }
}

impl fmt::Show for Var {
    fn fmt(&self, f : &mut fmt::Formatter) -> fmt::Result {
        let Var(ref v) = *self;
        write!(f, "x{}", v)
    }
}


#[deriving(PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
pub struct Lit(uint);

impl Lit {
    #[inline]
    pub fn new(Var(v) : Var, sign : bool) -> Lit {
        Lit(v + v + sign as uint)
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

impl HasIndex for Lit {
    #[inline]
    fn toIndex(&self) -> uint {
        let Lit(ref idx) = *self;
        *idx
    }
}

impl Not<Lit> for Lit {
    #[inline]
    fn not(&self) -> Lit {
        let Lit(l) = *self;
        Lit(l ^ 1)
    }
}

impl BitXor<bool, Lit> for Lit {
    #[inline]
    fn bitxor(self, b : bool) -> Lit {
        let Lit(l) = self;
        Lit(l ^ b as uint)
    }
}

impl fmt::Show for Lit {
    fn fmt(&self, f : &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}", if self.sign() { "~" } else { "" }, self.var())
    }
}
