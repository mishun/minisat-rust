use std::fmt;
use std::ops;
use super::index_map::HasIndex;


#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
pub struct Var(usize);

impl Var {
    #[inline]
    pub fn new(v : usize) -> Var {
        Var(v)
    }
}

impl HasIndex for Var {
    #[inline]
    fn toIndex(&self) -> usize {
        let Var(ref idx) = *self;
        *idx
    }
}

impl fmt::Display for Var {
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

    pub fn fromIndex(x : usize) -> Lit {
        Lit(x)
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
    fn toIndex(&self) -> usize {
        let Lit(ref idx) = *self;
        *idx
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

impl fmt::Display for Lit {
    fn fmt(&self, f : &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}", if self.sign() { "¬" } else { "" }, self.var())
    }
}
