use std::{fmt, ops};
pub use self::index_map::*;

mod allocator;
pub mod assignment;
pub mod clause;
mod index_map;
pub mod subsumes;
pub mod util;


#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct Var(u32);

impl Var {
    #[inline]
    pub fn sign_lit(&self, sign: bool) -> Lit {
        Lit((self.0 << 1) | (sign as u32))
    }

    #[inline]
    pub fn pos_lit(&self) -> Lit {
        Lit(self.0 << 1)
    }

    #[inline]
    pub fn neg_lit(&self) -> Lit {
        Lit((self.0 << 1) | 1)
    }


    #[inline]
    fn index(&self) -> usize {
        self.0 as usize
    }

    #[inline]
    fn from_index(index: usize) -> Var {
        if index <= 0x7FFFFFFF {
            Var(index as u32)
        } else {
            panic!("Var index {} is out of bound", index)
        }
    }
}

impl fmt::Debug for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "x{}", self.0)
    }
}


#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct Lit(u32);

impl Lit {
    #[inline]
    pub fn sign(&self) -> bool {
        (self.0 & 1) != 0
    }

    #[inline]
    pub fn var(&self) -> Var {
        Var(self.0 >> 1)
    }


    #[inline]
    fn abstraction(&self) -> u32 {
        1 << ((self.0 >> 1) & 31)
    }


    #[inline]
    fn var_index(&self) -> usize {
        (self.0 >> 1) as usize
    }

    #[inline]
    fn sign_index(&self) -> usize {
        (self.0 & 1) as usize
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
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.sign() {
            write!(f, "¬")?;
        }
        write!(f, "{:?}", self.var())
    }
}
