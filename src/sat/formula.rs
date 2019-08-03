use std::{fmt, mem, ops};
pub use self::index_map::*;

mod allocator;
pub mod assignment;
pub mod clause;
mod index_map;
pub mod subsumes;
pub mod util;


#[derive(PartialEq, Eq, Clone, Copy, Debug)]
#[repr(u8)]
pub enum LBool {
    False = 0,
    True  = 1,
    Undef = 2
}

impl LBool {
    #[inline]
    fn is_undef(self) -> bool {
        (self as u8) > 1
    }
}

impl ops::Not for LBool {
    type Output = LBool;

    #[inline]
    fn not(self) -> LBool {
        unsafe {
            mem::transmute((0x21u8 >> ((self as u8) << 1)) & 3)
        }
    }
}

impl ops::BitAnd for LBool {
    type Output = LBool;

    #[inline]
    fn bitand(self, that: LBool) -> LBool {
        unsafe {
            let off = ((self as u8) << 1) | ((that as u8) << 3);
            mem::transmute(((0x282400 >> off) & 3) as u8)
        }
    }
}

impl ops::BitOr for LBool {
    type Output = LBool;

    #[inline]
    fn bitor(self, that: LBool) -> LBool {
        unsafe {
            let off = ((self as u8) << 1) | ((that as u8) << 3);
            mem::transmute(((0x261524 >> off) & 3) as u8)
        }
    }
}


#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct Lit(u32);

impl Lit {
    #[inline]
    pub fn sign(self) -> bool {
        (self.0 & 1) != 0
    }

    #[inline]
    pub fn var(self) -> Var {
        Var(self.0 >> 1)
    }

    #[inline]
    pub fn is_pos_at(self, val: LBool) -> bool {
        ((self.0 as u8) & 1) == ((val as u8) ^ 1)
    }

    #[inline]
    pub fn is_neg_at(self, val: LBool) -> bool {
        ((self.0 as u8) & 1) == (val as u8)
    }

    #[inline]
    pub fn apply_sign(self, val: LBool) -> LBool {
        unsafe {
            let off = (((self.0 & 1) as u8) << 3) | ((val as u8) << 1);
            mem::transmute(((0x2124 >> off) & 3) as u8)
        }
    }

    #[inline]
    pub fn pos_assignment(self) -> LBool {
        unsafe { mem::transmute((!self.0 & 1) as u8) }
    }

    #[inline]
    pub fn neg_assignment(self) -> LBool {
        unsafe { mem::transmute((self.0 & 1) as u8) }
    }


    #[inline]
    fn abstraction(self) -> u32 {
        1 << ((self.0 >> 1) & 31)
    }


    #[inline]
    fn var_index(self) -> usize {
        (self.0 >> 1) as usize
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


#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct Var(u32);

impl Var {
    #[inline]
    pub fn sign_lit(self, sign: bool) -> Lit {
        Lit((self.0 << 1) | (sign as u32))
    }

    #[inline]
    pub fn pos_lit(self) -> Lit {
        Lit(self.0 << 1)
    }

    #[inline]
    pub fn neg_lit(self) -> Lit {
        Lit((self.0 << 1) | 1)
    }


    #[inline]
    fn index(self) -> usize {
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


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lits() {
        let v = Var::from_index(31337);


        let pv = v.pos_lit();
        assert_eq!(v, pv.var());
        assert_eq!(pv, v.sign_lit(false));
        assert_eq!(pv.pos_assignment(), LBool::True);
        assert_eq!(pv.neg_assignment(), LBool::False);

        assert_eq!(pv.apply_sign(LBool::False), LBool::False);
        assert_eq!(pv.apply_sign(LBool::True), LBool::True);
        assert_eq!(pv.apply_sign(LBool::Undef), LBool::Undef);

        assert!(!pv.is_pos_at(LBool::False));
        assert!(pv.is_pos_at(LBool::True));
        assert!(!pv.is_pos_at(LBool::Undef));
        assert!(pv.is_neg_at(LBool::False));
        assert!(!pv.is_neg_at(LBool::True));
        assert!(!pv.is_neg_at(LBool::Undef));


        let nv = v.neg_lit();
        assert_eq!(v, nv.var());
        assert_eq!(nv, v.sign_lit(true));
        assert_eq!(nv.pos_assignment(), LBool::False);
        assert_eq!(nv.neg_assignment(), LBool::True);

        assert_eq!(nv.apply_sign(LBool::False), LBool::True);
        assert_eq!(nv.apply_sign(LBool::True), LBool::False);
        assert_eq!(nv.apply_sign(LBool::Undef), LBool::Undef);

        assert!(nv.is_pos_at(LBool::False));
        assert!(!nv.is_pos_at(LBool::True));
        assert!(!nv.is_pos_at(LBool::Undef));
        assert!(!nv.is_neg_at(LBool::False));
        assert!(nv.is_neg_at(LBool::True));
        assert!(!nv.is_neg_at(LBool::Undef));

        assert_ne!(pv, nv);
    }

    #[test]
    fn test_not() {
        assert_eq!(!LBool::True, LBool::False);
        assert_eq!(!LBool::False, LBool::True);
        assert_eq!(!LBool::Undef, LBool::Undef);
    }

    #[test]
    fn test_and() {
        assert_eq!(LBool::True & LBool::True, LBool::True);
        assert_eq!(LBool::True & LBool::False, LBool::False);
        assert_eq!(LBool::True & LBool::Undef, LBool::Undef);

        assert_eq!(LBool::False & LBool::True, LBool::False);
        assert_eq!(LBool::False & LBool::False, LBool::False);
        assert_eq!(LBool::False & LBool::Undef, LBool::False);

        assert_eq!(LBool::Undef & LBool::True, LBool::Undef);
        assert_eq!(LBool::Undef & LBool::False, LBool::False);
        assert_eq!(LBool::Undef & LBool::Undef, LBool::Undef);
    }

    #[test]
    fn test_or() {
        assert_eq!(LBool::True | LBool::True, LBool::True);
        assert_eq!(LBool::True | LBool::False, LBool::True);
        assert_eq!(LBool::True | LBool::Undef, LBool::True);

        assert_eq!(LBool::False | LBool::True, LBool::True);
        assert_eq!(LBool::False | LBool::False, LBool::False);
        assert_eq!(LBool::False | LBool::Undef, LBool::Undef);

        assert_eq!(LBool::Undef | LBool::True, LBool::True);
        assert_eq!(LBool::Undef | LBool::False, LBool::Undef);
        assert_eq!(LBool::Undef | LBool::Undef, LBool::Undef);
    }
}
