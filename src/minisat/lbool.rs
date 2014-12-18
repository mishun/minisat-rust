use std::fmt;

#[deriving(Copy, Clone)]
pub struct LBool(u8);

impl LBool {
    pub fn True() -> LBool { LBool(0) }
    pub fn False() -> LBool { LBool(1) }
    pub fn Undef() -> LBool { LBool(2) }

    #[inline]
    pub fn isTrue(&self) -> bool {
        let LBool(ref b) = *self;
        *b == 0
    }

    #[inline]
    pub fn isFalse(&self) -> bool {
        let LBool(ref b) = *self;
        *b == 1
    }

    #[inline]
    pub fn isUndef(&self) -> bool {
        let LBool(ref b) = *self;
        *b > 1
    }

    #[inline]
    pub fn new(b : bool) -> LBool {
        LBool(!b as u8)
    }
}

impl BitXor<bool, LBool> for LBool {
    #[inline]
    fn bitxor(self, b : bool) -> LBool {
        let LBool(a) = self;
        LBool(a ^ b as u8)
    }
}

impl fmt::Show for LBool {
    fn fmt(&self, f : &mut fmt::Formatter) -> fmt::Result {
        match () {
            _ if self.isTrue()  => { write!(f, "true") }
            _ if self.isFalse() => { write!(f, "false") }
            _                   => { write!(f, "?") }
        }
    }
}
