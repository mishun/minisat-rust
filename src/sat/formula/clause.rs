use std::{fmt, marker, ops, ptr};
use super::Lit;


#[derive(Clone, Copy)]
struct ClauseHeader {
    mark      : u32,
    learnt    : bool,
    reloced   : bool,
    has_extra : bool,
    data_act  : f32,
    data_abs  : u32,
    data_rel  : Option<ClauseRef>
}

pub struct Clause {
    header : ClauseHeader,
    len    : usize,
    data   : Box<[Lit]>
}

impl Clause {
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub fn is_deleted(&self) -> bool {
        (self.header.mark & 1) != 0
    }

    #[inline]
    pub fn touched(&self) -> bool {
        (self.header.mark & 2) != 0
    }

    #[inline]
    pub fn is_learnt(&self) -> bool {
        self.header.learnt
    }

    #[inline]
    pub fn reloced(&self) -> bool {
        self.header.reloced
    }

    #[inline]
    pub fn activity(&self) -> f64 {
        assert!(self.header.has_extra);
        self.header.data_act as f64
    }

    #[inline]
    pub fn setActivity(&mut self, act : f64) {
        assert!(self.header.has_extra);
        self.header.data_act = act as f32;
    }

    #[inline]
    pub fn setTouched(&mut self, b : bool) {
        if b {
            self.header.mark |= 2;
        } else {
            self.header.mark &= !2;
        }
    }

    #[inline]
    pub fn swap(&mut self, i : usize, j : usize) {
        self.data.swap(i, j);
    }

    #[inline]
    pub fn head(&self) -> Lit {
        self.data[0]
    }

    #[inline]
    pub fn headPair(&self) -> (Lit, Lit) {
        assert!(self.len > 1);
        (self.data[0], self.data[1])
    }

    #[inline]
    pub fn pullLiteral<F : FnMut(Lit) -> bool>(&mut self, place : usize, mut f : F) -> Option<Lit> {
        unsafe {
            let p = self.data.as_mut_ptr();
            let src = p.offset(place as isize);
            let end = p.offset(self.len as isize);

            let mut ptr = src.offset(1);
            while ptr < end {
                if f(*ptr) {
                    ptr::swap(ptr, src);
                    return Some(*src);
                }
                ptr = ptr.offset(1);
            }

            None
        }
    }

    #[inline]
    pub fn iter<'c>(&'c self) -> ClauseIter<'c> {
        unsafe {
            let p = self.data.as_ptr();
            ClauseIter { ptr : p
                       , end : p.offset(self.len as isize)
                       , ph  : marker::PhantomData
                       }
        }
    }

    #[inline]
    pub fn iterFrom<'c>(&'c self, start : usize) -> ClauseIter<'c> {
        unsafe {
            let p = self.data.as_ptr();
            ClauseIter { ptr : p.offset(start as isize)
                       , end : p.offset(self.len as isize)
                       , ph  : marker::PhantomData
                       }
        }
    }

    #[inline]
    pub fn retainSuffix<F : Fn(&Lit) -> bool>(&mut self, base : usize, f : F) {
        let mut i = base;
        while i < self.len {
            if f(&self.data[i]) {
                i += 1
            } else {
                self.len -= 1;
                self.data[i] = self.data[self.len];
            }
        }
    }

    pub fn strengthen(&mut self, p : Lit) {
        for i in 0 .. self.len {
            if self.data[i] == p {
                for j in i + 1 .. self.len {
                    self.data[j - 1] = self.data[j];
                }
                self.len -= 1;
                self.calcAbstraction();
                return;
            }
        }
    }

    pub fn calcAbstraction(&mut self) {
        assert!(self.header.has_extra);
        let mut abstraction : u32 = 0;
        for lit in self.iter() {
            abstraction |= lit.abstraction();
        }
        self.header.data_abs = abstraction; //data[header.size].abs = abstraction;
    }

    pub fn abstraction(&self) -> u32 {
        assert!(self.header.has_extra);
        self.header.data_abs
    }
}

impl ops::Index<usize> for Clause {
    type Output = Lit;

    #[inline]
    fn index<'a>(&'a self, index : usize) -> &'a Lit {
        assert!(index < self.len);
        self.data.index(index)
    }
}

impl fmt::Debug for Clause {
    fn fmt(&self, f : &mut fmt::Formatter) -> fmt::Result {
        if self.is_deleted() {
            try!(write!(f, "<deleted>"));
        }
        try!(write!(f, "("));
        let mut first = true;
        for lit in self.iter() {
            if !first { try!(write!(f, " ∨ ")); }
            first = false;
            try!(write!(f, "{:?}", lit));
        }
        write!(f, ")")
    }
}


pub struct ClauseIter<'c> {
    ptr : *const Lit,
    end : *const Lit,
    ph  : marker::PhantomData<&'c Lit>
}

impl<'c> Iterator for ClauseIter<'c> {
    type Item = Lit;

    #[inline]
    fn next(&mut self) -> Option<Lit> {
        unsafe {
            if self.ptr >= self.end {
                None
            } else {
                let lit = *self.ptr;
                self.ptr = self.ptr.offset(1);
                Some(lit)
            }
        }
    }
}


#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct ClauseRef(usize);


pub struct ClauseAllocator {
    clauses            : Vec<Clause>,
    size               : usize,
    wasted             : usize,
    extra_clause_field : bool
}

impl ClauseAllocator {
    pub fn newEmpty() -> ClauseAllocator {
        ClauseAllocator { clauses            : Vec::new()
                        , size               : 0
                        , wasted             : 0
                        , extra_clause_field : false
                        }
    }

    pub fn newForGC(old : &ClauseAllocator) -> ClauseAllocator {
        // old.size - old.wasted
        ClauseAllocator { clauses            : Vec::new()
                        , size               : 0
                        , wasted             : 0
                        , extra_clause_field : old.extra_clause_field
                        }
    }

    fn clauseSize(size : usize, has_extra : bool) -> usize {
        4 * (1 + size + (has_extra as usize))
    }

    pub fn alloc(&mut self, ps : Box<[Lit]>, learnt : bool) -> (&Clause, ClauseRef) {
        assert!(ps.len() > 1);

        let use_extra = learnt | self.extra_clause_field;
        let len = ps.len();

        let mut c = Clause {
            header : ClauseHeader { mark      : 0
                                  , learnt    : learnt
                                  , reloced   : false
                                  , has_extra : use_extra
                                  , data_act  : 0.0
                                  , data_abs  : 0
                                  , data_rel  : None
                                  },
            len    : len,
            data   : ps
        };

        if c.header.has_extra {
            if c.header.learnt {
                c.header.data_act = 0.0;
            } else {
                c.calcAbstraction();
            };
        }

        let index = self.clauses.len();
        self.clauses.push(c);
        self.size += ClauseAllocator::clauseSize(len, use_extra);

        (&self.clauses[index], ClauseRef(index))
    }

    fn reloc(&mut self, src : &Clause) -> ClauseRef {
        let use_extra = src.header.learnt | self.extra_clause_field;
        let len = src.len;

        let mut c = Clause {
            header : src.header,
            len    : src.len,
            data   : src.data.clone()
        };
        c.header.has_extra = use_extra;

        let index = self.clauses.len();
        self.clauses.push(c);
        self.size += ClauseAllocator::clauseSize(len, use_extra);

        ClauseRef(index)
    }

    pub fn free(&mut self, ClauseRef(cr) : ClauseRef) {
        let ref mut c = self.clauses[cr];
        assert!(!c.is_deleted());
        c.header.mark |= 1;
        self.wasted += ClauseAllocator::clauseSize(c.len, c.header.has_extra);
    }

    pub fn relocTo(&mut self, to : &mut ClauseAllocator, src : ClauseRef) -> ClauseRef {
        let c = self.edit(src);
        assert!(!c.is_deleted());
        if c.header.reloced {
            c.header.data_rel.unwrap()
        } else {
            let dst = to.reloc(c);
            c.header.reloced = true;
            c.header.data_rel = Some(dst);
            dst
        }
    }

    pub fn size(&self) -> usize {
        self.size
    }

    pub fn set_extra_clause_field(&mut self, new_value : bool) {
        self.extra_clause_field = new_value;
    }

    pub fn checkGarbage(&mut self, gf : f64) -> bool {
        (self.wasted as f64) > (self.size as f64) * gf
    }

    #[inline]
    pub fn isDeleted(&self, ClauseRef(index) : ClauseRef) -> bool {
        self.clauses[index].is_deleted()
    }

    #[inline]
    pub fn view<'a>(&'a self, ClauseRef(index) : ClauseRef) -> &'a Clause {
        assert!(index < self.clauses.len());
        &self.clauses[index]
    }

    #[inline]
    pub fn edit<'a>(&'a mut self, ClauseRef(index) : ClauseRef) -> &'a mut Clause {
        assert!(index < self.clauses.len());
        &mut self.clauses[index]
    }
}
