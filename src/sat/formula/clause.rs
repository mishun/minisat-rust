use std::fmt;
use std::ops;
use super::Lit;


#[derive(Clone, Copy)]
struct ClauseHeader {
    size      : usize,
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
    data   : Box<[Lit]>
}

impl Clause {
    #[inline]
    pub fn len(&self) -> usize {
        self.header.size
    }

    #[inline]
    pub fn mark(&self) -> u32 {
        self.header.mark
    }

    #[inline]
    fn is_deleted(&self) -> bool {
        self.header.mark == 1
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
    pub fn setMark(&mut self, m : u32) {
        self.header.mark = m
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
        assert!(self.header.size > 1);
        (self.data[0], self.data[1])
    }

    #[inline]
    pub fn pullLiteral<F : FnMut(Lit) -> bool>(&mut self, place : usize, mut f : F) -> Option<Lit> {
        for k in (place + 1) .. self.header.size {
            let lit = self.data[k];
            if f(lit) {
                self.data.swap(place, k);
                return Some(lit);
            }
        }
        None
    }

    #[inline]
    pub fn iter(&self) -> ClauseIter {
        ClauseIter { clause : self, index : 0 }
    }

    #[inline]
    pub fn iterFrom(&self, start : usize) -> ClauseIter {
        ClauseIter { clause : self, index : start }
    }

    #[inline]
    pub fn retainSuffix<F : Fn(&Lit) -> bool>(&mut self, base : usize, f : F) {
        let mut i = base;
        while i < self.header.size {
            if f(&self.data[i]) {
                i += 1
            } else {
                self.header.size -= 1;
                self.data[i] = self.data[self.header.size];
            }
        }
    }

    pub fn strengthen(&mut self, p : Lit) {
        for i in 0 .. self.header.size {
            if self.data[i] == p {
                for j in i + 1 .. self.header.size {
                    self.data[j - 1] = self.data[j];
                }
                self.header.size -= 1;
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
        assert!(index < self.header.size);
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
            if first { first = false; } else { try!(write!(f, " ∨ ")); }
            try!(write!(f, "{:?}", lit));
        }
        write!(f, ")")
    }
}


pub struct ClauseIter<'c> {
    clause : &'c Clause,
    index  : usize
}

impl<'c> Iterator for ClauseIter<'c> {
    type Item = Lit;

    #[inline]
    fn next(&mut self) -> Option<Lit> {
        if self.index < self.clause.header.size {
            let lit = self.clause.data[self.index];
            self.index += 1;
            Some(lit)
        } else {
            None
        }
    }
}


#[derive(PartialEq, Eq, Copy, Clone)]
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
            header : ClauseHeader { size      : len
                                  , mark      : 0
                                  , learnt    : learnt
                                  , reloced   : false
                                  , has_extra : use_extra
                                  , data_act  : 0.0
                                  , data_abs  : 0
                                  , data_rel  : None
                                  },
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
        let len = src.header.size;

        let mut c = Clause {
            header : src.header,
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
        c.header.mark = 1;
        self.wasted += ClauseAllocator::clauseSize(c.header.size, c.header.has_extra);
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
