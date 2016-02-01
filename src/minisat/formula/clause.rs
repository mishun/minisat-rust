use std::fmt;
use std::ops;
use super::Lit;


#[derive(PartialEq, Eq, Copy, Clone)]
pub struct ClauseRef(usize);


struct ClauseHeader {
    mark      : u32,
    learnt    : bool,
    has_extra : bool,
    reloced   : bool,
    size      : usize
}

pub struct Clause {
    header   : ClauseHeader,
    data     : Box<[Lit]>,
    data_act : f32,
    data_abs : u32,
    data_rel : Option<ClauseRef>,
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
    pub fn is_deleted(&self) -> bool {
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
        self.data_act as f64
    }

    #[inline]
    pub fn setActivity(&mut self, act : f64) {
        assert!(self.header.has_extra);
        self.data_act = act as f32;
    }

    #[inline]
    pub fn setMark(&mut self, m : u32) {
        self.header.mark = m
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

    pub fn to_vec(&self) -> Vec<Lit> {
        let mut v = Vec::with_capacity(self.len());
        for i in 0 .. self.len() {
            v.push(self[i])
        }
        v
    }

    pub fn calcAbstraction(&mut self) {
        assert!(self.header.has_extra);
        let mut abstraction : u32 = 0;
        for i in 0 .. self.header.size {
            let Lit(p) = self.data[i];
            abstraction |= 1 << ((p >> 1) & 31);
        }
        self.data_abs = abstraction; //data[header.size].abs = abstraction;
    }

    pub fn abstraction(&self) -> u32 {
        assert!(self.header.has_extra);
        self.data_abs
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

impl ops::IndexMut<usize> for Clause {
    #[inline]
    fn index_mut<'a>(&'a mut self, index : usize) -> &'a mut Lit {
        assert!(index < self.header.size);
        self.data.index_mut(index)
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f : &mut fmt::Formatter) -> fmt::Result {
        if self.is_deleted() {
            try!(write!(f, "<deleted>"));
        }
        try!(write!(f, "("));
        for i in 0 .. self.len() {
            if i > 0 { try!(write!(f, " ∨ ")); }
            try!(write!(f, "{}", self[i]));
        }
        write!(f, ")")
    }
}


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
        let use_extra = learnt | self.extra_clause_field;
        let len = ps.len();

        let mut c = Clause {
            header   : ClauseHeader { mark      : 0
                                    , learnt    : learnt
                                    , has_extra : use_extra
                                    , reloced   : false
                                    , size      : len
                                    },
            data     : ps,
            data_act : 0.0,
            data_abs : 0,
            data_rel : None,
        };

        if c.header.has_extra {
            if c.header.learnt {
                c.data_act = 0.0;
            } else {
                c.calcAbstraction();
            };
        }

        let index = self.clauses.len();
        self.clauses.push(c);
        self.size += ClauseAllocator::clauseSize(len, use_extra);

        (&self.clauses[index], ClauseRef(index))
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
            c.data_rel.unwrap()
        } else {
            let (_, dst) = to.alloc(c.to_vec().into_boxed_slice(), c.header.learnt);
            c.header.reloced = true;
            c.data_rel = Some(dst);
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
    pub fn edit<'a>(&'a mut self, ClauseRef(index) : ClauseRef) -> &'a mut Clause {
        assert!(index < self.clauses.len());
        &mut self.clauses[index]
    }
}

impl ops::Index<ClauseRef> for ClauseAllocator {
    type Output = Clause;

    #[inline]
    fn index<'a>(&'a self, ClauseRef(index) : ClauseRef) -> &'a Clause {
        assert!(index < self.clauses.len());
        &self.clauses[index]
    }
}
