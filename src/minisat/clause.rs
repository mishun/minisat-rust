use super::literal::{Lit};
use super::index_map::{HasIndex};


pub type ClauseRef = uint;


struct ClauseHeader {
    mark : u32,
    learnt : bool,
    has_extra : bool,
    reloced : bool,
    size : uint
}

pub struct Clause {
    header : ClauseHeader,
    data : Vec<Lit>,
    data_act : f32,
    data_abs : u32,
    data_rel : Option<ClauseRef>,
}

impl Clause {
    #[inline]
    pub fn len(&self) -> uint {
        self.header.size
    }

    #[inline]
    pub fn mark(&self) -> u32 {
        self.header.mark
    }

    #[inline]
    pub fn learnt(&self) -> bool {
        self.header.learnt
    }

    #[inline]
    pub fn reloced(&self) -> bool {
        self.header.reloced
    }

    #[inline]
    pub fn activity(&self) -> f32 {
        assert!(self.header.has_extra);
        self.data_act
    }

    #[inline]
    pub fn bumpActivity(&mut self, delta : f32) {
        if self.learnt() { self.data_act += delta; }
    }

    #[inline]
    pub fn setMark(&mut self, m : u32) {
        self.header.mark = m
    }

    #[inline]
    pub fn retainSuffix(&mut self, base : uint, f : |&Lit| -> bool) {
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

    fn calcAbstraction(&mut self) {
        assert!(self.header.has_extra);
        let mut abstraction : u32 = 0;
        for i in range(0, self.header.size) {
            abstraction |= 1 << (self.data[i].var().toIndex() & 31);
        }
        self.data_abs = abstraction; //data[header.size].abs = abstraction;
    }
}

impl Index<uint, Lit> for Clause {
    #[inline]
    fn index<'a>(&'a self, index : &uint) -> &'a Lit {
        self.data.index(index)
    }
}

impl IndexMut<uint, Lit> for Clause {
    #[inline]
    fn index_mut<'a>(&'a mut self, index : &uint) -> &'a mut Lit {
        self.data.index_mut(index)
    }
}


fn clauseSize(size : uint, has_extra : bool) -> uint {
    4 * (1 + size + has_extra as uint)
}


pub struct ClauseAllocator {
    clauses : Vec<Box<Clause>>,
    size    : uint,
    wasted  : uint,
}

impl ClauseAllocator {
    pub fn new() -> ClauseAllocator {
        ClauseAllocator {
            clauses : Vec::new(),
            size    : 0,
            wasted  : 0,
        }
    }

    pub fn alloc(&mut self, ps : &Vec<Lit>, learnt : bool) -> ClauseRef {
        let use_extra = learnt;
        let mut c = box Clause {
            header : ClauseHeader { mark : 0, learnt : learnt, has_extra : use_extra, reloced : false, size : ps.len() },
            data : ps.clone(),
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
        };

        let len = self.clauses.len();
        self.clauses.push(c);
        self.size += clauseSize(ps.len(), use_extra);

        len
    }

    fn allocCopy(&mut self, that : &Clause) -> ClauseRef {
        self.alloc(&that.data, that.header.learnt)
    }

    pub fn free(&mut self, cr : ClauseRef) {
        let size = {
            let c = &self[cr];
            clauseSize(c.header.size, c.header.has_extra)
        };
        self.wasted += size;
    }

    pub fn size(&self) -> uint {
        self.size
    }

    pub fn wasted(&self) -> uint {
        self.wasted
    }

    pub fn numberOfClauses(&self) -> uint {
        self.clauses.len()
    }

    pub fn reloc(&mut self, to : &mut ClauseAllocator, cr : &mut ClauseRef) {
        let c = &mut self[*cr];
        if c.header.reloced {
            *cr = c.data_rel.unwrap();
        } else {
            *cr = to.allocCopy(c);
            c.header.reloced = true;
            c.data_rel = Some(*cr);
        }
    }
}

impl Index<ClauseRef, Clause> for ClauseAllocator {
    #[inline]
    fn index<'a>(&'a self, index : &ClauseRef) -> &'a Clause {
        assert!(*index < self.clauses.len());
        &(*self.clauses[*index])
    }
}

impl IndexMut<ClauseRef, Clause> for ClauseAllocator {
    #[inline]
    fn index_mut<'a>(&'a mut self, index : &ClauseRef) -> &'a mut Clause {
        assert!(*index < self.clauses.len());
        &mut(*self.clauses[*index])
    }
}

