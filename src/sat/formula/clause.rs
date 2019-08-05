use std::{fmt, ptr, slice};
use super::{allocator, Lit};


pub const MIN_CLAUSE_SIZE : usize = 2;


#[derive(Clone, Copy)]
pub struct ClauseHeader {
    pub learnt: bool,
    pub has_extra: bool,
    pub activity: f32,
    pub abstraction: u32
}

pub struct Clause {
    mark: u32,
    pub header: ClauseHeader,
    reloced: Option<ClauseRef>,
    len: u32,
    pub head: [Lit; MIN_CLAUSE_SIZE]
}

impl Clause {
    #[inline]
    pub fn len(&self) -> usize {
        self.len as usize
    }

    #[inline]
    pub fn shrink_by(&mut self, shrink: usize) {
        self.len -= shrink as u32;
    }

    #[inline]
    pub fn lits(&self) -> &[Lit] {
        unsafe { slice::from_raw_parts(self.head.as_ptr(), self.len as usize) }
    }

    #[inline]
    pub fn lits_mut(&mut self) -> &mut [Lit] {
        unsafe { slice::from_raw_parts_mut(self.head.as_mut_ptr(), self.len as usize) }
    }

    #[inline]
    pub unsafe fn ptr_range(&mut self) -> (*mut Lit, *mut Lit) {
        let begin = self.head.as_mut_ptr();
        let end = begin.add(self.len as usize);
        (begin, end)
    }


    pub fn is_deleted(&self) -> bool {
        (self.mark & 1) != 0
    }

    fn mark_deleted(&mut self) {
        self.mark |= 1;
    }

    pub fn is_touched(&self) -> bool {
        (self.mark & 2) != 0
    }

    pub fn set_touched(&mut self, b: bool) {
        if b {
            self.mark |= 2;
        } else {
            self.mark &= !2;
        }
    }
}

impl fmt::Debug for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_deleted() {
            write!(f, "<deleted>")?;
        }
        write!(f, "(")?;
        let mut first = true;
        for lit in self.lits() {
            if !first {
                write!(f, " ∨ ")?;
            }
            first = false;
            write!(f, "{:?}", lit)?;
        }
        write!(f, ")")
    }
}


#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct ClauseRef(allocator::Ref);


pub struct ClauseAllocator {
    ra: allocator::RegionAllocator<Clause>,
    lc: LegacyCounter,
    pub extra_clause_field: bool,
}

impl ClauseAllocator {
    pub fn new_empty() -> ClauseAllocator {
        ClauseAllocator {
            ra: allocator::RegionAllocator::new(),
            lc: LegacyCounter::new(),
            extra_clause_field: false,
        }
    }

    pub fn new_for_gc(old: &ClauseAllocator) -> ClauseAllocator {
        ClauseAllocator {
            ra: allocator::RegionAllocator::with_capacity(old.lc.size - old.lc.wasted),
            lc: LegacyCounter::new(),
            extra_clause_field: old.extra_clause_field,
        }
    }

    pub fn alloc(&mut self, literals: &[Lit], header: ClauseHeader) -> (&Clause, ClauseRef) {
        let len = literals.len();
        assert!(len >= MIN_CLAUSE_SIZE);
        unsafe {
            let (clause, cref) = self.ra.allocate_with_extra::<Lit>(len - MIN_CLAUSE_SIZE);

            clause.mark = 0;
            clause.header = header;
            clause.reloced = None;
            clause.len = len as u32;
            ptr::copy_nonoverlapping(literals.as_ptr(), clause.head.as_mut_ptr(), len);

            self.lc.add(clause);
            (clause, ClauseRef(cref))
        }
    }

    fn reloc(&mut self, src: &Clause) -> ClauseRef {
        let len = src.len as usize;
        assert!(len >= MIN_CLAUSE_SIZE);
        unsafe {
            let (clause, cref) = self.ra.allocate_with_extra::<Lit>(len - MIN_CLAUSE_SIZE);

            clause.mark = src.mark;
            clause.header = src.header;
            clause.reloced = None;
            clause.len = src.len;
            ptr::copy_nonoverlapping(src.head.as_ptr(), clause.head.as_mut_ptr(), len);

            self.lc.add(clause);
            ClauseRef(cref)
        }
    }

    pub fn reloc_to(&mut self, to: &mut ClauseAllocator, src: ClauseRef) -> Option<ClauseRef> {
        let c = self.edit(src);
        if c.is_deleted() {
            None
        } else {
            if let None = c.reloced {
                c.reloced = Some(to.reloc(c));
            }
            c.reloced
        }
    }

    pub fn free(&mut self, ClauseRef(cr): ClauseRef) {
        let clause = self.ra.get_mut(cr);
        assert!(!clause.is_deleted());
        clause.mark_deleted();
        self.lc.sub(clause);
    }

    #[inline]
    pub fn is_deleted(&self, ClauseRef(cr): ClauseRef) -> bool {
        let c = self.ra.get(cr);
        c.is_deleted()
    }


    pub fn size(&self) -> usize {
        self.lc.size
    }

    pub fn check_garbage(&mut self, gf: f64) -> bool {
        (self.lc.wasted as f64) > (self.lc.size as f64) * gf
    }

    pub fn set_extra_clause_field(&mut self, new_value: bool) {
        self.extra_clause_field = new_value;
    }


    #[inline]
    pub fn view(&self, ClauseRef(cr): ClauseRef) -> &Clause {
        self.ra.get(cr)
    }

    #[inline]
    pub fn edit(&mut self, ClauseRef(cr): ClauseRef) -> &mut Clause {
        self.ra.get_mut(cr)
    }

    #[inline]
    pub fn literals(&self, cref: ClauseRef) -> &[Lit] {
        self.view(cref).lits()
    }
}


struct LegacyCounter {
    size: usize,
    wasted: usize,
}

impl LegacyCounter {
    fn clause_size(size: usize, has_extra: bool) -> usize {
        4 * (1 + size + (has_extra as usize))
    }

    pub fn new() -> LegacyCounter {
        LegacyCounter { size: 0, wasted: 0 }
    }

    pub fn add(&mut self, clause: &Clause) {
        self.size += Self::clause_size(clause.len as usize, clause.header.has_extra);
    }

    pub fn sub(&mut self, clause: &Clause) {
        self.wasted += Self::clause_size(clause.len as usize, clause.header.has_extra);
    }
}
