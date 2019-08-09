use std::{fmt, mem, ptr, slice};
use super::{allocator, Lit};
pub use super::clause_header::*;


const FLAG_BITS : usize = 4;
const FLAG_DELETED : u32 = 0x01;
const FLAG_TOUCHED : u32 = 0x02;
const FLAG_RELOCED : u32 = 0x08;

pub const MIN_CLAUSE_SIZE : usize = 2;
pub const MAX_CLAUSE_SIZE : usize = 0xFFFFFFFF >> FLAG_BITS;


pub struct Clause {
    mark: u32,
    pub header: ClauseHeader,
    pub prefix: [Lit; MIN_CLAUSE_SIZE]
}

impl Clause {
    #[inline]
    pub fn len(&self) -> usize {
        (self.mark >> FLAG_BITS) as usize
    }

    #[inline]
    pub fn shrink_by(&mut self, shrink: usize) {
        assert!(self.len() >= MIN_CLAUSE_SIZE + shrink);
        self.mark -= (shrink << FLAG_BITS) as u32;
    }

    #[inline]
    pub fn lits(&self) -> &[Lit] {
        unsafe { slice::from_raw_parts(self.prefix.as_ptr(), self.len()) }
    }

    #[inline]
    pub fn lits_mut(&mut self) -> &mut [Lit] {
        unsafe { slice::from_raw_parts_mut(self.prefix.as_mut_ptr(), self.len()) }
    }

    #[inline]
    pub unsafe fn ptr_range(&mut self) -> (*mut Lit, *mut Lit) {
        let begin = self.prefix.as_mut_ptr();
        let end = begin.add(self.len());
        (begin, end)
    }


    pub fn is_deleted(&self) -> bool {
        (self.mark & FLAG_DELETED) != 0
    }

    fn mark_deleted(&mut self) {
        self.mark |= FLAG_DELETED;
    }

    pub fn is_touched(&self) -> bool {
        (self.mark & FLAG_TOUCHED) != 0
    }

    pub fn set_touched(&mut self, b: bool) {
        if b {
            self.mark |= FLAG_TOUCHED;
        } else {
            self.mark &= !FLAG_TOUCHED;
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
    pub extra_clause_field: bool
}

impl ClauseAllocator {
    pub fn with_capacity(capacity: usize) -> ClauseAllocator {
        ClauseAllocator {
            ra: allocator::RegionAllocator::with_capacity(capacity),
            lc: LegacyCounter::new(),
            extra_clause_field: false,
        }
    }

    pub fn gc(&mut self) -> ClauseGC {
        let dst = ClauseAllocator {
            ra: allocator::RegionAllocator::with_capacity(self.lc.size - self.lc.wasted),
            lc: LegacyCounter::new(),
            extra_clause_field: self.extra_clause_field,
        };
        ClauseGC { src: self, dst }
    }

    pub fn alloc(&mut self, literals: &[Lit], header: ClauseHeader) -> (&Clause, ClauseRef) {
        let len = literals.len();
        assert!(len >= MIN_CLAUSE_SIZE);
        assert!(len <= MAX_CLAUSE_SIZE);
        unsafe {
            let (clause, cref) = self.ra.allocate_with_extra::<Lit>(len - MIN_CLAUSE_SIZE);

            clause.mark = (len << FLAG_BITS) as u32;
            ptr::write(&mut clause.header, header);
            ptr::copy_nonoverlapping(literals.as_ptr(), clause.prefix.as_mut_ptr(), len);

            self.lc.add(clause);
            (clause, ClauseRef(cref))
        }
    }

    fn reloc(&mut self, src: &Clause) -> ClauseRef {
        let len = src.len();
        assert!(len >= MIN_CLAUSE_SIZE);
        unsafe {
            let (clause, cref) = self.ra.allocate_with_extra::<Lit>(len - MIN_CLAUSE_SIZE);

            clause.mark = src.mark;
            ptr::write(&mut clause.header, ptr::read(&src.header));
            ptr::copy_nonoverlapping(src.prefix.as_ptr(), clause.prefix.as_mut_ptr(), len);

            if !self.extra_clause_field {
                if let ClauseHeader::Clause { ref mut abstraction} = clause.header {
                    *abstraction = None;
                }
            }

            self.lc.add(clause);
            ClauseRef(cref)
        }
    }

    pub fn free(&mut self, cref: ClauseRef) {
        let clause = self.ra.get_mut(cref.0);
        assert!(!clause.is_deleted());
        clause.mark_deleted();
        self.lc.sub(clause);
    }

    #[inline]
    pub fn is_deleted(&self, cref: ClauseRef) -> bool {
        let c = self.ra.get(cref.0);
        c.is_deleted()
    }


    pub fn check_garbage(&mut self, gf: f64) -> bool {
        (self.lc.wasted as f64) > (self.lc.size as f64) * gf
    }


    #[inline]
    pub fn view(&self, cref: ClauseRef) -> &Clause {
        self.ra.get(cref.0)
    }

    #[inline]
    pub fn edit(&mut self, cref: ClauseRef) -> &mut Clause {
        self.ra.get_mut(cref.0)
    }

    #[inline]
    pub fn literals(&self, cref: ClauseRef) -> &[Lit] {
        self.view(cref).lits()
    }
}


pub struct ClauseGC<'a> {
    src: &'a mut ClauseAllocator,
    dst: ClauseAllocator
}

impl Drop for ClauseGC<'_> {
    fn drop(&mut self) {
        debug!("|  Garbage collection:   {:12} bytes => {:12} bytes ({} -> {})            |",
            self.src.lc.size,
            self.dst.lc.size,
            self.src.ra.allocated_bytes(),
            self.dst.ra.allocated_bytes()
        );
        mem::swap(self.src, &mut self.dst);
    }
}

impl<'a> ClauseGC<'a> {
    pub fn relocate(&mut self, cref: ClauseRef) -> Option<ClauseRef> {
        let c = self.src.edit(cref);
        if c.is_deleted() {
            None
        } else if (c.mark & FLAG_RELOCED) == 0 {
            let reloced = self.dst.reloc(c);
            unsafe { ptr::write(c.prefix.as_mut_ptr() as *mut ClauseRef, reloced); }
            c.mark |= FLAG_RELOCED;
            Some(reloced)
        } else {
            Some(unsafe { ptr::read(c.prefix.as_ptr() as *const ClauseRef) })
        }
    }
}


struct LegacyCounter {
    size: usize,
    wasted: usize,
}

impl LegacyCounter {
    fn clause_size(clause: &Clause) -> usize {
        if let ClauseHeader::Clause { abstraction: None } = clause.header {
            4 * (1 + clause.len())
        } else {
            4 * (2 + clause.len())
        }
    }

    pub fn new() -> LegacyCounter {
        LegacyCounter { size: 0, wasted: 0 }
    }

    pub fn add(&mut self, clause: &Clause) {
        self.size += Self::clause_size(clause);
    }

    pub fn sub(&mut self, clause: &Clause) {
        self.wasted += Self::clause_size(clause);
    }
}
