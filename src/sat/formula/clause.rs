use std::{fmt, ptr, slice};
use super::Lit;
use super::allocator;


pub const MIN_CLAUSE_SIZE : usize = 2;


#[derive(Clone, Copy)]
struct ClauseHeader {
    mark: u32,
    learnt: bool,
    has_extra: bool,
    data_act: f32,
    data_abs: u32,
    reloced: Option<ClauseRef>,
}

pub struct Clause {
    header: ClauseHeader,
    len: u32,
    hp: [Lit; MIN_CLAUSE_SIZE]
}

impl Clause {
    #[inline]
    pub fn len(&self) -> usize {
        self.len as usize
    }

    #[inline]
    pub fn is_deleted(&self) -> bool {
        (self.header.mark & 1) != 0
    }

    #[inline]
    pub fn is_learnt(&self) -> bool {
        self.header.learnt
    }


    #[inline]
    pub fn activity(&self) -> f64 {
        assert!(self.header.has_extra);
        self.header.data_act as f64
    }

    #[inline]
    pub fn set_activity(&mut self, act: f64) {
        assert!(self.header.has_extra);
        self.header.data_act = act as f32;
    }


    #[inline]
    pub fn touched(&self) -> bool {
        (self.header.mark & 2) != 0
    }

    #[inline]
    pub fn set_touched(&mut self, b: bool) {
        if b {
            self.header.mark |= 2;
        } else {
            self.header.mark &= !2;
        }
    }


    #[inline]
    pub fn head(&self) -> Lit {
        self.hp[0]
    }

    #[inline]
    pub fn head_pair(&self) -> (Lit, Lit) {
        (self.hp[0], self.hp[1])
    }

    #[inline]
    pub fn lits(&self) -> &[Lit] {
        unsafe { slice::from_raw_parts(self.hp.as_ptr(), self.len as usize) }
    }

    #[inline]
    pub fn lits_from(&self, start: usize) -> &[Lit] {
        &self.lits()[start..]
    }

    #[inline]
    fn lits_mut(&mut self) -> &mut [Lit] {
        unsafe { slice::from_raw_parts_mut(self.hp.as_mut_ptr(), self.len as usize) }
    }


    #[inline]
    pub fn swap(&mut self, i: usize, j: usize) {
        let data = self.lits_mut();
        data.swap(i, j);
    }

    #[inline]
    pub fn retain_suffix<F: Fn(&Lit) -> bool>(&mut self, base: usize, f: F) {
        let data = unsafe { slice::from_raw_parts_mut(self.hp.as_mut_ptr(), self.len as usize) };

        let mut i = base;
        while i < self.len as usize {
            if f(&data[i]) {
                i += 1
            } else {
                self.len -= 1;
                data[i] = data[self.len as usize];
            }
        }
    }

    #[inline]
    pub fn pull_literal<F: FnMut(Lit) -> bool>(&mut self, place: usize, mut f: F) -> Option<Lit> {
        unsafe {
            let p = self.hp.as_mut_ptr();
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


    pub fn strengthen(&mut self, p: Lit) {
        let data = unsafe { slice::from_raw_parts_mut(self.hp.as_mut_ptr(), self.len as usize) };

        for i in 0..self.len as usize {
            if data[i] == p {
                for j in i + 1..self.len as usize {
                    data[j - 1] = data[j];
                }
                self.len -= 1;
                self.calc_abstraction();
                return;
            }
        }
    }

    pub fn abstraction(&self) -> u32 {
        assert!(self.header.has_extra);
        self.header.data_abs
    }

    fn calc_abstraction(&mut self) {
        assert!(self.header.has_extra);
        let mut abstraction: u32 = 0;
        for lit in self.lits() {
            abstraction |= lit.abstraction();
        }
        self.header.data_abs = abstraction; //data[header.size].abs = abstraction;
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
    extra_clause_field: bool,
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

    pub fn alloc(&mut self, literals: &[Lit], learnt: bool) -> (&Clause, ClauseRef) {
        let len = literals.len();
        assert!(len >= MIN_CLAUSE_SIZE);
        unsafe {
            let (clause, cref) = self.ra.allocate_with_extra::<Lit>(len - MIN_CLAUSE_SIZE);

            clause.header = ClauseHeader {
                mark: 0,
                learnt,
                has_extra: learnt | self.extra_clause_field,
                data_act: 0.0,
                data_abs: 0,
                reloced: None,
            };
            clause.len = len as u32;
            ptr::copy_nonoverlapping(literals.as_ptr(), clause.hp.as_mut_ptr(), len);

            if clause.header.has_extra {
                if clause.header.learnt {
                    clause.header.data_act = 0.0;
                } else {
                    clause.calc_abstraction();
                };
            }

            self.lc.add(clause);
            (clause, ClauseRef(cref))
        }
    }

    fn reloc(&mut self, src: &Clause) -> ClauseRef {
        let len = src.len as usize;
        assert!(len >= MIN_CLAUSE_SIZE);
        unsafe {
            let (clause, cref) = self.ra.allocate_with_extra::<Lit>(len - MIN_CLAUSE_SIZE);

            clause.header = src.header;
            clause.header.has_extra |= self.extra_clause_field;
            clause.len = src.len;
            ptr::copy_nonoverlapping(src.hp.as_ptr(), clause.hp.as_mut_ptr(), len);

            self.lc.add(clause);
            ClauseRef(cref)
        }
    }

    pub fn reloc_to(&mut self, to: &mut ClauseAllocator, src: ClauseRef) -> Option<ClauseRef> {
        let c = self.edit(src);
        if c.is_deleted() {
            None
        } else {
            if let None = c.header.reloced {
                c.header.reloced = Some(to.reloc(c));
            }
            c.header.reloced
        }
    }

    pub fn free(&mut self, ClauseRef(cr): ClauseRef) {
        let c = self.ra.get_mut(cr);
        assert!(!c.is_deleted());
        c.header.mark |= 1;
        self.lc.sub(c);
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
