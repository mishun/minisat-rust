use std::{fmt, ptr, slice};
use super::Lit;


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
    len: usize,
    data: Box<[Lit]>,
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
        unsafe { *self.data.get_unchecked(0) }
    }

    #[inline]
    pub fn head_pair(&self) -> (Lit, Lit) {
        assert!(self.len > 1);
        (self.data[0], self.data[1])
    }

    #[inline]
    pub fn lits<'c>(&'c self) -> &'c [Lit] {
        unsafe { slice::from_raw_parts(self.data.as_ptr(), self.len) }
    }

    #[inline]
    pub fn lits_from<'c>(&'c self, start: usize) -> &'c [Lit] {
        &self.lits()[start..]
    }


    #[inline]
    pub fn swap(&mut self, i: usize, j: usize) {
        self.data.swap(i, j);
    }

    #[inline]
    pub fn retain_suffix<F: Fn(&Lit) -> bool>(&mut self, base: usize, f: F) {
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

    #[inline]
    pub fn pull_literal<F: FnMut(Lit) -> bool>(&mut self, place: usize, mut f: F) -> Option<Lit> {
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


    pub fn strengthen(&mut self, p: Lit) {
        for i in 0..self.len {
            if self.data[i] == p {
                for j in i + 1..self.len {
                    self.data[j - 1] = self.data[j];
                }
                self.len -= 1;
                self.calc_abstraction();
                return;
            }
        }
    }

    fn abstraction(&self) -> u32 {
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


pub enum Subsumes {
    Different,
    Exact,
    LitSign(Lit),
}

pub fn subsumes(this: &Clause, other: &Clause) -> Subsumes {
    assert!(!this.is_learnt());
    assert!(!other.is_learnt());

    if other.len() < this.len() || (this.abstraction() & !other.abstraction()) != 0 {
        return Subsumes::Different;
    }

    let mut ret = Subsumes::Exact;
    for &lit in this.lits() {
        // search for lit or ¬lit
        let mut found = false;
        for &cur in other.lits() {
            if lit == cur {
                found = true;
                break;
            } else if lit == !cur {
                if let Subsumes::Exact = ret {
                    ret = Subsumes::LitSign(lit);
                    found = true;
                    break;
                } else {
                    return Subsumes::Different;
                }
            }
        }

        // did not find it
        if !found {
            return Subsumes::Different;
        }
    }

    return ret;
}

pub fn unit_subsumes(unit: Lit, c: &Clause) -> Subsumes {
    assert!(!c.is_learnt());

    if unit.abstraction() & !c.abstraction() != 0 {
        return Subsumes::Different;
    }

    for &cur in c.lits() {
        if unit == cur {
            return Subsumes::Exact;
        } else if unit == !cur {
            return Subsumes::LitSign(unit);
        }
    }

    return Subsumes::Different;
}


#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct ClauseRef(usize);


pub struct ClauseAllocator {
    clauses: Vec<Clause>,
    lc: LegacyCounter,
    extra_clause_field: bool,
}

impl ClauseAllocator {
    pub fn new_empty() -> ClauseAllocator {
        ClauseAllocator {
            clauses: Vec::new(),
            lc: LegacyCounter::new(),
            extra_clause_field: false,
        }
    }

    pub fn new_for_gc(old: &ClauseAllocator) -> ClauseAllocator {
        // old.size - old.wasted
        ClauseAllocator {
            clauses: Vec::new(),
            lc: LegacyCounter::new(),
            extra_clause_field: old.extra_clause_field,
        }
    }

    pub fn alloc(&mut self, ps: Box<[Lit]>, learnt: bool) -> (&Clause, ClauseRef) {
        assert!(ps.len() > 1);
        let mut c = Clause {
            header: ClauseHeader {
                mark: 0,
                learnt: learnt,
                has_extra: learnt | self.extra_clause_field,
                data_act: 0.0,
                data_abs: 0,
                reloced: None,
            },
            len: ps.len(),
            data: ps,
        };

        if c.header.has_extra {
            if c.header.learnt {
                c.header.data_act = 0.0;
            } else {
                c.calc_abstraction();
            };
        }

        self.lc.add(&c);

        let index = self.clauses.len();
        self.clauses.push(c);
        (&self.clauses[index], ClauseRef(index))
    }

    fn reloc(&mut self, src: &Clause) -> ClauseRef {
        let mut c = Clause {
            header: src.header,
            len: src.len,
            data: src.data.clone(),
        };
        c.header.has_extra |= self.extra_clause_field;
        self.lc.add(&c);

        let index = self.clauses.len();
        self.clauses.push(c);
        ClauseRef(index)
    }

    pub fn free(&mut self, ClauseRef(cr): ClauseRef) {
        let ref mut c = self.clauses[cr];
        assert!(!c.is_deleted());
        c.header.mark |= 1;
        self.lc.sub(c);
    }

    #[inline]
    pub fn is_deleted(&self, ClauseRef(index): ClauseRef) -> bool {
        self.clauses[index].is_deleted()
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
    pub fn view<'a>(&'a self, ClauseRef(index): ClauseRef) -> &'a Clause {
        assert!(index < self.clauses.len());
        &self.clauses[index]
    }

    #[inline]
    pub fn edit<'a>(&'a mut self, ClauseRef(index): ClauseRef) -> &'a mut Clause {
        assert!(index < self.clauses.len());
        &mut self.clauses[index]
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

    pub fn add(&mut self, c: &Clause) {
        self.size += Self::clause_size(c.len, c.header.has_extra);
    }

    pub fn sub(&mut self, c: &Clause) {
        self.wasted += Self::clause_size(c.len, c.header.has_extra);
    }
}
