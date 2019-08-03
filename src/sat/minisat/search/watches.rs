use std::{mem, ptr};
use crate::sat::formula::{assignment::Assignment, clause::*, Lit, LitVec, Var};


#[derive(Clone, Copy, Debug)]
struct Watcher {
    pub cref: ClauseRef,
    pub blocker: Lit,
}


#[derive(Default, Debug)]
struct WatchesLine {
    watchers: Vec<Watcher>,
    dirty: bool,
}


pub struct Watches {
    watches: LitVec<WatchesLine>,
    pub propagations: u64,
}

impl Watches {
    pub fn new() -> Self {
        Watches {
            watches: LitVec::new(),
            propagations: 0,
        }
    }

    pub fn init_var(&mut self, v: Var) {
        self.watches.init(v.pos_lit());
        self.watches.init(v.neg_lit());
    }

    pub fn try_clear_var(&mut self, _: Var) {}

    pub fn watch_clause(&mut self, c: &Clause, cr: ClauseRef) {
        for i in 0..2 {
            let w = Watcher { cref: cr, blocker: c.head[i ^ 1] };
            self.watches[!c.head[i]].watchers.push(w);
        }
    }

    pub fn unwatch_clause_strict(&mut self, c: &Clause, cr: ClauseRef) {
        for &lit in &c.head {
            self.watches[!lit].watchers.retain(|w| w.cref != cr);
        }
    }

    pub fn unwatch_clause_lazy(&mut self, c: &Clause) {
        for &lit in &c.head {
            self.watches[!lit].dirty = true;
        }
    }

    // Description:
    //   Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
    //   otherwise CRef_Undef.
    //
    //   Post-conditions:
    //     * the propagation queue is empty, even if there was a conflict.
    pub fn propagate(&mut self, ca: &mut ClauseAllocator, assigns: &mut Assignment) -> Option<ClauseRef> {
        while let Some(p) = assigns.dequeue() {
            self.propagations += 1;

            {
                let ref mut line = self.watches[p];
                if line.dirty {
                    line.watchers.retain(|w| !ca.is_deleted(w.cref));
                    line.dirty = false;
                }
            }

            unsafe {
                let not_p = !p;
                let p_watches = &mut self.watches[p].watchers as *mut Vec<Watcher>;

                let watch_l = (*p_watches).as_mut_ptr();
                let watch_r = watch_l.add((*p_watches).len());

                let mut head = watch_l;
                let mut tail = watch_l;
                'next_watch: while head < watch_r {
                    let pwi = *head;
                    head = head.offset(1);

                    if assigns.is_assigned_pos(pwi.blocker) {
                        *tail = pwi;
                        tail = tail.offset(1);
                        continue;
                    }

                    let clause = ca.edit(pwi.cref);
                    //if clause.is_deleted() {
                    //    continue;
                    //}

                    if clause.head[0] == not_p {
                        clause.head.swap(0, 1);
                    }
                    //assert!(clause.head[1] == not_p);

                    // If 0th watch is true, then clause is already satisfied.
                    let cw = Watcher { cref: pwi.cref, blocker: clause.head[0] };
                    if cw.blocker != pwi.blocker && assigns.is_assigned_pos(cw.blocker) {
                        *tail = cw;
                        tail = tail.offset(1);
                        continue;
                    }

                    // Look for new watch:
                    {
                        let (clause_l, clause_r) = clause.ptr_range();
                        let mut plit = clause_l.offset(2);
                        while plit < clause_r {
                            if !assigns.is_assigned_neg(*plit) {
                                self.watches[!*plit].watchers.push(cw);
                                ptr::swap(clause_l.offset(1), plit);
                                continue 'next_watch;
                            }
                            plit = plit.offset(1);
                        }
                    }

                    // Did not find watch -- clause is unit under assignment:
                    *tail = cw;
                    tail = tail.offset(1);
                    if assigns.is_assigned_neg(cw.blocker) {
                        let copied = ptr_diff(watch_l, tail);
                        let remaining = ptr_diff(head, watch_r);
                        ptr::copy(head, tail, remaining);
                        (*p_watches).truncate(copied + remaining);

                        return Some(cw.cref);
                    } else {
                        assigns.assign_lit(cw.blocker, Some(cw.cref));
                    }
                }

                let copied = ptr_diff(watch_l, tail);
                (*p_watches).truncate(copied);
            }
        }

        None
    }

    pub fn reloc_gc(&mut self, from: &mut ClauseAllocator, to: &mut ClauseAllocator) {
        for line in self.watches.iter_mut() {
            line.dirty = false;
            line.watchers.retain(|w| !from.is_deleted(w.cref));
            for w in line.watchers.iter_mut() {
                w.cref = from.reloc_to(to, w.cref).unwrap();
            }
        }
    }
}


// TODO: replace it with future std function
#[inline]
fn ptr_diff<T>(a: *mut T, b: *mut T) -> usize {
    ((b as usize) - (a as usize)) / mem::size_of::<T>()
}
