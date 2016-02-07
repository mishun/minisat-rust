use std::collections::vec_deque::VecDeque;
use sat::formula::Lit;
use sat::formula::assignment::Assignment;
use sat::formula::clause::*;


pub struct SubsumptionQueue {
    subsumption_queue : VecDeque<ClauseRef>,
    bwdsub_assigns    : usize
}

pub enum SubsumptionJob {
    Clause(ClauseRef),
    Assign(Lit)
}

impl SubsumptionQueue {
    pub fn new() -> Self {
        SubsumptionQueue { subsumption_queue : VecDeque::new()
                         , bwdsub_assigns    : 0
                         }
    }

    pub fn pop(&mut self, ca : &ClauseAllocator, assigns : &Assignment) -> Option<SubsumptionJob> {
        loop {
            match self.subsumption_queue.pop_front() {
                Some(cr) => {
                    if !ca.isDeleted(cr) {
                        return Some(SubsumptionJob::Clause(cr));
                    }
                }

                None if self.bwdsub_assigns < assigns.numberOfGroundAssigns() => {
                    let lit = assigns.assignAt(self.bwdsub_assigns);
                    self.bwdsub_assigns += 1;
                    return Some(SubsumptionJob::Assign(lit));
                }

                None => {
                    return None;
                }
            }
        }
    }

    pub fn push(&mut self, cr : ClauseRef) {
        self.subsumption_queue.push_back(cr);
    }

    pub fn len(&self) -> usize {
        self.subsumption_queue.len()
    }

    pub fn assignsLeft(&self, assigns : &Assignment) -> usize {
        assigns.numberOfGroundAssigns() - self.bwdsub_assigns
    }

    pub fn clear(&mut self, assigns : &Assignment) {
        self.subsumption_queue.clear();
        self.bwdsub_assigns = assigns.numberOfGroundAssigns();
    }

    pub fn remarkQueued(&mut self, ca : &mut ClauseAllocator, src : u32, dst : u32) {
        for cr in self.subsumption_queue.iter() {
            let c = ca.edit(*cr);
            if c.mark() == src {
                c.setMark(dst);
            }
        }
    }

    pub fn relocGC(&mut self, from : &mut ClauseAllocator, to : &mut ClauseAllocator) {
        self.subsumption_queue.retain(|cr| { !from.isDeleted(*cr) });
        for cr in self.subsumption_queue.iter_mut() {
            *cr = from.relocTo(to, *cr);
        }
    }
}
