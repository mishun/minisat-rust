use std::collections::vec_deque;
use crate::sat::formula::{assignment::*, clause::*, Lit};


pub struct SubsumptionQueue {
    subsumption_queue: vec_deque::VecDeque<ClauseRef>,
    bwdsub_assigns: usize,
}

pub enum SubsumptionJob {
    Clause(ClauseRef),
    Assign(Lit),
}

impl SubsumptionQueue {
    pub fn new() -> Self {
        SubsumptionQueue {
            subsumption_queue: vec_deque::VecDeque::new(),
            bwdsub_assigns: 0,
        }
    }

    pub fn pop(&mut self, ca: &ClauseAllocator, assigns: &Assignment) -> Option<SubsumptionJob> {
        let trail = assigns.trail_at(GROUND_LEVEL);
        loop {
            match self.subsumption_queue.pop_front() {
                Some(cr) => if !ca.is_deleted(cr) {
                    return Some(SubsumptionJob::Clause(cr));
                }

                None if self.bwdsub_assigns < trail.len() => {
                    let lit = trail[self.bwdsub_assigns];
                    self.bwdsub_assigns += 1;
                    return Some(SubsumptionJob::Assign(lit));
                }

                None => {
                    return None;
                }
            }
        }
    }

    pub fn push(&mut self, cr: ClauseRef) {
        self.subsumption_queue.push_back(cr);
    }

    pub fn try_push(&mut self, cr: ClauseRef) {
        // FIX: this is too inefficient but would be nice to have (properly implemented)
        // if (!find(subsumption_queue, &c))
        self.push(cr);
    }

    pub fn len(&self) -> usize {
        self.subsumption_queue.len()
    }

    pub fn is_empty(&self) -> bool {
        self.subsumption_queue.is_empty()
    }

    pub fn assigns_left(&self, assigns: &Assignment) -> usize {
        assigns.number_of_ground_assigns() - self.bwdsub_assigns
    }

    pub fn clear(&mut self, assigns: &Assignment) {
        self.subsumption_queue.clear();
        self.bwdsub_assigns = assigns.number_of_ground_assigns();
    }

    pub fn iter(&self) -> vec_deque::Iter<ClauseRef> {
        self.subsumption_queue.iter()
    }

    pub fn gc(&mut self, gc: &mut ClauseGC) {
        let mut j = 0;
        for i in 0..self.subsumption_queue.len() {
            if let Some(cr) = gc.relocate(self.subsumption_queue[i]) {
                self.subsumption_queue[j] = cr;
                j += 1;
            }
        }
        self.subsumption_queue.truncate(j);
    }
}
