use std::sync::atomic;


// Resource contraints:
pub struct Budget {
    conflict_budget: i64,    // -1 means no budget.
    propagation_budget: i64, // -1 means no budget.
    asynch_interrupt: atomic::AtomicBool,
}

impl Budget {
    pub fn new() -> Budget {
        Budget {
            conflict_budget: -1,
            propagation_budget: -1,
            asynch_interrupt: atomic::AtomicBool::new(false),
        }
    }

    pub fn within(&self, conflicts: u64, propagations: u64) -> bool {
        !self.asynch_interrupt.load(atomic::Ordering::Relaxed)
            && (self.conflict_budget < 0 || conflicts < self.conflict_budget as u64)
            && (self.propagation_budget < 0 || propagations < self.propagation_budget as u64)
    }

    pub fn interrupted(&self) -> bool {
        self.asynch_interrupt.load(atomic::Ordering::Relaxed)
    }

    pub fn off(&mut self) {
        self.conflict_budget = -1;
        self.propagation_budget = -1;
    }
}
