use std::num;


#[derive(Clone, Copy)]
pub enum ClauseHeader {
    Clause { abstraction: Option<num::NonZeroU32> },
    Learnt { activity: f32 }
}

impl ClauseHeader {
    pub fn activity(&self) -> f32 {
        if let ClauseHeader::Learnt { activity } = self {
            *activity
        } else {
            panic!("Learnt expected");
        }
    }
}
