use std::{alloc, mem, ptr};


pub type Ref = u32;

pub struct RegionAllocator {
    memory: *mut u8,
    offset: usize,
    capacity: usize,
    align: usize
}

impl RegionAllocator {
    pub fn with_capacity(capacity: usize, align: usize) -> Self {
        let mut ra = RegionAllocator {
            memory: ptr::null_mut(),
            offset: 0,
            capacity: 0,
            align: align
        };
        unsafe { ra.ensure_capacity(capacity); }
        ra
    }

    unsafe fn ensure_capacity(&mut self, min_capacity: usize) {
        if self.capacity >= min_capacity {
            return;
        }

        let new_capacity = {
            let mut new_capacity = self.capacity;
            while new_capacity < min_capacity {
                let delta = ((new_capacity >> 1) + (new_capacity >> 3) + 2) & !1;
                match usize::checked_add(new_capacity, delta) {
                    Some(res) => { new_capacity = res }
                    None => { panic!("overflow") }
                }
            }
            new_capacity
        };

        let new_memory =
            if self.memory.is_null() {
                let new_layout = alloc::Layout::from_size_align_unchecked(new_capacity, self.align);
                alloc::alloc_zeroed(new_layout)
            } else {
                let old_layout = alloc::Layout::from_size_align_unchecked(self.capacity, self.align);
                alloc::realloc(self.memory, old_layout, new_capacity)
            };

        if new_memory.is_null() {
            panic!("(Re)Allocation failed");
        }

        self.memory = new_memory;
        self.capacity = new_capacity;
    }

    pub unsafe fn allocate_with_extra<T, E>(&mut self, extra: usize) -> (&mut T, Ref) {
        let offset = {
            let align = mem::align_of::<T>();
            assert!(align <= self.align);
            if (self.offset & (align - 1)) == 0 {
                self.offset
            } else {
                match usize::checked_add(self.offset & !(align - 1), align) {
                    Some(offset) => { offset }
                    None => { panic!("overflow") }
                }
            }
        };

        assert!(offset <= Ref::max_value() as usize, "{} is out of bound", offset);
        let size = mem::size_of::<T>() + extra * mem::size_of::<E>();

        match usize::checked_add(offset, size) {
            Some(new_offset) => {
                self.ensure_capacity(new_offset);
                self.offset = new_offset;
            }
            None => { panic!("overflow") }
        }

        let reference = offset as u32;
        (self.get_mut(reference), reference)
    }

    #[inline]
    pub unsafe fn get<T>(&self, reference: Ref) -> &T {
        assert!((reference as usize) < self.offset);
        &*(self.memory.add(reference as usize) as *const T)
    }

    #[inline]
    pub unsafe fn get_mut<T>(&self, reference: Ref) -> &mut T {
        assert!((reference as usize) < self.offset);
        &mut *(self.memory.add(reference as usize) as *mut T)
    }

    pub fn allocated_bytes(&self) -> usize {
        self.offset
    }
}

impl Drop for RegionAllocator {
    fn drop(&mut self) {
        if !self.memory.is_null() {
            unsafe {
                let layout = alloc::Layout::from_size_align_unchecked(self.capacity, self.align);
                alloc::dealloc(self.memory, layout);
            }
        }
    }
}
