use std::{alloc, mem, ptr};
use std::marker::PhantomData;


pub type Ref = u32;

pub struct RegionAllocator<T> {
    memory: *mut u8,
    offset: usize,
    capacity: usize,
    phantom: PhantomData<T>
}

impl<T> RegionAllocator<T> {
    pub fn with_capacity(capacity: usize) -> Self {
        let mut ra = RegionAllocator {
            memory: ptr::null_mut(),
            offset: 0,
            capacity: 0,
            phantom: PhantomData
        };
        ra.ensure_capacity(capacity);
        ra
    }

    fn ensure_capacity(&mut self, min_capacity: usize) {
        if self.capacity < min_capacity {
            let mut new_capacity = self.capacity;
            while new_capacity < min_capacity {
                let delta = ((new_capacity >> 1) + (new_capacity >> 3) + 2) & !1;
                new_capacity += delta;
                match usize::checked_add(new_capacity, delta) {
                    Some(res) => new_capacity = res,
                    None      => panic!("overflow")
                }
            }

            self.memory =
                unsafe {
                    if self.memory.is_null() {
                        let new_layout = alloc::Layout::from_size_align_unchecked(new_capacity, mem::align_of::<T>());
                        alloc::alloc_zeroed(new_layout)
                    } else {
                        let old_layout = alloc::Layout::from_size_align_unchecked(self.capacity, mem::align_of::<T>());
                        alloc::realloc(self.memory, old_layout, new_capacity)
                    }
                };
            self.capacity = new_capacity;
        }
    }

    pub unsafe fn allocate_with_extra<E>(&mut self, extra: usize) -> (&mut T, Ref) {
        if self.offset > Ref::max_value() as usize {
            panic!("Ref {} is out of bound {}", self.offset, Ref::max_value())
        }

        let size = mem::size_of::<T>() + extra * mem::size_of::<E>();
        let increment = {
            let align = mem::align_of::<T>();
            if size & (align - 1) == 0 {
                size
            } else {
                (size & !(align - 1)) + align
            }
        };

        self.ensure_capacity(self.offset + size);
        let reference = self.offset as Ref;
        self.offset += increment;
        (self.get_mut(reference), reference)
    }

    pub fn allocated_bytes(&self) -> usize {
        self.offset
    }

    #[inline]
    pub fn get(&self, reference: Ref) -> &T {
        assert!((reference as usize) < self.offset);
        unsafe { &*(self.memory.offset(reference as isize) as *const T) }
    }

    #[inline]
    pub fn get_mut(&self, reference: Ref) -> &mut T {
        assert!((reference as usize) < self.offset);
        unsafe { &mut *(self.memory.offset(reference as isize) as *mut T) }
    }
}

impl<T> Drop for RegionAllocator<T> {
    fn drop(&mut self) {
        if !self.memory.is_null() {
            unsafe {
                let layout = alloc::Layout::from_size_align_unchecked(self.capacity, mem::align_of::<T>());
                alloc::dealloc(self.memory, layout);
            }
        }
    }
}
