use std::ops::{Index};
use super::index_map::{HasIndex, IndexMap};


pub struct ActivityQueue<V : HasIndex> {
    heap     : Vec<V>,
    indices  : IndexMap<V, usize>,
    activity : IndexMap<V, f64>,
}

impl<V : HasIndex> ActivityQueue<V> {
    pub fn new() -> ActivityQueue<V> {
        ActivityQueue {
            heap     : Vec::new(),
            indices  : IndexMap::new(),
            activity : IndexMap::new(),
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.heap.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    #[inline]
    pub fn contains(&self, v : &V) -> bool {
        self.indices.contains_key(v)
    }

    #[inline]
    pub fn getActivity(&self, v : &V) -> f64 {
        self.activity[v]
    }

    pub fn clear(&mut self) {
        self.heap.clear();
        self.indices.clear();
    }

    pub fn scaleActivity(&mut self, factor : f64) {
        self.activity.modify_in_place(|act| { act * factor });
    }
}

impl<V : HasIndex + Clone> ActivityQueue<V> {
    pub fn setActivity(&mut self, v : &V, new : f64) {
        match self.activity.insert(v, new) {
            None      => {}
            Some(old) => {
                if self.indices.contains_key(v) {
                    let i = self.indices[v];
                    if new > old { self.sift_up(i) } else { self.sift_down(i) }
                }
            }
        }
    }

    pub fn insert(&mut self, v : V) {
        if !self.contains(&v) {
            if !self.activity.contains_key(&v) {
                self.activity.insert(&v, 0.0);
            }

            let i = self.heap.len();
            self.indices.insert(&v, i);
            self.heap.push(v);
            self.sift_up(i);
        }
    }

    pub fn pop(&mut self) -> Option<V>
    {
        match self.heap.len() {
            0 => { None }
            1 => {
                let h = self.heap.pop().unwrap();
                self.indices.remove(&h);
                Some(h)
            }
            _ => {
                let h = self.heap[0].clone();
                self.indices.remove(&h);

                let t = self.heap.pop().unwrap();
                self.set(0, t);

                self.sift_down(0);
                Some(h)
            }
        }
    }

    pub fn heapifyFrom(&mut self, from : Vec<V>) {
        self.heap = from;
        self.indices.clear();
        for i in 0 .. self.heap.len() {
            self.indices.insert(&self.heap[i], i);
        }

        for i in (0 .. self.heap.len() / 2).rev() {
            self.sift_down(i);
        }
    }


    fn sift_up(&mut self, mut i : usize) {
        let x = self.heap[i].clone();
        while i > 0 {
            let pi = (i - 1) >> 1;
            let p = self.heap[pi].clone();
            if self.activity[&x] > self.activity[&p] {
                self.set(i, p);
                i = pi;
            } else {
                break
            }
        }
        self.set(i, x);
    }

    fn sift_down(&mut self, mut i : usize) {
        let x = self.heap[i].clone();
        let len = self.heap.len();
        loop {
            let li = i + i + 1;
            if li >= len { break; }
            let ri = i + i + 2;
            let ci = if ri < len && self.activity[&self.heap[ri]] > self.activity[&self.heap[li]] { ri } else { li };
            let c = self.heap[ci].clone();
            if self.activity[&c] <= self.activity[&x] { break; }
            self.set(i, c);
            i = ci;
        }
        self.set(i, x);
    }

    #[inline]
    fn set(&mut self, i : usize, v : V) {
        self.indices.insert(&v, i);
        self.heap[i] = v;
    }
}

impl<V : HasIndex> Index<usize> for ActivityQueue<V> {
    type Output = V;

    #[inline]
    fn index(&self, i : usize) -> &V {
        self.heap.index(i)
    }
}
