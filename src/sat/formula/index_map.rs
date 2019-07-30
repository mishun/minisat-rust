use std::{marker, ops, slice};
use vec_map;
use super::{Lit, Var};


pub type VarMap<V> = IdxMap<Var, V>;
pub type LitMap<V> = IdxMap<Lit, V>;
pub type VarVec<V> = IdxVec<Var, V>;
pub type LitVec<V> = IdxVec<Lit, V>;
pub type VarHeap = IdxHeap<Var>;


pub trait Idx {
    fn idx(&self) -> usize;
    fn unidx(_: usize) -> Self;
}

impl Idx for Var {
    #[inline]
    fn idx(&self) -> usize {
        self.0
    }

    #[inline]
    fn unidx(idx: usize) -> Var {
        Var(idx)
    }
}

impl Idx for Lit {
    #[inline]
    fn idx(&self) -> usize {
        self.0
    }

    #[inline]
    fn unidx(idx: usize) -> Lit {
        Lit(idx)
    }
}


pub struct IdxMap<K: Idx, V> {
    map: vec_map::VecMap<V>,
    ph: marker::PhantomData<K>,
}

impl<K: Idx, V> IdxMap<K, V> {
    pub fn new() -> Self {
        IdxMap {
            map: vec_map::VecMap::new(),
            ph: marker::PhantomData,
        }
    }

    #[inline]
    pub fn insert(&mut self, k: &K, v: V) -> Option<V> {
        self.map.insert(k.idx(), v)
    }

    #[inline]
    pub fn remove(&mut self, k: &K) -> Option<V> {
        self.map.remove(k.idx())
    }

    #[inline]
    pub fn get(&self, k: &K) -> Option<&V> {
        self.map.get(k.idx())
    }

    #[inline]
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            it: self.map.iter(),
            ph: marker::PhantomData,
        }
    }

    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut {
            it: self.map.iter_mut(),
            ph: marker::PhantomData,
        }
    }
}

impl<'r, K: Idx, V> ops::Index<&'r K> for IdxMap<K, V> {
    type Output = V;

    #[inline]
    fn index(&self, k: &'r K) -> &V {
        self.map.index(&k.idx())
    }
}

impl<'r, K: Idx, V> ops::IndexMut<&'r K> for IdxMap<K, V> {
    #[inline]
    fn index_mut(&mut self, k: &'r K) -> &mut V {
        self.map.index_mut(&k.idx())
    }
}


pub struct Iter<'a, K: Idx, V: 'a> {
    it: vec_map::Iter<'a, V>,
    ph: marker::PhantomData<K>,
}

impl<'a, K: Idx, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<(K, &'a V)> {
        self.it.next().map(|(idx, v)| (Idx::unidx(idx), v))
    }
}


pub struct IterMut<'a, K: Idx, V: 'a> {
    it: vec_map::IterMut<'a, V>,
    ph: marker::PhantomData<K>,
}

impl<'a, K: Idx, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<(K, &'a mut V)> {
        self.it.next().map(|(idx, v)| (Idx::unidx(idx), v))
    }
}


pub struct IdxVec<K: Idx, V> {
    vec: Vec<V>,
    ph: marker::PhantomData<K>,
}

impl<K: Idx, V: Default> IdxVec<K, V> {
    pub fn new() -> Self {
        IdxVec {
            vec: Vec::new(),
            ph: marker::PhantomData,
        }
    }

    #[inline]
    pub fn init(&mut self, k: K) {
        while self.vec.len() <= k.idx() {
            self.vec.push(V::default());
        }
    }

    #[inline]
    pub fn iter(&self) -> slice::Iter<V> {
        self.vec.iter()
    }

    #[inline]
    pub fn iter_mut(&mut self) -> slice::IterMut<V> {
        self.vec.iter_mut()
    }
}

impl<K: Idx, V> ops::Index<K> for IdxVec<K, V> {
    type Output = V;

    #[inline]
    fn index(&self, k: K) -> &V {
        &self.vec[k.idx()]
    }
}

impl<K: Idx, V> ops::IndexMut<K> for IdxVec<K, V> {
    #[inline]
    fn index_mut(&mut self, k: K) -> &mut V {
        &mut self.vec[k.idx()]
    }
}


pub struct IdxHeap<K: Idx> {
    heap: Vec<K>,
    index: vec_map::VecMap<usize>,
}

impl<K: Idx> IdxHeap<K> {
    pub fn new() -> Self {
        IdxHeap {
            heap: Vec::new(),
            index: vec_map::VecMap::new(),
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
    pub fn contains(&self, key: &K) -> bool {
        self.index.contains_key(key.idx())
    }

    #[inline]
    pub fn clear(&mut self) {
        self.heap.clear();
        self.index.clear();
    }

    #[inline]
    pub fn insert<F: Fn(&K, &K) -> bool>(&mut self, key: K, before: F) -> bool {
        if !self.index.contains_key(key.idx()) {
            let place = self.heap.len();
            self.heap.push(key);
            self.sift_up(place, before);
            true
        } else {
            false
        }
    }

    #[inline]
    pub fn pop<F: Fn(&K, &K) -> bool>(&mut self, before: F) -> Option<K> {
        if self.heap.is_empty() {
            None
        } else {
            let res = self.heap.swap_remove(0);
            self.index.remove(res.idx());
            if !self.heap.is_empty() {
                self.sift_down(0, &before);
            }
            Some(res)
        }
    }

    #[inline]
    pub fn update<F: Fn(&K, &K) -> bool>(&mut self, key: &K, before: F) -> bool {
        let place = match self.index.get(key.idx()) {
            None => {
                return false;
            }
            Some(i) => *i,
        };

        self.sift_down(place, &before);
        self.sift_up(place, before);
        true
    }

    pub fn heapify_from<F: Fn(&K, &K) -> bool>(&mut self, from: Vec<K>, before: F) {
        self.index.clear();
        self.heap = from;

        for i in (0..self.heap.len()).rev() {
            self.sift_down(i, &before);
        }
    }

    #[inline]
    fn sift_up<F: Fn(&K, &K) -> bool>(&mut self, mut i: usize, before: F) {
        while i > 0 {
            let p = (i - 1) >> 1;
            if before(&self.heap[i], &self.heap[p]) {
                self.index.insert(self.heap[p].idx(), i);
                self.heap.swap(i, p);
                i = p;
            } else {
                break;
            }
        }

        self.index.insert(self.heap[i].idx(), i);
    }

    #[inline]
    fn sift_down<F: Fn(&K, &K) -> bool>(&mut self, mut i: usize, before: &F) {
        loop {
            let c = {
                let l = 2 * i + 1;
                if l >= self.heap.len() {
                    break;
                }
                let r = l + 1;
                if r < self.heap.len() && before(&self.heap[r], &self.heap[l]) {
                    r
                } else {
                    l
                }
            };

            if before(&self.heap[c], &self.heap[i]) {
                self.index.insert(self.heap[c].idx(), i);
                self.heap.swap(c, i);
                i = c;
            } else {
                break;
            }
        }

        self.index.insert(self.heap[i].idx(), i);
    }
}

impl<K: Idx> ops::Index<usize> for IdxHeap<K> {
    type Output = K;

    #[inline]
    fn index(&self, i: usize) -> &K {
        self.heap.index(i)
    }
}
