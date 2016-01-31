use std::marker;
use std::ops;
use vec_map;
use super::{Var, Lit};


pub type VarMap<V> = IdxMap<Var, V>;
pub type LitMap<V> = IdxMap<Lit, V>;


trait Idx {
    fn idx(&self) -> usize;
    fn unidx(usize) -> Self;
}

impl Idx for Var {
    #[inline]
    fn idx(&self) -> usize {
        let Var(ref idx) = *self;
        *idx
    }

    #[inline]
    fn unidx(idx : usize) -> Var {
        Var(idx)
    }
}

impl Idx for Lit {
    #[inline]
    fn idx(&self) -> usize {
        let Lit(ref idx) = *self;
        *idx
    }

    #[inline]
    fn unidx(idx : usize) -> Lit {
        Lit(idx)
    }
}


struct IdxMap<K : Idx, V> {
    map : vec_map::VecMap<V>,
    ph  : marker::PhantomData<K>
}

impl<K : Idx, V> IdxMap<K, V> {
    pub fn new() -> IdxMap<K, V> {
        IdxMap { map : vec_map::VecMap::new(), ph : marker::PhantomData }
    }

    pub fn clear(&mut self) {
        self.map.clear();
    }

    #[inline]
    pub fn contains_key(&self, k : &K) -> bool {
        self.map.contains_key(&k.idx())
    }

    #[inline]
    pub fn insert(&mut self, k : &K, v : V) -> Option<V> {
        self.map.insert(k.idx(), v)
    }

    #[inline]
    pub fn remove(&mut self, k : &K) -> Option<V> {
        self.map.remove(&k.idx())
    }

    #[inline]
    pub fn get(&self, k : &K) -> Option<&V> {
        self.map.get(&k.idx())
    }

    #[inline]
    pub fn iter(&self) -> Iter<K, V> {
        Iter { it : self.map.iter(), ph : marker::PhantomData }
    }

    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut { it : self.map.iter_mut(), ph : marker::PhantomData }
    }
}

impl<'r, K : Idx, V> ops::Index<&'r K> for IdxMap<K, V> {
    type Output = V;

    #[inline]
    fn index(&self, k : &'r K) -> &V {
        self.map.index(&k.idx())
    }
}

impl<'r, K : Idx, V> ops::IndexMut<&'r K> for IdxMap<K, V> {
    #[inline]
    fn index_mut(&mut self, k : &'r K) -> &mut V {
        self.map.index_mut(&k.idx())
    }
}


struct Iter<'a, K : Idx, V : 'a> {
    it : vec_map::Iter<'a, V>,
    ph : marker::PhantomData<K>
}

impl<'a, K : Idx, V : 'a> Iterator for Iter<'a, K, V> {
    type Item = (K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<(K, &'a V)> {
        self.it.next().map(|(idx, v)| (Idx::unidx(idx), v))
    }
}


struct IterMut<'a, K : Idx, V : 'a> {
    it : vec_map::IterMut<'a, V>,
    ph : marker::PhantomData<K>
}

impl<'a, K : Idx, V : 'a> Iterator for IterMut<'a, K, V> {
    type Item = (K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<(K, &'a mut V)> {
        self.it.next().map(|(idx, v)| (Idx::unidx(idx), v))
    }
}
