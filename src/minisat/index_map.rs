use std::marker;
use std::ops;
use vec_map;


pub trait HasIndex {
    fn toIndex(&self) -> usize;
    fn fromIndex(usize) -> Self;
}


pub struct IndexMap<K : HasIndex, V> {
    map : vec_map::VecMap<V>,
    ph  : marker::PhantomData<K>
}

impl<K : HasIndex, V> IndexMap<K, V> {
    pub fn new() -> IndexMap<K, V> {
        IndexMap { map : vec_map::VecMap::new(), ph : marker::PhantomData }
    }

    pub fn clear(&mut self) {
        self.map.clear();
    }

    #[inline]
    pub fn contains_key(&self, k : &K) -> bool {
        self.map.contains_key(&k.toIndex())
    }

    #[inline]
    pub fn insert(&mut self, k : &K, v : V) -> Option<V> {
        self.map.insert(k.toIndex(), v)
    }

    #[inline]
    pub fn remove(&mut self, k : &K) -> Option<V> {
        self.map.remove(&k.toIndex())
    }

    #[inline]
    pub fn get(&self, k : &K) -> Option<&V> {
        self.map.get(&k.toIndex())
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

impl<'r, K : HasIndex, V> ops::Index<&'r K> for IndexMap<K, V> {
    type Output = V;

    #[inline]
    fn index(&self, k : &'r K) -> &V {
        self.map.index(&k.toIndex())
    }
}

impl<'r, K : HasIndex, V> ops::IndexMut<&'r K> for IndexMap<K, V> {
    #[inline]
    fn index_mut(&mut self, k : &'r K) -> &mut V {
        self.map.index_mut(&k.toIndex())
    }
}


pub struct Iter<'a, K : HasIndex, V : 'a> {
    it : vec_map::Iter<'a, V>,
    ph : marker::PhantomData<K>
}

impl<'a, K : HasIndex, V : 'a> Iterator for Iter<'a, K, V> {
    type Item = (K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<(K, &'a V)> {
        self.it.next().map(|(idx, v)| (HasIndex::fromIndex(idx), v))
    }
}


pub struct IterMut<'a, K : HasIndex, V : 'a> {
    it : vec_map::IterMut<'a, V>,
    ph : marker::PhantomData<K>
}

impl<'a, K : HasIndex, V : 'a> Iterator for IterMut<'a, K, V> {
    type Item = (K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<(K, &'a mut V)> {
        self.it.next().map(|(idx, v)| (HasIndex::fromIndex(idx), v))
    }
}
