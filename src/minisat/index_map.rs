use std::marker::PhantomData;
use vec_map::VecMap;
use std::ops::{Index, IndexMut};


pub trait HasIndex {
    fn toIndex(&self) -> usize;
}


pub struct IndexMap<K : HasIndex, V> {
    map : VecMap<V>,
    tmp : PhantomData<K>
}

impl<K : HasIndex, V> IndexMap<K, V> {
    pub fn new() -> IndexMap<K, V> {
        IndexMap { map : VecMap::new()
                 , tmp : PhantomData
                 }
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
    pub fn modify_in_place<F : FnMut(&mut V) -> ()>(&mut self, mut f : F) {
        for (_, v) in self.map.iter_mut() {
            f(v);
        }
    }
}

impl<'r, K : HasIndex, V> Index<&'r K> for IndexMap<K, V> {
    type Output = V;

    #[inline]
    fn index(&self, k : &'r K) -> &V {
        self.map.index(&k.toIndex())
    }
}

impl<'r, K : HasIndex, V> IndexMut<&'r K> for IndexMap<K, V> {
    #[inline]
    fn index_mut(&mut self, k : &'r K) -> &mut V {
        self.map.index_mut(&k.toIndex())
    }
}
