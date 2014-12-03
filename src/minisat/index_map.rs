use std::collections::{VecMap};


pub trait HasIndex {
    fn toIndex(&self) -> uint;
}


pub struct IndexMap<K : HasIndex, V> {
    map : VecMap<V>
}

impl<K : HasIndex, V> IndexMap<K, V> {
    pub fn new() -> IndexMap<K, V> {
        IndexMap { map : VecMap::new() }
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
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
}

impl<K : HasIndex, V : Clone> IndexMap<K, V> {
    #[inline]
    pub fn update(&mut self, k : &K, new : V, ff : |V, V| -> V) -> bool {
        self.map.update(k.toIndex(), new, ff)
    }
}

impl<K : HasIndex, V> Index<K, V> for IndexMap<K, V> {
    #[inline]
    fn index(&self, k : &K) -> &V {
        self.map.index(&k.toIndex())
    }
}

impl<K : HasIndex, V> IndexMut<K, V> for IndexMap<K, V> {
    #[inline]
    fn index_mut(&mut self, k : &K) -> &mut V {
        self.map.index_mut(&k.toIndex())
    }
}

