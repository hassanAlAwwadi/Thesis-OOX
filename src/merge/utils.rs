pub mod utils {
    use core::hash::Hash;
    use std::collections::{HashMap, HashSet};

    pub fn union_with<K, V>(
        mut left: HashMap<K, V>,
        mut right: HashMap<K, V>,
        combine: impl Fn(V, V) -> V,
        lift_l: impl Fn(V) -> V, 
        lift_r: impl Fn(V) -> V, 
    ) -> HashMap<K, V>
    where
        K: PartialEq,
        K: Eq,
        K: Hash,
        V: Clone,
    {
        for (k, v) in left.iter_mut(){
            if let Some(r) = right.remove(k){
                *v = combine(v.clone(), r);
            }else{
                *v = lift_l(v.clone()); 
            }


        }
        for (k, r) in right.into_iter(){
            left.insert(k, lift_r(r));
        }
        return left; 
    }
    pub fn union<V>(mut left: HashSet<V>, right: HashSet<V>) -> HashSet<V>
    where
        V: Eq,
        V: Hash,
    {
        for elem in right {
            left.insert(elem);
        }
        return left;
    }

    pub fn hash_unit<T>(t: T) -> HashSet<T>
    where
        T: Eq,
        T: Hash,
    {
        let mut h = HashSet::new();
        h.insert(t);
        return h;
    }
}
