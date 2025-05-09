pub mod utils{
  use std::collections::{HashMap, HashSet};
  use core::hash::Hash;
  
  pub fn union_with<K,V, F>(mut left: HashMap<K,V>, right: HashMap<K,V>, fun: F) -> HashMap<K,V>
    where K:PartialEq, K:Eq, K:Hash, F: Fn(V,V) -> V{
      for (k, v) in right {
        if let Some(w) = left.remove(&k) {
          left.insert(k, fun(w, v));
        }
        else{
          left.insert(k, v);
        }
      }
      return left;
    }

  pub fn union<V>(mut left: HashSet<V>, right: HashSet<V>) -> HashSet<V>
    where  V: Eq, V: Hash, {
    for elem in right{
      left.insert(elem);
    }
    return left;
  }

  pub fn hash_unit<T>(t: T) -> HashSet<T> where T: Eq, T: Hash{
    let mut h = HashSet::new();
    h.insert(t);
    return h;
  }  
}