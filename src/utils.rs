use std::collections::HashMap;
use std::hash::Hash;

use itertools::Itertools;

pub fn group_by<'a, I, A, B>(v: I) -> HashMap<A, Vec<B>>
where
    I: Iterator<Item = (A, B)>,
    A: PartialEq + Eq + Hash + Clone,
{
    let mut map = HashMap::new();
    for (key, values) in v.group_by(|(k, _v)| k.clone()).into_iter() {
        for (_, value) in values {
            map.entry(key.clone()).or_insert_with(Vec::<B>::new).push(value);
        }
    }
    map
}
