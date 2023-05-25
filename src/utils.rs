use std::collections::HashMap;
use std::hash::Hash;

use im_rc::Vector;
use itertools::Itertools;

pub fn group_by<'a, I, A, B>(v: I) -> HashMap<A, Vec<B>>
where
    I: Iterator<Item = (A, B)>,
    A: PartialEq + Eq + Hash + Clone,
{
    let mut map = HashMap::new();
    for (key, values) in v.group_by(|(k, _v)| k.clone()).into_iter() {
        for (_, value) in values {
            map.entry(key.clone())
                .or_insert_with(Vec::<B>::new)
                .push(value);
        }
    }
    map
}

pub fn group_by_into_immutable_vec<'a, I, A, B>(v: I) -> HashMap<A, Vector<B>>
where
    I: Iterator<Item = (A, B)>,
    A: PartialEq + Eq + Hash + Clone,
    B: Clone,
{
    let mut map = HashMap::new();
    for (key, values) in v.group_by(|(k, _v)| k.clone()).into_iter() {
        for (_, value) in values {
            map.entry(key.clone())
                .or_insert_with(Vector::<B>::new)
                .push_back(value);
        }
    }
    map
}
