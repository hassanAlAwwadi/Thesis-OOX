//! Functions and types related to the heap model of OOX.
//!
//! The heap is modelled as a map from reference -> heapvalue.
//! A reference of a heapvalue can be seen as the adress or unique identifier.
//!

use std::{rc::Rc};

use crate::exec::ImHashMap;
use crate::{Expression, Identifier, Reference, RuntimeType};
use std::collections::BTreeMap;
pub type Heap = ImHashMap<Reference, HeapValue>;

/// Get an element at index from reference in the heap.
///
/// Assumes that the reference points to an array value, panics otherwise.
pub fn get_element(index: usize, ref_: Reference, heap: &Heap) -> Rc<Expression> {
    if let HeapValue::ArrayValue { elements, .. } = &heap[&ref_] {
        return elements[index].clone();
    }
    panic!("Expected an array");
}

/// A value on the heap, either an object (mapping from fields to expression) or an array (mapping from index to expression)
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HeapValue {
    ObjectValue {
        fields: BTreeMap<Identifier, Rc<Expression>>,
        type_: RuntimeType,
    },
    ArrayValue {
        elements: Vec<Rc<Expression>>,
        type_: RuntimeType,
    },
}

impl HeapValue {}
