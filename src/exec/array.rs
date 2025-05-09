use std::rc::Rc;

use itertools::Itertools;

use crate::{
    typeable::Typeable, Expression, Identifier, NonVoidType, RuntimeType, SourcePos, SymbolTable,
};

use super::{alias_map::AliasEntry, create_symbolic_var, heap::HeapValue, Engine, State};
use crate::exec::evaluate_as_int;

/// Initialises an array by creating a concrete array of size array_size in the heap, symbolic objects are initialised lazily.
/// The resulting state has a single concrete array (or null) in its alias map.
pub(crate) fn array_initialisation(
    state: &mut State,
    array_name: &Identifier,
    array_size: u64,
    array_type: RuntimeType,
    inner_type: RuntimeType,
    st: &SymbolTable,
) {
    let r = state.next_reference_id();

    state.alias_map.insert(
        array_name.clone(),
        AliasEntry::new(vec![Rc::new(Expression::Ref {
            ref_: r,
            type_: array_type.clone(),
            info: SourcePos::UnknownPosition,
        })]),
    );

    let array_elements = (0..array_size)
        .map(|i| {
            create_symbolic_var(
                format!("{}{}", array_name, i).into(),
                inner_type.clone(),
                st,
            )
            .into()
        })
        .collect();

    state.heap.insert(
        r,
        HeapValue::ArrayValue {
            elements: array_elements,
            type_: array_type,
        },
    );

    // dbg!("after array initialization", &state.heap, &state.alias_map);
}

/// Constructs an array that was created by an OOX statement like this:
// / ```
// / int[] a = new int[10];
// / ```
/// in this example, array_type = int, sizes = { 10 }, type_ = int[].
pub(crate) fn exec_array_construction(
    state: &mut State,
    array_type: &NonVoidType,
    sizes: &[Rc<Expression>],
    type_: &RuntimeType,
    en: &mut impl Engine,
) -> Rc<Expression> {
    let ref_id = state.next_reference_id();

    assert!(sizes.len() == 1, "Support for only 1D arrays");
    // int[][] a = new int[10][10];

    let size = evaluate_as_int(state, sizes[0].clone(), en).expect_right("no symbolic array sizes");

    let array = (0..size)
        .map(|_| Rc::new(array_type.default()))
        .collect_vec();

    state.heap.insert(
        ref_id,
        HeapValue::ArrayValue {
            elements: array,
            type_: type_.clone(),
        },
    );

    Rc::new(Expression::Ref {
        ref_: ref_id,
        type_: type_.clone(),
        info: SourcePos::UnknownPosition,
    })
}
