use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use crate::{
    exec::AliasMap,
    fold::ExprFoldCollection,
    syntax::{Expression, Identifier, RuntimeType},
};

pub fn concretizations<'a>(
    expression: Rc<Expression>,
    symbolic_refs: &HashSet<&Identifier>,
    alias_map: &'a AliasMap,
) -> Vec<Rc<Expression>> {
    let mut replaced_expressions = Vec::new();
    let n_combinations = alias_map.iter().fold(1, |a, (_, refs)| a * refs.aliases().len());

    let mut concretizations = alias_map
        .iter()
        .filter(|(id, _)| symbolic_refs.contains(*id))
        .map(|(id, refs)| (id, refs.aliases().iter().cycle().take(n_combinations)))
        .collect::<HashMap<_, _>>();

    // let (combinations, id_to_idx) = alias_map
    // .iter()
    // .map(|(key, refs)|  (key, refs.iter().cycle().take(n_combinations)))
    // .fold((Vec::new(), HashMap::new()), |(mut refs, mut id_to_idx), (id, refs_iter)| {
    //     let idx = refs.len();
    //     refs.push(refs_iter);
    //     id_to_idx.insert(id, idx);
    //     (refs, id_to_idx)
    // });

    if concretizations.len() == 0 {
        return replaced_expressions;
    }

    loop {
        let concretization = concretizations
            .iter_mut()
            .map(|(id, refs)| refs.next().map(|ref_| (*id, ref_)))
            .collect::<Option<HashMap<_, _>>>();

        if let Some(concretization) = concretization {
            // dbg!(&concretization);
            replaced_expressions.push(helper(expression.clone(), &concretization));
        } else {
            return replaced_expressions;
        }
    }
}

fn helper(
    expression: Rc<Expression>,
    concretization: &HashMap<&Identifier, &Rc<Expression>>,
) -> Rc<Expression> {
    match expression.as_ref() {
        Expression::SymbolicRef { var, .. } => concretization[&var].clone(),
        Expression::BinOp {
            bin_op,
            lhs,
            rhs,
            type_,
        } => Rc::new(Expression::BinOp {
            bin_op: bin_op.clone(),
            lhs: helper(lhs.clone(), concretization),
            rhs: helper(rhs.clone(), concretization),
            type_: type_.clone(),
        }),
        Expression::UnOp {
            un_op,
            value,
            type_,
        } => Rc::new(Expression::UnOp {
            un_op: un_op.clone(),
            value: helper(value.clone(), concretization),
            type_: type_.clone(),
        }),

        Expression::Conditional {
            guard,
            true_,
            false_,
            type_,
        } => Rc::new(Expression::Conditional {
            guard: helper(guard.clone(), concretization),
            true_: helper(true_.clone(), concretization),
            false_: helper(false_.clone(), concretization),
            type_: type_.clone(),
        }),
        Expression::Forall {
            elem,
            range,
            domain,
            formula,
            type_,
        } => todo!(),
        Expression::Exists {
            elem,
            range,
            domain,
            formula,
            type_,
        } => todo!(),
        Expression::Var { .. }
        | Expression::SymbolicVar { .. }
        | Expression::Lit { .. }
        | Expression::SizeOf { .. }
        | Expression::Ref { .. } => expression.clone(),
    }
}

// [
//     node1: [1, 2, 3],
//     node2: [3, 4],
//     node3: [5, 6],
// ]

// [
//     node1: [1, 1, 2, 2, 3, 3]
//     node2: [3, 4, 3, 4, 3, 4]
//     node5: []
// ]

// [
//     node3: [5, 6]
// ], node2

// =>
// [
//     node2: [3, 3, 4, 4]
//     node3, [5, 6, 5, 6]
// ], node1

// [
//     node1: [1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3]
//     node2: [3, 3, 4, 4, 3, 3, 4, 4, 3, 3, 4, 4]
//     node3, [5, 6, 5, 6, 5, 6, 5, 6, 5, 6, 5, 6]
// ]

// alias_map.iter().fold(HashMap::new(), |mut a: HashMap<&Identifier, Option<Box<dyn Iterator<Item = &Expression>>>>, x| {

//     if a.len() == 0 {
//         a.insert(x.0, Some(Box::new(x.1.iter())));
//     }
//     for ref_ in x.1 {
//         for (key, refs) in  a.iter_mut() {
//             let r = refs.take().unwrap();
//             *refs = Some( Box::new(std::iter::repeat(ref_).chain(r)));

//         }
//     }

//     a
// });

// cycle all and take(<all_len_multiplied>)

// let mut iter = symbolic_refs.iter().map(|ref_| (ref_, &alias_map[ref_]));

// let mut m: HashMap<&'a String, Option<Box<dyn CloneIterator<Item=&Expression>>>> = HashMap::new();
// let mut size = 0;

// let (ref_, crefs) = iter.next().unwrap();
// m.insert(ref_, Some(Box::new(crefs.iter())));
// size = crefs.len();

// for (ref_, concrete_refs) in iter {
// let len = concrete_refs.len();

// for concrete_refs in m.values_mut() {
//     let r = concrete_refs.take().unwrap();
//     let z = r.clone_box();
//     let r = Box::new(r.chain(z));
//     // *concrete_refs = Some(r);
// }
// }

// returns the identifiers of all Expression::SymbolicRef in expression.
pub fn find_symbolic_refs<'a>(expression: &Expression) -> HashSet<&Identifier> {
    struct SymbolicRefFold;
    impl<'a> ExprFoldCollection<'a, HashSet<&'a Identifier>> for SymbolicRefFold {
        fn fold_sym_ref(var: &'a Identifier, _: &RuntimeType) -> HashSet<&'a Identifier> {
            HashSet::from_iter(std::iter::once(var))
        }
    }

    SymbolicRefFold::fold_expr(expression)
}
