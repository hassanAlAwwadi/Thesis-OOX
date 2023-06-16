use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use crate::{
    exec::alias_map::AliasMap,
    fold::ExprFoldCollection,
    syntax::{Expression, Identifier, RuntimeType},
};

/// Iterator over all concretizations of the expression
/// I is assumed to be equally as long for all symbolic objects in field concretizations.
pub struct ConcretizationIterator<I>
where
    I: Iterator<Item = Rc<Expression>>,
{
    concretizations: HashMap<Identifier, I>,
    expression: Rc<Expression>,
    length: usize,
}

impl<I: Iterator<Item = Rc<Expression>>> Iterator for ConcretizationIterator<I> {
    type Item = Rc<Expression>;

    fn next(&mut self) -> Option<Self::Item> {
        let concretization = self
            .concretizations
            .iter_mut()
            .map(|(id, refs)| refs.next().map(|ref_| (id, ref_)))
            .collect::<Option<HashMap<_, _>>>();

        if let Some(concretization) = concretization {
            Some(helper(self.expression.clone(), &concretization))
        } else {
            None
        }
    }
}

impl<I: Iterator<Item = Rc<Expression>>> ExactSizeIterator for ConcretizationIterator<I> {
    fn len(&self) -> usize {
        self.length
    }
}

pub fn concretizations<'a>(
    expression: Rc<Expression>,
    symbolic_refs: &HashSet<&Identifier>,
    alias_map: AliasMap,
) -> impl ExactSizeIterator<Item = Rc<Expression>> + 'a {
    let n_combinations = alias_map
        .iter()
        .fold(1, |a, (_, refs)| a * refs.aliases().len());

    let concretizations = alias_map
        .into_iter()
        .filter(|(id, _)| symbolic_refs.contains(id))
        .map(|(id, refs)| (id, refs.aliases.into_iter().cycle().take(n_combinations)))
        .collect::<HashMap<_, _>>();

    ConcretizationIterator {
        concretizations,
        expression,
        length: n_combinations,
    }
}

/// Replaces variables with their concretization in the expression.
fn helper(
    expression: Rc<Expression>,
    concretization: &HashMap<&Identifier, Rc<Expression>>,
) -> Rc<Expression> {
    match expression.as_ref() {
        Expression::SymbolicRef { var, .. } => concretization[&var].clone(),
        Expression::BinOp {
            bin_op,
            lhs,
            rhs,
            type_,
            info,
        } => Rc::new(Expression::BinOp {
            bin_op: *bin_op,
            lhs: helper(lhs.clone(), concretization),
            rhs: helper(rhs.clone(), concretization),
            type_: type_.clone(),
            info: *info,
        }),
        Expression::UnOp {
            un_op,
            value,
            type_,
            info,
        } => Rc::new(Expression::UnOp {
            un_op: un_op.clone(),
            value: helper(value.clone(), concretization),
            type_: type_.clone(),
            info: *info,
        }),

        Expression::Conditional {
            guard,
            true_,
            false_,
            type_,
            info,
        } => Rc::new(Expression::Conditional {
            guard: helper(guard.clone(), concretization),
            true_: helper(true_.clone(), concretization),
            false_: helper(false_.clone(), concretization),
            type_: type_.clone(),
            info: *info,
        }),
        Expression::Forall { .. } => {
            unreachable!("Unexpected forall in concretization expression.")
        }
        Expression::Exists { .. } => {
            unreachable!("Unexpected forall in concretization expression.")
        }
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

//     if a.is_empty() {
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
pub fn find_symbolic_refs(expression: &Expression) -> HashSet<&Identifier> {
    struct SymbolicRefFold;
    impl<'a> ExprFoldCollection<'a, HashSet<&'a Identifier>> for SymbolicRefFold {
        fn fold_sym_ref(var: &'a Identifier, _: &RuntimeType) -> HashSet<&'a Identifier> {
            HashSet::from_iter(std::iter::once(var))
        }
    }

    SymbolicRefFold::fold_expr(expression)
}
