//!
//! 
//! Original OOX deals with symbolic references in Z3 expressions as follows:
//! Find all concrete references (aliasMap) for each of the symbolic references 
//! create for each combination of these an expression with their concrete references
//! this results in multiple expressions that need to be solved
//! 
//! Concretization example
//! Given the following two symbolic objects and their aliases
//!  _node = [null, ref(1)] 
//!  _next1 = [null, ref(1), ref(2)]
//!  
//!  And given the expression
//!  _node == _next1
//!  
//!  There are len(_node) * len(_next1) number of unique concretizations that will be solved by Z3:
//!  
//!  null == null
//!  null == ref(1)
//!  null == ref(2)
//!  ref(1) == null
//!  ref(1) == ref(1)
//!  ref(1) == ref(2)

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
