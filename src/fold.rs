use std::collections::HashMap;

use crate::syntax::{BinOp, Expression, Identifier, Lit, Reference, RuntimeType, UnOp};

#[allow(unused_variables)]
pub trait ExprFoldCollection<'a, R>
where
    R: Default + Extend<<R as IntoIterator>::Item> + IntoIterator,
    <R as IntoIterator>::Item: 'a,
{
    fn fold_binop(
        bin_op: &'a BinOp,
        lhs: &'a Box<Expression>,
        rhs: &'a Box<Expression>,
        type_: &'a RuntimeType,
    ) -> R {
        let mut r = Self::fold_expr(lhs);
        r.extend(Self::fold_expr(rhs).into_iter());
        r
    }

    fn fold_unop(un_op: &'a UnOp, value: &'a Box<Expression>, type_: &'a RuntimeType) -> R {
        Self::fold_expr(value)
    }

    fn fold_var(var: &'a Identifier, type_: &'a RuntimeType) -> R {
        R::default()
    }

    fn fold_sym_var(var: &'a Identifier, type_: &'a RuntimeType) -> R {
        R::default()
    }

    fn fold_lit(lit: &'a Lit, type_: &'a RuntimeType) -> R {
        R::default()
    }

    fn fold_size_of(var: &'a Identifier, type_: &'a RuntimeType) -> R {
        R::default()
    }

    fn fold_ref(ref_: &'a Reference, type_: &'a RuntimeType) -> R {
        R::default()
    }

    fn fold_sym_ref(var: &'a Identifier, type_: &'a RuntimeType) -> R {
        R::default()
    }

    fn fold_cond(
        guard: &'a Box<Expression>,
        true_: &'a Box<Expression>,
        false_: &'a Box<Expression>,
        type_: &'a RuntimeType,
    ) -> R {
        let mut r = Self::fold_expr(guard);
        r.extend(Self::fold_expr(true_));
        r.extend(Self::fold_expr(false_));
        r
    }

    fn fold_expr(e: &'a Expression) -> R {
        match e {
            Expression::Forall {
                elem,
                range,
                domain,
                formula,
                type_,
            } => R::default(),
            Expression::Exists {
                elem,
                range,
                domain,
                formula,
                type_,
            } => R::default(),
            Expression::BinOp {
                bin_op,
                lhs,
                rhs,
                type_,
            } => Self::fold_binop(bin_op, lhs, rhs, type_),
            Expression::UnOp {
                un_op,
                value,
                type_,
            } => Self::fold_unop(un_op, value, type_),
            Expression::Var { var, type_ } => Self::fold_var(var, type_),
            Expression::SymbolicVar { var, type_ } => Self::fold_sym_var(var, type_),
            Expression::Lit { lit, type_ } => Self::fold_lit(lit, type_),
            Expression::SizeOf { var, type_ } => Self::fold_size_of(var, type_),
            Expression::Ref { ref_, type_ } => Self::fold_ref(ref_, type_),
            Expression::SymbolicRef { var, type_ } => Self::fold_sym_ref(var, type_),
            Expression::Conditional {
                guard,
                true_,
                false_,
                type_,
            } => Self::fold_cond(guard, true_, false_, type_),
        }
    }
}
