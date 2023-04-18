/// This file contains functions that makes writing expressions more compact
/// It can be used to reduce boilerplate code.
use std::rc::Rc;

use crate::{
    positioned::SourcePos,
    syntax::{BinOp, Expression, Identifier, Lit, RuntimeType, UnOp},
};

/// Not the expression.
/// e becomes !e
pub(crate) fn negate(expression: Rc<Expression>) -> Expression {
    Expression::UnOp {
        un_op: UnOp::Negate,
        value: expression,
        type_: RuntimeType::BoolRuntimeType,
        info: SourcePos::UnknownPosition,
    }
}

/// e becomes -e
pub(crate) fn negative(expression: Rc<Expression>) -> Expression {
    Expression::UnOp {
        un_op: UnOp::Negative,
        value: expression,
        type_: RuntimeType::BoolRuntimeType,
        info: SourcePos::UnknownPosition,
    }
}

/// Creates an if guard then e1 else e2 conditional expression.
pub(crate) fn ite<E1, E2, E3>(guard: E1, e1: E2, e2: E3) -> Expression
where
    E1: Into<Rc<Expression>>,
    E2: Into<Rc<Expression>>,
    E3: Into<Rc<Expression>>,
{
    Expression::Conditional {
        guard: guard.into(),
        true_: e1.into(),
        false_: e2.into(),
        type_: RuntimeType::ANYRuntimeType,
        info: SourcePos::UnknownPosition,
    }
}

fn bin_op<E1, E2>(e1: E1, e2: E2, bin_op: BinOp, type_: RuntimeType) ->  Rc<Expression>
where
    E1: Into<Rc<Expression>>,
    E2: Into<Rc<Expression>>,
{
    Rc::new(Expression::BinOp {
            bin_op,
            lhs: e1.into(),
            rhs: e2.into(),
            type_,
            info: SourcePos::UnknownPosition,
        })
}
pub(crate) fn equal<E1, E2>(e1: E1, e2: E2) -> Rc<Expression>
where
    E1: Into<Rc<Expression>>,
    E2: Into<Rc<Expression>>,
{
    bin_op(e1, e2, BinOp::Equal, RuntimeType::BoolRuntimeType)
}

pub(crate) fn greater_than_equal<E1, E2>(e1: E1, e2: E2) -> Rc<Expression>
where
    E1: Into<Rc<Expression>>,
    E2: Into<Rc<Expression>>,
{
    bin_op(
        e1,
        e2,
        BinOp::GreaterThanEqual,
        RuntimeType::BoolRuntimeType,
    )
}

pub(crate) fn less_than<E1, E2>(e1: E1, e2: E2) -> Rc<Expression>
where
    E1: Into<Rc<Expression>>,
    E2: Into<Rc<Expression>>,
{
    bin_op(e1, e2, BinOp::LessThan, RuntimeType::BoolRuntimeType)
}

pub(crate) fn or<E1, E2>(e1: E1, e2: E2) -> Rc<Expression>
where
    E1: Into<Rc<Expression>>,
    E2: Into<Rc<Expression>>,
{
    bin_op(e1, e2, BinOp::Or, RuntimeType::BoolRuntimeType)
}

pub(crate) fn and<E1, E2>(e1: E1, e2: E2) -> Rc<Expression>
where
    E1: Into<Rc<Expression>>,
    E2: Into<Rc<Expression>>,
{
    bin_op(e1, e2, BinOp::And, RuntimeType::BoolRuntimeType)
}

pub(crate) fn size_of(var: Identifier) -> Expression {
    Expression::SizeOf {
        var,
        type_: RuntimeType::IntRuntimeType,
        info: SourcePos::UnknownPosition,
    }
}

/// Turns an iterator of Expressions into an OR expression, with a false added to the front.
/// returns False if the iterator is empty
/// For example:
/// ```
/// # use lib::{syntax::Expression, dsl};
/// let expressions = [Expression::TRUE, Expression::FALSE, Expression::TRUE];
///
/// assert_eq!(
///     format!("{:?}", dsl::ors(expressions)),
///     "true || false || true"
/// )
/// ```
pub fn ors<I, E>(iter: I) -> Rc<Expression>
where
    I: IntoIterator<Item = E>,
    E: Into<Rc<Expression>>,
{
    let mut it = iter.into_iter();
    if let Some(first) = it.next() {
        it.fold(first.into(), or)
    } else {
        Rc::new(Expression::FALSE)
    }
}

/// Turns an iterator of Expressions into an AND expression, with a true added to the front.
/// For example:
/// ```
/// # use lib::{syntax::Expression, dsl};
/// let expressions = [Expression::TRUE, Expression::FALSE, Expression::TRUE];
///
/// assert_eq!(
///     format!("{:?}", dsl::ands(expressions)),
///     "true && true && false && true"
/// )
/// ```
pub fn ands<I, E>(iter: I) -> Rc<Expression>
where
    I: IntoIterator<Item = E>,
    E: Into<Rc<Expression>>,
{
    iter.into_iter().fold(Expression::TRUE.into(), and)
}

pub(crate) fn to_int_expr(int_value: i64) -> Expression {
    Expression::Lit {
        lit: Lit::IntLit { int_value },
        type_: RuntimeType::IntRuntimeType,
        info: SourcePos::UnknownPosition,
    }
}
