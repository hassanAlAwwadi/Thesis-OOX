/// This file contains functions that makes writing expressions more compact
/// It can be used to reduce boilerplate code.
use std::rc::Rc;

use crate::syntax::{BinOp, Expression, Lit, RuntimeType, UnOp, Identifier};

/// Not the expression.
/// e becomes !e
pub(crate) fn negate(expression: Rc<Expression>) -> Expression {
    Expression::UnOp {
        un_op: UnOp::Negate,
        value: expression,
        type_: RuntimeType::BoolRuntimeType,
    }
}

/// e becomes -e
pub(crate) fn negative(expression: Rc<Expression>) -> Expression {
    Expression::UnOp {
        un_op: UnOp::Negative,
        value: expression,
        type_: RuntimeType::BoolRuntimeType,
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
    }
}

fn bin_op<E1, E2>(e1: E1, e2: E2, bin_op: BinOp) -> Expression
where
    E1: Into<Rc<Expression>>,
    E2: Into<Rc<Expression>>,
{
    Expression::BinOp {
        bin_op,
        lhs: e1.into(),
        rhs: e2.into(),
        type_: RuntimeType::ANYRuntimeType,
    }
}
pub(crate) fn equal<E1, E2>(e1: E1, e2: E2) -> Expression
where
    E1: Into<Rc<Expression>>,
    E2: Into<Rc<Expression>>,
{
    bin_op(e1, e2, BinOp::Equal)
}

pub(crate) fn greater_than_equal<E1, E2>(e1: E1, e2: E2) -> Expression
where
    E1: Into<Rc<Expression>>,
    E2: Into<Rc<Expression>>,
{
    bin_op(e1, e2, BinOp::GreaterThanEqual)
}

pub(crate) fn less_than<E1, E2>(e1: E1, e2: E2) -> Expression
where
    E1: Into<Rc<Expression>>,
    E2: Into<Rc<Expression>>,
{
    bin_op(e1, e2, BinOp::LessThan)
}


pub(crate) fn size_of(var: Identifier) -> Expression {
    Expression::SizeOf { var, type_: RuntimeType::IntRuntimeType }
}


/// Turns an iterator of Expressions into an OR expression, with a false added to the front.
/// For example:
/// ```
/// # use lib::{syntax::Expression, dsl};
/// let expressions = [Expression::TRUE, Expression::FALSE, Expression::TRUE];
///
/// assert_eq!(
///     format!("{:?}", dsl::ors(expressions)),
///     "false || true || false || true"
/// )
/// ```
pub fn ors<I>(iter: I) -> Expression
where
    I: IntoIterator<Item = Expression>,
{
    iter.into_iter()
        .fold(Expression::FALSE, |acc, expr| Expression::BinOp {
            bin_op: BinOp::Or,
            lhs: Rc::new(acc),
            rhs: expr.into(),
            type_: RuntimeType::BoolRuntimeType,
        })
}

pub(crate) fn toIntExpr(int_value: i64) -> Expression {
    Expression::Lit {
        lit: Lit::IntLit { int_value },
        type_: RuntimeType::IntRuntimeType,
    }
}
