use std::rc::Rc;

use crate::syntax::{BinOp, Expression, RuntimeType, UnOp};

// Not the expression
// e becomes !e
pub(crate) fn negate(expression: Rc<Expression>) -> Expression {
    Expression::UnOp {
        un_op: UnOp::Negate,
        value: expression,
        type_: RuntimeType::BoolRuntimeType,
    }
}

pub(crate) fn negative(expression: Rc<Expression>) -> Expression {
    Expression::UnOp {
        un_op: UnOp::Negative,
        value: expression,
        type_: RuntimeType::BoolRuntimeType,
    }
}

pub(crate) fn ite(guard: Rc<Expression>, e1: Rc<Expression>, e2: Rc<Expression>) -> Expression {
    Expression::Conditional {
        guard: guard,
        true_: e1,
        false_: e2,
        type_: RuntimeType::ANYRuntimeType,
    }
}

pub(crate) fn equal<E1, E2>(e1: E1, e2: E2) -> Expression
where
    E1: Into<Rc<Expression>>,
    E2: Into<Rc<Expression>>
{
    Expression::BinOp {
        bin_op: BinOp::Equal,
        lhs: e1.into(),
        rhs: e2.into(),
        type_: RuntimeType::ANYRuntimeType,
    }
}


pub(crate) fn ors<I>(iter: I) -> Expression
where I: IntoIterator<Item=Expression>,{
    iter.into_iter().fold(Expression::FALSE, |acc, expr | {
        Expression::BinOp { bin_op: BinOp::Or, lhs: Rc::new(acc), rhs: expr.into(), type_: RuntimeType::BoolRuntimeType }
    })
}