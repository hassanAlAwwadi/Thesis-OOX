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

pub(crate) fn equal(e1: Rc<Expression>, e2: Rc<Expression>) -> Expression {
    Expression::BinOp {
        bin_op: BinOp::Equal,
        lhs: e1,
        rhs: e2,
        type_: RuntimeType::ANYRuntimeType,
    }
}
