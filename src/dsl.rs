use crate::syntax::{Expression, UnOp, RuntimeType};

// Not the expression
// e becomes !e
pub(crate) fn negate(expression: Expression) -> Expression {
    Expression::UnOp { un_op: UnOp::Negate, value: Box::new(expression), type_: RuntimeType::BoolRuntimeType }
}


pub(crate) fn negative(expression: Expression) -> Expression {
    Expression::UnOp { un_op: UnOp::Negative, value: Box::new(expression), type_: RuntimeType::BoolRuntimeType }
}