use crate::syntax::{Expression, UnOp, RuntimeType};

// Negates the expression
// e becomes !e
pub(crate) fn neg(statement: Expression) -> Expression {
    Expression::UnOp { un_op: UnOp::Negate, value: Box::new(statement), type_: RuntimeType::BoolRuntimeType }
}