use std::{fmt::Debug, rc::Rc};

use crate::syntax::{BinOp, Expression, Lit, RuntimeType, UnOp};

impl Debug for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn helper(expression: &Expression, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match expression {
                Expression::BinOp {
                    bin_op,
                    lhs,
                    rhs,
                    type_,
                } => {
                    let op_str = match bin_op {
                        BinOp::Implies => "==>",
                        BinOp::And => "&&",
                        BinOp::Or => "||",
                        BinOp::Equal => "==",
                        BinOp::NotEqual => "!=",
                        BinOp::LessThan => "<",
                        BinOp::LessThanEqual => "<=",
                        BinOp::GreaterThan => ">",
                        BinOp::GreaterThanEqual => ">=",
                        BinOp::Plus => "+",
                        BinOp::Minus => "-",
                        BinOp::Multiply => "*",
                        BinOp::Divide => "/",
                        BinOp::Modulo => "%",
                    };
                    // if bin_op == &BinOp::Implies {
                    //     f.write_str("(")?;
                    //     helper(lhs, f)?;
                    //     f.write_str(")")?;
                    //     f.write_str(" ")?;
                    //     f.write_str(op_str)?;
                    //     f.write_str(" ")?;

                    //     f.write_str("(")?;
                    //     helper(rhs, f)?;
                    //     f.write_str(")")?;
                    // } else {
                    helper(lhs, f)?;
                    f.write_str(" ")?;
                    f.write_str(op_str)?;
                    f.write_str(" ")?;
                    helper(rhs, f)?;
                    // }
                }
                Expression::UnOp {
                    un_op,
                    value,
                    type_,
                } => {
                    match un_op {
                        UnOp::Negative => f.write_str("-")?,
                        UnOp::Negate => f.write_str("!")?,
                    };
                    f.write_str("(")?;
                    helper(value, f)?;
                    f.write_str(")")?;
                }
                Expression::Var { var, type_ } => f.write_str(var)?,
                Expression::SymbolicVar { var, type_ } => f.write_fmt(format_args!("${}", var))?,
                Expression::Lit { lit, type_ } => match lit {
                    Lit::NullLit => f.write_str("null")?,
                    Lit::BoolLit { bool_value } => f.write_fmt(format_args!("{}", bool_value))?,
                    Lit::UIntLit { uint_value } => f.write_fmt(format_args!("{}", uint_value))?,
                    Lit::IntLit { int_value } => f.write_fmt(format_args!("{}", int_value))?,
                    Lit::FloatLit { float_value } => {
                        f.write_fmt(format_args!("{}", float_value))?
                    }
                    Lit::StringLit { string_value } => {
                        f.write_fmt(format_args!("{}", string_value))?
                    }
                    Lit::CharLit { char_value } => f.write_fmt(format_args!("{}", char_value))?,
                },
                Expression::SizeOf { var, .. } => f.write_fmt(format_args!("#{}", var))?,
                Expression::Ref { ref_, type_ } => f.write_fmt(format_args!("#{}", ref_))?,
                Expression::SymbolicRef { var, type_ } => f.write_fmt(format_args!("%{}", var))?,
                Expression::Conditional {
                    guard,
                    true_,
                    false_,
                    type_,
                } => {
                    helper(guard, f)?;
                    f.write_str(" ? ")?;

                    f.write_str("(")?;
                    helper(true_, f)?;
                    f.write_str(")")?;
                    f.write_str(" : ")?;
                    f.write_str("(")?;
                    helper(false_, f)?;
                    f.write_str(")")?;
                }
                Expression::Forall {
                    elem,
                    range,
                    domain,
                    formula,
                    ..
                } => {
                    // forall elem, index : a : elem > 0
                    f.write_fmt(format_args!("forall {}, {} : {} : ", elem, range, domain))?;
                    helper(&formula, f)?;
                },
                Expression::Exists {
                    elem,
                    range,
                    domain,
                    formula,
                    type_,
                } => {
                    // exists elem, index : a : elem > 0
                    f.write_fmt(format_args!("exists {}, {} : {} : ", elem, range, domain))?;
                    helper(&formula, f)?;
                },
            };
            Ok(())
        }

        helper(self, f)?;
        Ok(())
    }
}

#[test]
fn test() {
    let e = Expression::BinOp {
        bin_op: BinOp::Implies,
        lhs: Rc::new(Expression::Var {
            var: "x".to_owned(),
            type_: RuntimeType::ANYRuntimeType,
        }),
        rhs: Rc::new(Expression::Var {
            var: "y".to_owned(),
            type_: RuntimeType::ANYRuntimeType,
        }),
        type_: RuntimeType::ANYRuntimeType,
    };

    let s = format!("{:?}", e);
    assert_eq!(s, "x ==> y".to_string());
}
