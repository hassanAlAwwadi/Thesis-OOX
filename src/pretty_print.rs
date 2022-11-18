use std::fmt::Debug;

use crate::syntax::{Expression, UnOp, Lit, BinOp, RuntimeType};


impl Debug for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {

        fn helper(expression: &Expression, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match expression {
                Expression::BinOp { bin_op, lhs, rhs, type_ } => {
                    helper(lhs, f)?;
                    f.write_str(" ")?;
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
                    f.write_str(op_str)?;
                    f.write_str(" ")?;
                    helper(rhs, f)?;
                },
                Expression::UnOp { un_op, value, type_ } => {
                    match un_op {
                        UnOp::Negative => f.write_str("-")?,
                        UnOp::Negate => f.write_str("!")?,
                    };
                    f.write_str("(")?;
                    helper(value, f)?;
                    f.write_str(")")?;
                },
                Expression::Var { var, type_ } => {
                    f.write_str(var)?
                },
                Expression::SymbolicVar { var, type_ } => {
                    f.write_fmt(format_args!("${}", var))?
                },
                Expression::Lit { lit, type_ } => {
                    match lit {
                        Lit::NullLit => f.write_str("null")?,
                        Lit::BoolLit { bool_value } => f.write_fmt(format_args!("{}", bool_value))?,
                        Lit::UIntLit { uint_value } => f.write_fmt(format_args!("{}", uint_value))?,
                        Lit::IntLit { int_value } => f.write_fmt(format_args!("{}", int_value))?,
                        Lit::FloatLit { float_value } => f.write_fmt(format_args!("{}", float_value))?,
                        Lit::StringLit { string_value } => f.write_fmt(format_args!("{}", string_value))?,
                        Lit::CharLit { char_value } => f.write_fmt(format_args!("{}", char_value))?,
                    }
                },
                Expression::SizeOf { var, type_ } => todo!(),
                Expression::Ref { ref_, type_ } => todo!(),
                Expression::SymbolicRef { var, type_ } => todo!(),
                Expression::Conditional { guard, true_, false_, type_ } => todo!(),
                Expression::Forall { elem, range, domain, formula, type_ } => todo!(),
                Expression::Exists { elem, range, domain, formula, type_ } => todo!(),
            };
            Ok(())
        }

        helper(self, f)?;
        Ok(())
    }
}


#[test]
fn test() {
    let e = Expression::BinOp { bin_op: BinOp::Implies, lhs: 
        Box::new(Expression::Var { var: "x".to_owned(), type_: RuntimeType::ANYRuntimeType }), 
        rhs: Box::new(Expression::Var { var: "y".to_owned(), type_: RuntimeType::ANYRuntimeType }), type_: RuntimeType::ANYRuntimeType };

    let s = format!("{:?}", e);
    assert_eq!(s, "x ==> y".to_string());
}