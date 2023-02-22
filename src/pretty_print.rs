use std::{
    fmt::{Debug, Display},
    rc::Rc,
};

use crate::{
    syntax::{
        BinOp, Expression, Invocation, Lhs, Lit, NonVoidType, Rhs, RuntimeType, Statement, UnOp,
    },
    typeable::Typeable,
};

impl Debug for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn helper(expression: &Expression, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match expression {
                Expression::BinOp {
                    bin_op,
                    lhs,
                    rhs,
                    type_,
                    info
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
                    //     write!(f,"(")?;
                    //     helper(lhs, f)?;
                    //     write!(f,")")?;
                    //     write!(f," ")?;
                    //     write!(f,op_str)?;
                    //     write!(f," ")?;

                    //     write!(f,"(")?;
                    //     helper(rhs, f)?;
                    //     write!(f,")")?;
                    // } else {
                    helper(lhs, f)?;
                    write!(f, " ")?;
                    write!(f, "{}", op_str)?;
                    write!(f, " ")?;
                    helper(rhs, f)?;
                    // }
                }
                Expression::UnOp {
                    un_op,
                    value,
                    type_,
                    info
                } => {
                    match un_op {
                        UnOp::Negative => write!(f, "-")?,
                        UnOp::Negate => write!(f, "!")?,
                    };
                    write!(f, "(")?;
                    helper(value, f)?;
                    write!(f, ")")?;
                }
                Expression::Var { var, type_, info } => write!(f, "{}", var)?,
                Expression::SymbolicVar { var, type_, info } => write!(f, "${}", var)?,
                Expression::Lit { lit, type_, info } => match lit {
                    Lit::NullLit => write!(f, "null")?,
                    Lit::BoolLit { bool_value } => write!(f, "{}", bool_value)?,
                    Lit::UIntLit { uint_value } => write!(f, "{}", uint_value)?,
                    Lit::IntLit { int_value } => write!(f, "{}", int_value)?,
                    Lit::FloatLit { float_value } => write!(f, "{}", float_value)?,
                    Lit::StringLit { string_value } => write!(f, "{}", string_value)?,
                    Lit::CharLit { char_value } => write!(f, "{}", char_value)?,
                },
                Expression::SizeOf { var, .. } => write!(f, "#{}", var)?,
                Expression::Ref { ref_, type_, info } => write!(f, "#{}", ref_)?,
                Expression::SymbolicRef { var, type_, info } => write!(f, "%{}", var)?,
                Expression::Conditional {
                    guard,
                    true_,
                    false_,
                    type_,
                    info
                } => {
                    helper(guard, f)?;
                    write!(f, " ? ")?;

                    write!(f, "(")?;
                    helper(true_, f)?;
                    write!(f, ")")?;
                    write!(f, " : ")?;
                    write!(f, "(")?;
                    helper(false_, f)?;
                    write!(f, ")")?;
                }
                Expression::Forall {
                    elem,
                    range,
                    domain,
                    formula,
                    ..
                } => {
                    // forall elem, index : a : elem > 0
                    write!(f, "forall {}, {} : {} : ", elem, range, domain)?;
                    helper(&formula, f)?;
                }
                Expression::Exists {
                    elem,
                    range,
                    domain,
                    formula,
                    type_,
                    info
                } => {
                    // exists elem, index : a : elem > 0
                    write!(f, "exists {}, {} : {} : ", elem, range, domain)?;
                    helper(&formula, f)?;
                }
            };
            Ok(())
        }

        helper(self, f)?;
        Ok(())
    }
}

// impl Debug for Statement {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match self {
//             Self::Declare { type_, var } => {
//                 write!(f, "{} {};", type_.type_of(), var)
//             }
//             Self::Assign { lhs, rhs } => write!(f, "{} := {};", lhs, rhs),
//             Self::Call { invocation } => write!(f, "{};", invocation),
//             Self::Skip => write!(f, ";"),
//             Self::Assert { assertion } => {
//                 write!(f, "assert {:?};", assertion)
//             }
//             Self::Assume { assumption } => write!(f, "assume {:?};", assumption),
//             Self::While { guard, body } => write!(f, "while {:?} {{ .. }}", guard),
//             Self::Ite {
//                 guard,
//                 true_body,
//                 false_body,
//             } => write!(
//                 f,
//                 "if ({:?}) {{ \n {:?} \n }} else {{ \n {:?} \n }}",
//                 guard, true_body, false_body
//             ),
//             Self::Continue => write!(f, "continue;"),
//             Self::Break => write!(f, "break;"),
//             Self::Return { expression } => {
//                 write!(f, "return")?;
//                 if let Some(expression) = expression {
//                     write!(f, " {:?}", expression)?;
//                 }
//                 write!(f, ";")
//             }
//             Self::Throw { message } => write!(f, "throw {};", message),
//             Self::Try {
//                 try_body,
//                 catch_body,
//             } => write!(f, "try {{ .. }} catch {{ .. }}"),
//             Self::Block { body } => write!(f, "{{ .. }}"),
//             Self::Seq { stat1, stat2 } => {
//                 writeln!(f, "{:?}", stat1)?;
//                 writeln!(f, "{:?}", stat2)
//             }
//         }
//     }
// }

impl Display for RuntimeType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RuntimeType::UnknownRuntimeType => write!(f, "unknown"),
            RuntimeType::VoidRuntimeType => write!(f, "void"),
            RuntimeType::UIntRuntimeType => write!(f, "unsigned int"),
            RuntimeType::IntRuntimeType => write!(f, "int"),
            RuntimeType::FloatRuntimeType => write!(f, "float"),
            RuntimeType::BoolRuntimeType => write!(f, "bool"),
            RuntimeType::StringRuntimeType => write!(f, "string"),
            RuntimeType::CharRuntimeType => write!(f, "char"),
            RuntimeType::ReferenceRuntimeType { type_ } => write!(f, "{}", type_),
            RuntimeType::ArrayRuntimeType { inner_type } => {
                write!(f, "{}[]", inner_type)
            }
            RuntimeType::ANYRuntimeType => write!(f, "any"),
            RuntimeType::NUMRuntimeType => write!(f, "NUM"),
            RuntimeType::REFRuntimeType => write!(f, "REF"),
            RuntimeType::ARRAYRuntimeType => write!(f, "ARRAY"),
        }
    }
}

impl Display for Lhs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Lhs::LhsVar { var, type_, .. } => write!(f, "{}: {}", var, type_),
            Lhs::LhsField {
                var,
                var_type,
                field,
                type_,
                ..
            } => write!(f, "{}.{}: {}.{}", var, field, var_type, type_),
            Lhs::LhsElem { var, index, type_ , ..} => {
                write!(f, "{}[{:?}]: {}", var, index, type_)
            }
        }
    }
}

impl Display for Rhs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rhs::RhsExpression { value, type_, .. } => {
                write!(f, "({:?}: {})", value, type_)
            }
            Rhs::RhsField { var, field, type_, .. } => {
                write!(f, "{:?}.{} : {}", var, field, type_)
            }
            Rhs::RhsElem { var, index, type_, .. } => {
                write!(f, "{:?}[{:?}]: {}", var, index, type_)
            }
            Rhs::RhsCall { invocation, type_, 
                .. } => {
                write!(f, "{}: {}", invocation, type_)
            }
            Rhs::RhsArray {
                array_type,
                sizes,
                type_,
                ..
            } => {
                write!(f, "new {}", array_type.type_of())?;
                for size in sizes {
                    write!(f, "[{:?}]", size)?;
                }
                Ok(())
            }
        }
    }
}

impl Display for Invocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvokeMethod {
                lhs,
                rhs,
                arguments,
                ..
            } => {
                write!(f, "{}.{}(", lhs, rhs)?;
                for arg in arguments {
                    write!(f, "{:?}", arg)?;
                    write!(f, ", ")?;
                }
                write!(f, ")")
            }
            Self::InvokeSuperMethod { arguments, rhs, .. } => {
                write!(f, "super.{}(", rhs)?;
                for arg in arguments {
                    write!(f, "{:?}", arg)?;
                    write!(f, ", ")?;
                }
                write!(f, ")")
            }
            Self::InvokeConstructor {
                class_name,
                arguments,
                ..
            } => {
                write!(f, "new {}", class_name)?;
                write!(f, "(")?;
                for arg in arguments {
                    write!(f, "{:?}", arg)?;
                    write!(f, ", ")?;
                }
                write!(f, ")")
            }
            Self::InvokeSuperConstructor {
                arguments,
                resolved,
                ..
            } => {
                write!(f, "super(")?;
                for arg in arguments {
                    write!(f, "{:?}", arg)?;
                    write!(f, ", ")?;
                }
                write!(f, ")")
            }
        }
    }
}

#[test]
fn test() {
    let e = Expression::BinOp {
        bin_op: BinOp::Implies,
        lhs: Rc::new(Expression::Var {
            var: "x".into(),
            type_: RuntimeType::ANYRuntimeType,
            info: crate::positioned::SourcePos::UnknownPosition
        }),
        rhs: Rc::new(Expression::Var {
            var: "y".into(),
            type_: RuntimeType::ANYRuntimeType,
            info: crate::positioned::SourcePos::UnknownPosition
        }),
        type_: RuntimeType::ANYRuntimeType,
        info: crate::positioned::SourcePos::UnknownPosition
    };

    let s = format!("{:?}", e);
    assert_eq!(s, "x ==> y".to_string());
}
