// simplify the expression


use std::collections::HashMap;

use crate::{
    dsl::{negate, negative},
    exec::{init_symbolic_reference, AliasMap, Heap},
    stack::StackFrame,
    symbolic_table::SymbolicTable,
    syntax::{BinOp, Expression, Lit, RuntimeType, UnOp},
};

pub fn evaluate(
    heap: &mut Heap,
    stack: &Vec<StackFrame>,
    alias_map: &mut AliasMap,
    expression: &Expression,
    ref_counter: &mut i64,
    st: &SymbolicTable,
) -> Expression {
    // if substitute
    
    // let expression = substitute(heap, stack, alias_map, expression, ref_counter, st);


    // dbg!(expression);
    let expression = eval_locally(heap, stack, alias_map, expression, ref_counter, st);
    // dbg!(&expression);
    return expression;
}

fn substitute(
    heap: &mut Heap,
    stack: &Vec<StackFrame>,
    alias_map: &mut AliasMap,
    expression: &Expression,
    ref_counter: &mut i64,
    st: &SymbolicTable,
) -> Expression {
    match expression {
        Expression::BinOp {
            bin_op,
            lhs,
            rhs,
            type_,
        } => {
            let lhs = Box::new(substitute(heap, stack, alias_map, lhs, ref_counter, st));
            let rhs = Box::new(substitute(heap, stack, alias_map, rhs, ref_counter, st));
            return Expression::BinOp {
                bin_op: bin_op.clone(),
                lhs,
                rhs,
                type_: type_.clone(),
            };
        }
        Expression::UnOp {
            un_op,
            value,
            type_,
        } => {
            let value = Box::new(substitute(heap, stack, alias_map, value, ref_counter, st));
            Expression::UnOp {
                un_op: un_op.clone(),
                value,
                type_: type_.clone(),
            }
        }
        Expression::Var { var, type_ } => {
            let StackFrame { pc, t, params, .. } = stack.last().unwrap();
            let o = params
                .get(var)
                .unwrap_or_else(|| panic!("infeasible, object does not exit"));

            match o {
                value @ Expression::SymbolicRef { var, type_ } => {
                    let value = match alias_map.get(var) {
                        None => value.clone(),
                        Some(aliases) => {
                            if aliases.len() == 1 {
                                aliases[0].clone()
                            } else {
                                value.clone()
                            }
                        }
                    };

                    init_symbolic_reference(heap, alias_map, var, type_, ref_counter, st);

                    value.clone()
                }
                value => substitute(heap, stack, alias_map, value, ref_counter, st),
            }
        }
        sv @ Expression::SymbolicVar { .. } => sv.clone(),
        lit @ Expression::Lit { .. } => lit.clone(),
        Expression::SizeOf { var, type_ } => {
            todo!()
        }
        ref_ @ Expression::Ref { .. } => ref_.clone(),
        Expression::SymbolicRef { var, type_ } => {
            init_symbolic_reference(heap, alias_map, var, type_, ref_counter, st);

            Expression::SymbolicRef {
                var: var.clone(),
                type_: type_.clone(),
            }
        }
        Expression::Conditional {
            guard,
            true_,
            false_,
            type_,
        } => {
            let guard = Box::new(substitute(heap, stack, alias_map, guard, ref_counter, st));
            let false_ = Box::new(substitute(heap, stack, alias_map, false_, ref_counter, st));
            let true_ = Box::new(substitute(heap, stack, alias_map, true_, ref_counter, st));
            Expression::Conditional {
                guard,
                true_,
                false_,
                type_: type_.clone(),
            }
        }
        Expression::Forall {
            elem,
            range,
            domain,
            formula,
            type_,
        } => todo!(),
        Expression::Exists {
            elem,
            range,
            domain,
            formula,
            type_,
        } => todo!(),
    }
}

fn eval_locally(
    heap: &mut Heap,
    stack: &Vec<StackFrame>,
    alias_map: &mut AliasMap,
    expression: &Expression,
    ref_counter: &mut i64,
    st: &SymbolicTable,
) -> Expression {
    match expression {
        Expression::BinOp {
            bin_op,
            lhs,
            rhs,
            type_,
        } => {
            let lhs = eval_locally(heap, stack, alias_map, lhs, ref_counter, st);
            let rhs = eval_locally(heap, stack, alias_map, rhs, ref_counter, st);
            evaluate_binop(bin_op.clone(), &lhs, &rhs)
        }
        Expression::UnOp {
            un_op,
            value,
            type_,
        } => {

            let value = eval_locally(heap, stack, alias_map, value, ref_counter, st);
            evaluate_unop(un_op.clone(), value)

        }
        Expression::Var { var, type_ } => {
            let StackFrame { pc, t, params, .. } = stack.last().unwrap();
            let o = params
                .get(var)
                .unwrap_or_else(|| panic!("infeasible, object does not exit"));
            let exp = eval_locally(heap, stack, alias_map, o, ref_counter, st);

            exp.clone()

            // Not sure about this part below, shouldn't it be included?
            // In case the aliases are not initialilzed?
            
            // match &exp {
            //     value @ Expression::SymbolicRef { var, type_ } => {
            //         let value = match alias_map.get(var) {
            //             None => value.clone(),
            //             Some(aliases) => {
            //                 if aliases.len() == 1 {
            //                     aliases[0].clone()
            //                 } else {
            //                     value.clone()
            //                 }
            //             }
            //         };

            //         init_symbolic_reference(heap, alias_map, var, type_, ref_counter, st);

            //         value.clone()
            //     }
            //     value => substitute(heap, stack, alias_map, value, ref_counter, st),
            // }
        }
        sv @ Expression::SymbolicVar { .. } => sv.clone(),
        lit @ Expression::Lit { .. } => lit.clone(),
        Expression::SizeOf { var, type_ } => {
            todo!()
        }
        ref_ @ Expression::Ref { .. } => ref_.clone(),
        Expression::SymbolicRef { var, type_ } => {
            init_symbolic_reference(heap, alias_map, var, type_, ref_counter, st);

            Expression::SymbolicRef {
                var: var.clone(),
                type_: type_.clone(),
            }
        }
        Expression::Conditional {
            guard,
            true_,
            false_,
            type_,
        } => {
            let guard = eval_locally(heap, stack, alias_map, guard, ref_counter, st);
            let false_ = eval_locally(heap, stack, alias_map, false_, ref_counter, st);
            let true_ = eval_locally(heap, stack, alias_map, true_, ref_counter, st);

            match guard {
                Expression::Lit {
                    lit: Lit::BoolLit { bool_value: true },
                    ..
                } => true_,

                Expression::Lit {
                    lit: Lit::BoolLit { bool_value: false },
                    ..
                } => false_,
                _ => Expression::Conditional {
                    guard: Box::new(guard),
                    true_: Box::new(true_),
                    false_: Box::new(false_),
                    type_: type_.clone(),
                },
            }
        }
        Expression::Forall {
            elem,
            range,
            domain,
            formula,
            type_,
        } => todo!(),
        Expression::Exists {
            elem,
            range,
            domain,
            formula,
            type_,
        } => todo!(),
    }
}

fn evaluate_binop(bin_op: BinOp, lhs: &Expression, rhs: &Expression) -> Expression {
    use crate::syntax::BinOp::*;
    use crate::syntax::Lit::*;
    use Expression::*;

    // dbg!(&bin_op, lhs, rhs);

    match (bin_op, lhs, rhs) {
        // Boolean evaluation
        (
            bin_op,
            Lit {
                lit: BoolLit { bool_value: a },
                ..
            },
            Lit {
                lit: BoolLit { bool_value: b },
                ..
            },
        ) => match bin_op {
            Implies => Expression::bool(!a || *b),
            And => Expression::bool(*a && *b),
            Or => Expression::bool(*a || *b),
            Equal => Expression::bool(*a == *b),
            NotEqual => Expression::bool(*a != *b),
            _ => panic!("unsupported boolean operator"),
        },
        (
            bin_op,
            Lit {
                lit: BoolLit { bool_value: a },
                ..
            },
            exp2,
        ) => match bin_op {
            Implies => {
                if *a {
                    rhs.clone()
                } else {
                    Expression::TRUE
                }
            }
            And => {
                if *a {
                    rhs.clone()
                } else {
                    Expression::FALSE
                }
            }
            Or => {
                if *a {
                    Expression::TRUE
                } else {
                    exp2.clone()
                }
            }
            _ => Expression::BinOp {
                bin_op,
                lhs: Box::new(lhs.clone()),
                rhs: Box::new(rhs.clone()),
                type_: RuntimeType::BoolRuntimeType,
            },
        },
        (
            bin_op,
            exp1,
            Lit {
                lit: BoolLit { bool_value: b },
                ..
            },
        ) => match bin_op {
            Implies => {
                if *b {
                    Expression::TRUE
                } else {
                    negate(exp1.clone())
                }
            }
            And => {
                if *b {
                    exp1.clone()
                } else {
                    Expression::FALSE
                }
            }
            Or => {
                if *b {
                    Expression::TRUE
                } else {
                    lhs.clone()
                }
            }
            _ => Expression::BinOp {
                bin_op,
                lhs: Box::new(lhs.clone()),
                rhs: Box::new(rhs.clone()),
                type_: RuntimeType::BoolRuntimeType,
            },
        },
        // Integer evaluation
        (
            Divide | Modulo,
            _,
            Lit {
                lit: IntLit { int_value: 0 },
                type_,
            },
        ) => panic!("infeasible, division/modulo by zero"),
        (
            bin_op,
            Lit {
                lit: IntLit { int_value: a },
                ..
            },
            Lit {
                lit: IntLit { int_value: b },
                ..
            },
        ) => match bin_op {
            Equal => Expression::bool(*a == *b),
            NotEqual => Expression::bool(*a != *b),
            LessThan => Expression::bool(*a < *b),
            LessThanEqual => Expression::bool(*a <= *b),
            GreaterThan => Expression::bool(*a > *b),
            GreaterThanEqual => Expression::bool(*a >= *b),
            Plus => Expression::int(*a + *b),
            Minus => Expression::int(*a - *b),
            Multiply => Expression::int(*a * *b),
            Divide => Expression::int(*a / *b),
            Modulo => Expression::int(*a % *b),
            _ => panic!("unsupported integer operator"),
        },
        (bin_op, Ref { ref_: a, .. }, Ref { ref_: b, .. }) => match bin_op {
            Equal => Expression::bool(*a == *b),
            NotEqual => Expression::bool(*a != *b),
            _ => panic!("unsupported ref operator"),
        },
        (bin_op, Ref { .. }, Lit { lit: NullLit, .. }) => match bin_op {
            Equal => Expression::FALSE,
            NotEqual => Expression::TRUE,
            _ => panic!("unsupported ref operator"),
        },
        (bin_op, Lit { lit: NullLit, .. }, Ref { .. }) => match bin_op {
            Equal => Expression::FALSE,
            NotEqual => Expression::TRUE,
            _ => panic!("unsupported ref operator"),
        },
        (bin_op, Lit { lit: NullLit, .. }, Lit { lit: NullLit, .. }) => match bin_op {
            Equal => Expression::TRUE,
            NotEqual => Expression::FALSE,
            _ => panic!("unsupported ref operator"),
        },
        (bin_op, SymbolicRef { var: a, .. }, SymbolicRef { var: b, .. }) => {
            if *a == *b {
                match bin_op {
                    Equal => Expression::TRUE,
                    NotEqual => Expression::FALSE,
                    _ => panic!("unsupported ref operator"),
                }
            } else {
                Expression::BinOp {
                    bin_op,
                    lhs: Box::new(lhs.clone()),
                    rhs: Box::new(rhs.clone()),
                    type_: RuntimeType::BoolRuntimeType,
                }
            }
        }
        (bin_op, _, _) => Expression::BinOp {
            bin_op,
            lhs: Box::new(lhs.clone()),
            rhs: Box::new(rhs.clone()),
            type_: RuntimeType::BoolRuntimeType,
        }, // room for optimization
    }
}

fn evaluate_unop(unop: UnOp, expression: Expression) -> Expression {
    match (unop, expression) {
        (
            UnOp::Negative,
            Expression::Lit {
                lit: Lit::IntLit { int_value },
                ..
            },
        ) => Expression::Lit {
            lit: Lit::IntLit {
                int_value: -int_value,
            },
            type_: RuntimeType::IntRuntimeType,
        },
        (UnOp::Negative, expression) => negative(expression),
        (
            UnOp::Negate,
            Expression::Lit {
                lit: Lit::BoolLit { bool_value },
                ..
            },
        ) => Expression::Lit {
            lit: Lit::BoolLit {
                bool_value: !bool_value,
            },
            type_: RuntimeType::BoolRuntimeType,
        },
        (UnOp::Negate, expression) => negate(expression),
    }
}


#[test]
fn test_local_solver() {
    let lhs = Expression::Ref { ref_: 1, type_: RuntimeType::ANYRuntimeType };
    let rhs = Expression::Lit { lit: Lit::NullLit, type_: RuntimeType::ANYRuntimeType };

    let expression1 = Expression::BinOp { bin_op: BinOp::NotEqual, lhs: Box::new(lhs), rhs: Box::new(rhs), type_: RuntimeType::ANYRuntimeType };
    
    let expression = Expression::BinOp { bin_op: BinOp::And, lhs: Box::new(expression1.clone()), rhs: Box::new(expression1.clone()), type_: RuntimeType::ANYRuntimeType };

    let expression = Expression::BinOp { bin_op: BinOp::And, lhs: Box::new(expression.clone()), rhs: Box::new(negate(expression1.clone())), type_: RuntimeType::ANYRuntimeType };

    let expression = Expression::BinOp { bin_op: BinOp::Implies, lhs: Box::new(expression), rhs: Box::new(Expression::TRUE), type_: RuntimeType::ANYRuntimeType };

    let expression = Expression::UnOp { un_op: UnOp::Negate, value: Box::new(expression), type_: RuntimeType::ANYRuntimeType };
    // dbg!(&expression);

    let mut heap = HashMap::new();
    let mut stack = Vec::new();
    let mut alias_map = HashMap::new();
    let mut ref_counter = 1;
    let mut st = SymbolicTable { class_to_fields: HashMap::new() };
    let result = eval_locally(&mut heap, &stack, &mut alias_map, &expression, &mut ref_counter, &st);

    assert_eq!(result, Expression::Lit { lit: Lit::BoolLit { bool_value: false }, type_: RuntimeType::BoolRuntimeType});
}