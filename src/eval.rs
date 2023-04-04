// simplify the expression

use std::{ops::Deref, rc::Rc};

use itertools::{Either, Itertools};

use crate::{
    dsl::{ands, negate, negative, ors, to_int_expr},
    exec::{
        get_element, init_symbolic_reference, single_alias_elimination, HeapValue, State, Engine,
    },
    positioned::SourcePos,
    stack::{remove_from_stack, write_to_stack, StackFrame},
    syntax::{BinOp, Expression, Identifier, Lit, RuntimeType, UnOp},
};

pub type EvaluationResult<T> = Either<Rc<Expression>, T>;

pub fn evaluate_as_int(
    state: &mut State,
    expression: Rc<Expression>,
    en: &mut impl Engine,
) -> EvaluationResult<i64> {
    let expression = evaluate(state, expression, en);
    if let Expression::Lit {
        lit: Lit::IntLit { int_value },
        ..
    } = expression.deref()
    {
        Either::Right(*int_value)
    } else {
        Either::Left(expression)
    }
}

pub fn evaluate(state: &mut State, expression: Rc<Expression>, en: &mut impl Engine) -> Rc<Expression> {
    // dbg!(expression)
    let expression = eval_locally(state, expression, en);
    // dbg!(&expression);
    return expression;
}


fn eval_locally(state: &mut State, expression: Rc<Expression>, en: &mut impl Engine) -> Rc<Expression> {
    match expression.as_ref() {
        Expression::BinOp {
            bin_op,
            lhs,
            rhs,
            type_,
            info,
        } => {
            let lhs = eval_locally(state, lhs.clone(), en);
            let rhs = eval_locally(state, rhs.clone(), en);
            evaluate_binop(bin_op.clone(), &lhs, &rhs)
        }
        Expression::UnOp {
            un_op,
            value,
            type_,
            info,
        } => {
            let value = eval_locally(state, value.clone(), en);
            evaluate_unop(un_op.clone(), value)
        }
        Expression::Var { var, type_, info } => {
            let StackFrame { pc, t, params, .. } = state.stack.last().unwrap();
            let o = params
                .get(var)
                .unwrap_or_else(|| panic!("infeasible, object does not exist: {:?}", var));
            //dbg!("var", var);
            let exp = eval_locally(state, o.clone(), en);

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
        Expression::SymbolicVar { .. } => expression,
        Expression::Lit { .. } => expression,
        Expression::SizeOf { var, type_, info } => {
            let StackFrame { pc, t, params, .. } = state.stack.last().unwrap();
            let expr = single_alias_elimination(params[var].clone(), &state.alias_map);

            match expr.as_ref() {
                Expression::Lit {
                    lit: Lit::NullLit,
                    type_,
                    info,
                } => {
                    // infeasible path
                    return Expression::int(-1);
                }
                Expression::Ref { ref_, .. } => {
                    if let HeapValue::ArrayValue { elements, .. } = &state.heap[ref_] {
                        return Expression::int(elements.len() as i64);
                    }
                }
                _ => todo!(),
            }
            dbg!(&state.heap, var, params[var].as_ref());
            panic!("invalid state, expected initialised array with arrayvalue in heap");
        }
        Expression::Ref { .. } => expression,
        Expression::SymbolicRef { var, type_, info } => {
            init_symbolic_reference(state, &var, &type_, en);

            Rc::new(Expression::SymbolicRef {
                var: var.clone(),
                type_: type_.clone(),
                info: *info,
            })
        }
        Expression::Conditional {
            guard,
            true_,
            false_,
            type_,
            info,
        } => {
            let guard = eval_locally(state, guard.clone(), en);
            let true_ = eval_locally(state, true_.clone(), en);
            let false_ = eval_locally(state, false_.clone(), en);

            match *guard {
                Expression::Lit {
                    lit: Lit::BoolLit { bool_value: true },
                    ..
                } => true_,

                Expression::Lit {
                    lit: Lit::BoolLit { bool_value: false },
                    ..
                } => false_,
                _ => Rc::new(Expression::Conditional {
                    guard: guard,
                    true_: true_,
                    false_: false_,
                    type_: type_.clone(),
                    info: *info,
                }),
            }
        }
        Expression::Forall {
            elem,
            range,
            domain,
            formula,
            type_,
            info,
        } => evaluate_quantifier(ands, elem, range, domain, formula, state, en),
        Expression::Exists {
            elem,
            range,
            domain,
            formula,
            type_,
            info,
        } => evaluate_quantifier(ors, elem, range, domain, formula, state, en),
    }
}

fn evaluate_binop(bin_op: BinOp, lhs: &Expression, rhs: &Expression) -> Rc<Expression> {
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
                    Rc::new(rhs.clone())
                } else {
                    Rc::new(Expression::TRUE)
                }
            }
            And => {
                if *a {
                    Rc::new(rhs.clone())
                } else {
                    Rc::new(Expression::FALSE)
                }
            }
            Or => {
                if *a {
                    Rc::new(Expression::TRUE)
                } else {
                    Rc::new(exp2.clone())
                }
            }
            _ => Rc::new(Expression::BinOp {
                bin_op,
                lhs: Rc::new(lhs.clone()),
                rhs: Rc::new(rhs.clone()),
                type_: RuntimeType::BoolRuntimeType,
                info: SourcePos::UnknownPosition,
            }),
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
                    Rc::new(Expression::TRUE)
                } else {
                    Rc::new(negate(Rc::new(exp1.clone())))
                }
            }
            And => {
                if *b {
                    Rc::new(exp1.clone())
                } else {
                    Rc::new(Expression::FALSE)
                }
            }
            Or => {
                if *b {
                    Rc::new(Expression::TRUE)
                } else {
                    Rc::new(lhs.clone())
                }
            }
            _ => Rc::new(Expression::BinOp {
                bin_op,
                lhs: Rc::new(lhs.clone()),
                rhs: Rc::new(rhs.clone()),
                type_: RuntimeType::BoolRuntimeType,
                info: SourcePos::UnknownPosition,
            }),
        },
        // Integer evaluation
        (
            Divide | Modulo,
            _,
            Lit {
                lit: IntLit { int_value: 0 },
                type_,
                info: SourcePos::UnknownPosition,
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
            Equal => Rc::new(Expression::FALSE),
            NotEqual => Rc::new(Expression::TRUE),
            _ => panic!("unsupported ref operator"),
        },
        (bin_op, Lit { lit: NullLit, .. }, Ref { .. }) => match bin_op {
            Equal => Rc::new(Expression::FALSE),
            NotEqual => Rc::new(Expression::TRUE),
            _ => panic!("unsupported ref operator"),
        },
        (bin_op, Lit { lit: NullLit, .. }, Lit { lit: NullLit, .. }) => match bin_op {
            Equal => Rc::new(Expression::TRUE),
            NotEqual => Rc::new(Expression::FALSE),
            _ => panic!("unsupported ref operator"),
        },
        (bin_op, SymbolicRef { var: a, .. }, SymbolicRef { var: b, .. }) => {
            if *a == *b {
                match bin_op {
                    Equal => Rc::new(Expression::TRUE),
                    NotEqual => Rc::new(Expression::FALSE),
                    _ => panic!("unsupported ref operator"),
                }
            } else {
                Rc::new(Expression::BinOp {
                    bin_op,
                    lhs: Rc::new(lhs.clone()),
                    rhs: Rc::new(rhs.clone()),
                    type_: RuntimeType::BoolRuntimeType,
                    info: SourcePos::UnknownPosition,
                })
            }
        }
        (bin_op, _, _) => Rc::new(Expression::BinOp {
            bin_op,
            lhs: Rc::new(lhs.clone()),
            rhs: Rc::new(rhs.clone()),
            type_: RuntimeType::BoolRuntimeType,
            info: SourcePos::UnknownPosition,
        }), // room for optimization
    }
}

fn evaluate_unop(unop: UnOp, expression: Rc<Expression>) -> Rc<Expression> {
    match (unop, expression.as_ref()) {
        (
            UnOp::Negative,
            Expression::Lit {
                lit: Lit::IntLit { int_value },
                ..
            },
        ) => Rc::new(Expression::Lit {
            lit: Lit::IntLit {
                int_value: -int_value,
            },
            type_: RuntimeType::IntRuntimeType,
            info: SourcePos::UnknownPosition,
        }),
        (UnOp::Negative, _) => Rc::new(negative(expression)),
        (
            UnOp::Negate,
            Expression::Lit {
                lit: Lit::BoolLit { bool_value },
                ..
            },
        ) => Rc::new(Expression::Lit {
            lit: Lit::BoolLit {
                bool_value: !bool_value,
            },
            type_: RuntimeType::BoolRuntimeType,
            info: SourcePos::UnknownPosition,
        }),
        (UnOp::Negate, _) => Rc::new(negate(expression)),
    }
}

/// Turns a `forall` or an `exists` into an expression with chained binary operators
/// forall <elem>, <range> : <domain> : <formula>
/// For example the expression:
/// ```
/// "forall elem, index : a : elem > 0";
/// ```
/// becomes, when a = { 0, 1, 2 }
/// ```
/// "0 > 0 && 1 > 0 && 2 > 0";
/// ```
///
/// F is a function that chains each subexpression together with a binary operator into one expression.
fn evaluate_quantifier<'a, F>(
    quantifier: F,
    elem: &'a Identifier,
    range: &'a Identifier,
    domain: &'a Identifier,
    formula: &'a Expression,
    state: &'a mut State,
    en: &mut impl Engine,
) -> Rc<Expression>
where
    F: Fn(Vec<Rc<Expression>>) -> Expression,
{
    let array = state
        .stack
        .last()
        .unwrap()
        .params
        .get(domain)
        .unwrap()
        .clone();
    let array = evaluate(state, array, en);

    let array = single_alias_elimination(array, &state.alias_map);

    match array.as_ref() {
        Expression::Lit {
            lit: Lit::NullLit, ..
        } => Expression::FALSE.into(), // return false?
        Expression::Ref { ref_, type_, info } => {
            // This might be optimized by not passing in &mut State, but instead pass in &Heap, &mut AliasMap, &mut reference_counter
            // for i in 0..elements.len()
            //    clone value, clone index
            //    run evaluation on other stuff

            let len = if let HeapValue::ArrayValue { elements, .. } = state.heap.get(&ref_).unwrap()
            {
                elements.len()
            } else {
                panic!("expected Array object")
            };

            //
            let formulas = (0..len)
                .map(|i| {
                    let element = get_element(i, *ref_, &state.heap);
                    let index = to_int_expr(i as i64);

                    write_to_stack(elem.clone(), element.clone(), &mut state.stack);
                    write_to_stack(range.clone(), index, &mut state.stack);
                    let value = evaluate(state, formula.clone().into(), en);
                    remove_from_stack(elem, &mut state.stack);
                    remove_from_stack(range, &mut state.stack);

                    value.clone()
                })
                .collect_vec();

            quantifier(formulas).into()
        }
        _ => unreachable!("Expected array to be a reference, found {:?}", array),
    }
}

// #[test]
// fn test_local_solver() {
//     let lhs = Expression::Ref {
//         ref_: 1,
//         type_: RuntimeType::ANYRuntimeType,
//     };
//     let rhs = Expression::Lit {
//         lit: Lit::NullLit,
//         type_: RuntimeType::ANYRuntimeType,
//     };

//     let expression1 = Expression::BinOp {
//         bin_op: BinOp::NotEqual,
//         lhs: Rc::new(lhs),
//         rhs: Rc::new(rhs),
//         type_: RuntimeType::ANYRuntimeType,
//     };

//     let expression = Expression::BinOp {
//         bin_op: BinOp::And,
//         lhs: Rc::new(expression1.clone()),
//         rhs: Rc::new(expression1.clone()),
//         type_: RuntimeType::ANYRuntimeType,
//     };

//     let expression = Expression::BinOp {
//         bin_op: BinOp::And,
//         lhs: Rc::new(expression.clone()),
//         rhs: Rc::new(negate(Rc::new(expression1))),
//         type_: RuntimeType::ANYRuntimeType,
//     };

//     let expression = Expression::BinOp {
//         bin_op: BinOp::Implies,
//         lhs: Rc::new(expression),
//         rhs: Rc::new(Expression::TRUE),
//         type_: RuntimeType::ANYRuntimeType,
//     };

//     let expression = Expression::UnOp {
//         un_op: UnOp::Negate,
//         value: Rc::new(expression),
//         type_: RuntimeType::ANYRuntimeType,
//     };
//     // dbg!(&expression);

//     let mut heap = HashMap::new();
//     let mut stack = Vec::new();
//     let mut alias_map = HashMap::new();
//     let mut ref_counter = 1;
//     let mut st = SymbolicTable {
//         class_to_fields: HashMap::new(),
//     };

//     let mut state = State { stack, heap, precondition: Expression::NULL, alias_map, pc: 0, constraints: Default::default(), ref_counter: Default::default() };
//     let result = eval_locally(
//         &mut state,
//         Rc::new(expression),
//         &st,
//     );

//     assert_eq!(
//         *result,
//         Expression::Lit {
//             lit: Lit::BoolLit { bool_value: false },
//             type_: RuntimeType::BoolRuntimeType
//         }
//     );
// }
