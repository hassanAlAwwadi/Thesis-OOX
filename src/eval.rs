// simplify the expression

use crate::{
    exec::{init, AliasMap, Heap},
    stack::StackFrame,
    syntax::Expression,
};

pub fn evaluate(
    heap: &mut Heap,
    stack: &Vec<StackFrame>,
    alias_map: &mut AliasMap,
    expression: &Expression,
    ref_counter: &mut i64,
) -> Expression {
    // if substitute
    ////dbg!(&stack);

    substitute(heap, stack, alias_map, expression, ref_counter)
}

fn substitute(
    heap: &mut Heap,
    stack: & Vec<StackFrame>,
    alias_map: &mut AliasMap,
    expression: &Expression,
    ref_counter: &mut i64,
) -> Expression {
    match expression {
        Expression::BinOp {
            bin_op,
            lhs,
            rhs,
            type_,
        } => {
            let lhs = Box::new(substitute(heap, stack, alias_map, lhs, ref_counter));
            let rhs = Box::new(substitute(heap, stack, alias_map, rhs, ref_counter));
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
            let value = Box::new(substitute(heap, stack, alias_map, value, ref_counter));
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

                    init(heap, alias_map, var, type_, ref_counter);

                    value.clone()
                }
                value => substitute(heap, stack, alias_map, value, ref_counter),
            }
        }
        sv @ Expression::SymbolicVar { .. } => sv.clone(),
        lit @ Expression::Lit { .. } => lit.clone(),
        Expression::SizeOf { var, type_ } => {
            todo!()
        }
        ref_ @ Expression::Ref { .. } => ref_.clone(),
        Expression::SymbolicRef { var, type_ } => {
            init(heap, alias_map, var, type_, ref_counter);

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
            let guard = Box::new(substitute(heap, stack, alias_map, guard, ref_counter));
            let false_ = Box::new(substitute(heap, stack, alias_map, false_, ref_counter));
            let true_ = Box::new(substitute(heap, stack, alias_map, true_, ref_counter));
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


#[test]
fn substituting_test1() {
    
}