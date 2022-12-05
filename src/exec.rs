use core::panic;
use std::collections::{HashMap, HashSet};

use itertools::Itertools;
use ordered_float::NotNan;
use z3::SatResult;

use crate::{
    cfg::{labelled_statements, CFGStatement},
    dsl::negate,
    eval::{self, evaluate},
    lexer::tokens,
    parser_pom::parse,
    stack::{lookup_in_stack, StackFrame},
    symbolic_table::SymbolicTable,
    syntax::{
        BinOp, DeclarationMember, Expression, Identifier, Invocation, Lhs, Lit, NonVoidType,
        Parameter, Reference, Rhs, RuntimeType, Statement, UnOp, Declaration,
    },
    typeable::Typeable,
    utils, z3_checker, concretization::{concretizations, find_symbolic_refs},
};

const NULL: Expression = Expression::Lit {
    lit: Lit::NullLit,
    type_: RuntimeType::ANYRuntimeType,
};

fn retval() -> String {
    "retval".to_string()
}

pub type Heap = HashMap<Reference, HeapValue>;

#[derive(Clone, Debug)]
pub enum HeapValue {
    ObjectValue {
        fields: HashMap<Identifier, Expression>,
        type_: RuntimeType,
    },
    ArrayValue(Vec<Expression>),
}

impl HeapValue {
    fn empty_object() -> HeapValue {
        HeapValue::ObjectValue {
            fields: HashMap::new(),
            type_: RuntimeType::ANYRuntimeType,
        }
    }
}

type PathConstraints = HashSet<Expression>;

// refactor to Vec<Reference>? neins, since it can also be ITE and stuff
pub type AliasMap = HashMap<String, Vec<Expression>>;

enum Output {
    Valid,
    Invalid,
    Unknown,
}

// perhaps separate program from this structure, such that we can have multiple references to it.
#[derive(Clone)]
struct State {
    pc: u64,
    program: HashMap<u64, CFGStatement>,
    stack: Vec<StackFrame>,
    heap: Heap,
    precondition: Expression,

    constraints: PathConstraints,
    alias_map: AliasMap,
    ref_counter: i64,
}

fn default(t: impl Typeable) -> Expression {
    let type_ = t.type_of();
    let lit = match &type_ {
        RuntimeType::UIntRuntimeType => Lit::UIntLit { uint_value: 0 },
        RuntimeType::IntRuntimeType => Lit::IntLit { int_value: 0 },
        RuntimeType::FloatRuntimeType => Lit::FloatLit {
            float_value: NotNan::new(0.0).unwrap(),
        },
        RuntimeType::BoolRuntimeType => Lit::BoolLit { bool_value: false },
        RuntimeType::StringRuntimeType => Lit::NullLit,
        RuntimeType::CharRuntimeType => Lit::CharLit { char_value: '\0' },
        RuntimeType::ReferenceRuntimeType { type_ } => Lit::NullLit,
        RuntimeType::ArrayRuntimeType { inner_type } => Lit::NullLit,
        RuntimeType::ANYRuntimeType => todo!(),
        RuntimeType::NUMRuntimeType => todo!(),
        RuntimeType::REFRuntimeType => todo!(),
        RuntimeType::ARRAYRuntimeType => todo!(),
        RuntimeType::VoidRuntimeType => todo!(),
        RuntimeType::UnknownRuntimeType => todo!(),
    };

    Expression::Lit { lit, type_ }
}

#[derive(Debug, PartialEq, Eq)]
enum SymResult {
    Valid,
    Invalid,
}

fn sym_exec(
    state: &mut State,
    flows: &HashMap<u64, Vec<u64>>,
    k: u64,
    st: &SymbolicTable,
) -> SymResult {
    if k == 0 {
        // finishing current branch
        //dbg!("FINITO");
        return SymResult::Valid;
    }
    let next = action(state, k, st);

    // //dbg!(&state.pc);

    match next {
        ActionResult::FunctionCall(next) => {
            // function call or return
            state.pc = next;
            sym_exec(state, flows, k - 1, st);
        }
        ActionResult::Return(return_pc) => {
            if let Some(neighbours) = flows.get(&return_pc) {
                for neighbour_pc in neighbours {
                    let mut new_state = state.clone();
                    new_state.pc = *neighbour_pc;

                    let result = sym_exec(&mut new_state, flows, k - 1, st);
                    if result != SymResult::Valid {
                        return result;
                    }
                }
            } else {
                panic!("function pc does not exist");
            }
        }
        ActionResult::Continue => {
            if let Some(neighbours) = flows.get(&state.pc) {
                // //dbg!(&neighbours);
                for neighbour_pc in neighbours {
                    let mut new_state = state.clone();
                    new_state.pc = *neighbour_pc;

                    let result = sym_exec(&mut new_state, flows, k - 1, st);
                    if result != SymResult::Valid {
                        return result;
                    }
                }
            } else {
                // Function exit of the main function under verification
                if let CFGStatement::FunctionExit(_) = state.program[&state.pc] {
                    return SymResult::Valid;
                } else {
                    return SymResult::Invalid;
                }
            }
        }
    };
    SymResult::Valid
}

enum ActionResult {
    Continue,
    Return(u64),
    FunctionCall(u64),
}

fn action(
    State {
        pc,
        program,
        stack,
        heap,
        precondition,
        constraints,
        alias_map,
        ref_counter,
    }: &mut State,
    k: u64,
    st: &SymbolicTable,
) -> ActionResult {
    let action = &program[&pc];

    dbg!(&action, stack.last().map(|s| &s.params));

    match action {
        CFGStatement::Statement(Statement::Declare { type_, var }) => {
            let StackFrame { pc, t, params, .. } = stack.last_mut().unwrap();
            params.insert(var.clone(), default(type_));

            ActionResult::Continue
        }
        CFGStatement::Statement(Statement::Assign { lhs, rhs }) => {
            if let Rhs::RhsCall { invocation, type_ } = rhs {
                return exec_invocation(
                    heap,
                    invocation,
                    stack,
                    alias_map,
                    &program,
                    *pc,
                    Some(lhs.clone()),
                    ref_counter,
                    st,
                );
            }
            let value = evaluateRhs(heap, stack, alias_map, ref_counter, rhs, st);
            let e = evaluate(heap, stack, alias_map, &value, ref_counter, st);
            execute_assign(heap, stack, alias_map, ref_counter, lhs, e, st);

            ActionResult::Continue
        }
        CFGStatement::Statement(Statement::Assert { assertion }) => {
            let expression = exec_assert(
                &constraints,
                assertion,
                heap,
                stack,
                alias_map,
                ref_counter,
                st,
            );
            if expression == true_lit() {
                panic!("invalid");
            } else if expression == false_lit() {
                ActionResult::Continue
            } else {
                dbg!("invoke Z3 with:", &expression);
                // dbg!(&alias_map);
                let symbolic_refs = find_symbolic_refs(&expression);
                if symbolic_refs.len() == 0 {
                    let result = z3_checker::verify(&expression);
                    if let SatResult::Unsat = result {
                        
                    } else {
                        panic!("invalid")
                    }
                } else {
                    // dbg!(&symbolic_refs);
                    let expressions = concretizations(&expression, &symbolic_refs, alias_map);
                    dbg!(&expressions);

                    for expression in expressions {
                        let expression = evaluate(heap, stack, alias_map, &expression, ref_counter, st);
                        if expression == true_lit() {
                            panic!("invalid");
                        } else if expression == false_lit() {
                            // valid, keep going
                            dbg!("locally solved!");
                        } else {
                            // panic!("should not do that right now");
                            let result = z3_checker::verify(&expression);
                            if let SatResult::Unsat = result {
                            } else {
                                panic!("invalid")
                            }
                        }
                        
                    }
                }
                

                ActionResult::Continue
            }
        }
        CFGStatement::Statement(Statement::Assume { assumption }) => {
            let expression = evaluate(heap, stack, alias_map, assumption, ref_counter, st);
            dbg!(assumption, &expression);
            //dbg!(&assumption, &expression, stack.last().map(|s| &s.params));
            if expression == false_lit() {
                panic!("infeasible, prune this path");
            } else if expression != true_lit() {
                constraints.insert(expression);
            }
            ActionResult::Continue
        }
        CFGStatement::Statement(Statement::Return { expression }) => {
            if let Some(expression) = expression {
                let StackFrame { pc, t, params, .. } = stack.last_mut().unwrap();
                params.insert("retval".to_string(), expression.clone());
            }
            ActionResult::Continue
        }
        CFGStatement::FunctionEntry(_name) => {
            // only check preconditions when it's the first method called??
            // we assume that the previous stackframe is of this method
            let StackFrame { current_member, .. } = stack.last().unwrap();
            if let Some(requires) = current_member.requires() {
                exec_assert(
                    constraints,
                    requires,
                    heap,
                    stack,
                    alias_map,
                    ref_counter,
                    st,
                );
                // more?
            }
            ActionResult::Continue
        }
        CFGStatement::FunctionExit(_name) => {
            let StackFrame {
                current_member,
                params,
                ..
            } = stack.last().unwrap();
            if let Some(post_condition) = current_member.post_condition() {
                exec_assert(
                    constraints,
                    post_condition,
                    heap,
                    stack,
                    alias_map,
                    ref_counter,
                    st,
                );
                // some if true then unfeasible/invalid or something?
            }
            if stack.len() == 1 {
                ActionResult::Continue
                // we are pbobably done now
            } else {
                let rv = stack.last().unwrap().params.get(&retval()).unwrap();
                let return_value = evaluate(heap, stack, alias_map, rv, ref_counter, st);

                let StackFrame { pc, t, .. } = stack.pop().unwrap();
                if let Some(lhs) = t {
                    // perhaps also write retval to current stack?
                    // will need to do this due to this case: `return o.func();`

                    execute_assign(heap, stack, alias_map, ref_counter, &lhs, return_value, st);
                }
                ActionResult::Return(pc)
            }
        }
        CFGStatement::Statement(Statement::Call { invocation }) => exec_invocation(
            heap,
            invocation,
            stack,
            alias_map,
            &program,
            *pc,
            None,
            ref_counter,
            st,
        ),

        _ => ActionResult::Continue,
    }
}

fn exec_invocation(
    heap: &mut Heap,
    invocation: &Invocation,
    stack: &mut Vec<StackFrame>,
    alias_map: &mut AliasMap,
    program: &HashMap<u64, CFGStatement>,
    return_point: u64,
    lhs: Option<Lhs>,
    ref_counter: &mut i64,
    st: &SymbolicTable,
) -> ActionResult {
    dbg!(invocation);
    let (Declaration::Class { name: class_name, .. }, member) = invocation.resolved().unwrap(); // i don't get this

    match member {
        // ??
        DeclarationMember::Method {
            is_static: true,
            return_type,
            name,
            params,
            specification,
            body,
        } => {
            // evaluate arguments
            let arguments = invocation
                .arguments()
                .into_iter()
                .map(|arg| evaluate(heap, stack, alias_map, arg, ref_counter, st))
                .collect::<Vec<_>>();

            exec_static_method(heap, stack, alias_map, return_point, member.clone(), lhs, &arguments, params, ref_counter, st);
            let next_entry = find_entry_for_static_invocation(invocation.identifier(), program);

            ActionResult::FunctionCall(next_entry)
        }
        DeclarationMember::Method {
            is_static: false,
            return_type,
            name,
            params,
            specification,
            body,
        } => {
            // evaluate arguments
            let arguments = invocation
                .arguments()
                .into_iter()
                .map(|arg| evaluate(heap, stack, alias_map, arg, ref_counter, st))
                .collect::<Vec<_>>();

            let invocation_lhs = if let Invocation::InvokeMethod { lhs, .. } = invocation {
                lhs
            } else {
                panic!("expected invokemethod");
            };
            
            let this = (NonVoidType::ReferenceType { identifier: class_name.to_string() }, invocation_lhs. to_owned());

            exec_method(heap, stack, alias_map, return_point, member.clone(), lhs, &arguments, params, ref_counter, st, this);
            let next_entry = find_entry_for_static_invocation(invocation.identifier(), program);

            ActionResult::FunctionCall(next_entry)
        }
        DeclarationMember::Constructor {
            name,
            params,
            specification,
            body,
        } => todo!(),
        DeclarationMember::Field { type_, name } => todo!(),
    }
}

fn find_entry_for_static_invocation(invocation: &str, program: &HashMap<u64, CFGStatement>) -> u64 {
    let (entry, _) = program
        .iter()
        .find(|(k, v)| **v == CFGStatement::FunctionEntry(invocation.to_string()))
        .unwrap();

    *entry
}

// fn exec_invocation(stack: &mut Vec<StackFrame>, invocation: &Invocation, return_point: u64, member: DeclarationMember, lhs_return: Option<Lhs>) {
//     match invocation {
//         Invocation::InvokeMethod { lhs, rhs, arguments, resolved } =>
//         exec_static_method(&mut stack, *pc, member.clone(), lhs),
//         Invocation::InvokeConstructor { class_name, arguments, resolved } => todo!(),
//     }

// }

fn exec_method(
    heap: &mut Heap,
    stack: &mut Vec<StackFrame>,
    alias_map: &mut AliasMap,
    return_point: u64,
    member: DeclarationMember,
    lhs: Option<Lhs>,
    arguments: &[Expression],
    parameters: &[Parameter],
    ref_counter: &mut i64,
    st: &SymbolicTable,
    this: (NonVoidType, Identifier)
) {
    let this_param = Parameter { type_: this.0.clone(), name: "this".to_owned() };
    let this_expr = Expression::Var { var: this.1.clone(), type_: this.0.type_of() };
    let parameters = std::iter::once(&this_param).chain(parameters.iter());
    let arguments = std::iter::once(&this_expr).chain(arguments.iter());

    push_stack_frame(
        heap,
        stack,
        alias_map,
        return_point,
        member,
        lhs,
        parameters.zip(arguments),
        ref_counter,
        st
    )
}

fn exec_static_method(
    heap: &mut Heap,
    stack: &mut Vec<StackFrame>,
    alias_map: &mut AliasMap,
    return_point: u64,
    member: DeclarationMember,
    lhs: Option<Lhs>,
    arguments: &[Expression],
    parameters: &[Parameter],
    ref_counter: &mut i64,
    st: &SymbolicTable,
) {
    push_stack_frame(
        heap,
        stack,
        alias_map,
        return_point,
        member,
        lhs,
        parameters.iter().zip(arguments.iter()),
        ref_counter,
        st
    )
}

fn push_stack_frame<'a, P>(
    heap: &mut Heap,
    stack: &mut Vec<StackFrame>,
    alias_map: &mut AliasMap,
    return_point: u64,
    member: DeclarationMember,
    lhs: Option<Lhs>,
    params: P,
    ref_counter: &mut i64,
    st: &SymbolicTable,
) where
    P: Iterator<Item = (&'a Parameter, &'a Expression)>,
{
    let params = params.map(|(p, e)| (p.name.clone(), evaluate(heap, stack, alias_map, e, ref_counter, st))).collect();
    let stack_frame = StackFrame {
        pc: return_point,
        t: lhs,
        params,
        current_member: member,
    };
    stack.push(stack_frame);
}

fn exec_assert(
    constraints: &PathConstraints,
    assertion: &Expression,
    heap: &mut Heap,
    stack: &Vec<StackFrame>,
    alias_map: &mut AliasMap,
    ref_counter: &mut i64,
    st: &SymbolicTable,
) -> Expression {
    let expression = if constraints.len() >= 1 {
        let assumptions = constraints
            .iter()
            .cloned()
            .reduce(|x, y| Expression::BinOp {
                bin_op: BinOp::And,
                lhs: Box::new(x),
                rhs: Box::new(y),
                type_: RuntimeType::BoolRuntimeType,
            })
            .unwrap();

        negate(Expression::BinOp {
            bin_op: BinOp::Implies,
            lhs: Box::new(assumptions),
            rhs: Box::new(assertion.clone()),
            type_: RuntimeType::BoolRuntimeType,
        })
    } else {
        negate(assertion.clone())
    };
    // let expression = constraints.iter().fold(
    //     Expression::UnOp {
    //         un_op: UnOp::Negative,
    //         value: Box::new(assertion.clone()),
    //         type_: RuntimeType::BoolRuntimeType,
    //     },
    //     |x, b| Expression::BinOp {
    //         bin_op: BinOp::And,
    //         lhs: Box::new(x),
    //         rhs: Box::new(b.clone()),
    //         type_: RuntimeType::BoolRuntimeType,
    //     },
    // );
    // //dbg!(&expression);
    let z = evaluate(heap, stack, alias_map, &expression, ref_counter, st);
    // //dbg!(&z);
    z
}

fn read_field_concrete_ref(heap: &mut Heap, ref_: i64, field: &Identifier) -> Expression {
    match heap.get_mut(&ref_).unwrap() {
        HeapValue::ObjectValue { fields, type_ } => fields[field].clone(),
        _ => panic!("Expected object, found array heapvalue"),
    }
}

fn ite(guard: Expression, e1: Expression, e2: Expression) -> Expression {
    Expression::Conditional {
        guard: Box::new(guard),
        true_: Box::new(e1),
        false_: Box::new(e2),
        type_: RuntimeType::ANYRuntimeType,
    }
}

fn equal(e1: Expression, e2: Expression) -> Expression {
    Expression::BinOp {
        bin_op: BinOp::Equal,
        lhs: Box::new(e1),
        rhs: Box::new(e2),
        type_: RuntimeType::ANYRuntimeType,
    }
}

fn read_field_symbolic_ref(
    heap: &mut Heap,
    concrete_refs: &[Expression],
    sym_ref: &Expression,
    field: &Identifier,
) -> Expression {
    match concrete_refs {
        [] => panic!(),
        [Expression::Ref { ref_, type_ }] => read_field_concrete_ref(heap, *ref_, field),
        // assuming here that concrete refs (perhaps in ITE expression)
        [r @ Expression::Ref { ref_, .. }, rs @ ..] => Expression::Conditional {
            guard: Box::new(Expression::BinOp {
                bin_op: BinOp::Equal,
                lhs: Box::new(sym_ref.clone()),
                rhs: Box::new(r.clone()),
                type_: RuntimeType::ANYRuntimeType,
            }),
            true_: Box::new(read_field_concrete_ref(heap, *ref_, &field)),
            false_: Box::new(read_field_symbolic_ref(heap, rs, sym_ref, field)),
            type_: RuntimeType::ANYRuntimeType,
        },
        // null is not possible here, will be caught with exceptional state
        _ => panic!(),
    }
}

fn write_field_concrete_ref(
    heap: &mut Heap,
    ref_: i64,
    field: &Identifier,
    value: Expression,
) -> () {
    // let x = ;

    if let HeapValue::ObjectValue { fields, type_ } = heap.get_mut(&ref_).unwrap() {
        fields.insert(field.clone(), value);
    } else {
        panic!("expected object")
    }
}

fn write_field_symbolic_ref(
    heap: &mut Heap,
    concrete_refs: &Vec<Expression>,
    field: &Identifier,
    sym_ref: &Expression,
    value: Expression,
) -> () {
    match concrete_refs.as_slice() {
        [] => panic!(),
        [Expression::Ref { ref_, type_ }] => {
            write_field_concrete_ref(heap, *ref_, field, value);
        }
        rs => {
            for r in rs {
                if let Expression::Ref { ref_, type_ } = r {
                    let ite = ite(
                        equal(sym_ref.clone(), r.clone()),
                        value.clone(),
                        read_field_concrete_ref(heap, *ref_, &field),
                    );
                    write_field_concrete_ref(heap, *ref_, field, ite)
                } else {
                    panic!("Should only contain refs");
                }
            }
        }
    }
}

fn null() -> Expression {
    Expression::Lit {
        lit: Lit::NullLit,
        type_: RuntimeType::ANYRuntimeType,
    }
}

pub fn init_symbolic_reference(
    heap: &mut Heap,
    alias_map: &mut AliasMap,
    sym_ref: &Identifier,
    type_ref: &RuntimeType,
    ref_counter: &mut i64,
    st: &SymbolicTable,
) {
    if !alias_map.contains_key(sym_ref) {
        let ref_fresh = *ref_counter;
        *ref_counter += 1;

        let class_name = if let RuntimeType::ReferenceRuntimeType { type_ } = type_ref {
            type_
        } else {
            panic!("Cannot initialize any other atm");
        };

        let fields = st
            .get_all_fields(class_name)
            .iter()
            .map(|(field_name, type_)| {
                (
                    field_name.clone(),
                    initialize_symbolic_var(&field_name, &type_.type_of(), ref_counter),
                )
            })
            .collect();

        heap.insert(
            ref_fresh,
            HeapValue::ObjectValue {
                fields,
                type_: type_ref.clone(),
            },
        );

        // Find all other possible concrete references of the same type as sym_ref

        let existing_aliases = alias_map
            .values()
            .filter(|x| x.iter().any(|x| x.type_of() == *type_ref))
            .flat_map(|x| x.iter()).unique();

        let aliases = existing_aliases
            .cloned()
            .chain(
                [
                    null(),
                    Expression::Ref {
                        ref_: ref_fresh,
                        type_: type_ref.clone(),
                    },
                ]
                .into_iter(),
            )
            .collect();

        alias_map.insert(sym_ref.clone(), aliases);
    }
}

// can't you have a symbolic array, as in the a in a[i] is symbolic?
fn write_index(heap: &mut Heap, ref_: i64, index: &Expression, value: &Expression) {
    // match index {
    //     Expression::Ref { ref_, type_ } => {
    //         let Expression::Lit { lit , type_ } = (&mut heap[ref_]);
    //     },
    //     Expression::SymbolicRef { var, type_ } => {},

    // }
}

fn execute_assign(
    heap: &mut Heap,
    stack: &mut Vec<StackFrame>,
    alias_map: &mut AliasMap,
    ref_counter: &mut i64,
    lhs: &Lhs,
    e: Expression,
    st: &SymbolicTable,
) {
    match lhs {
        Lhs::LhsVar { var, type_ } => {
            let StackFrame { pc, t, params, .. } = stack.last_mut().unwrap();
            params.insert(var.clone(), e);
        }
        Lhs::LhsField {
            var,
            var_type,
            field,
            type_,
        } => {
            let StackFrame { pc, t, params, .. } = stack.last_mut().unwrap();
            let o = params
                .get(var)
                .unwrap_or_else(|| panic!("infeasible, object does not exit"));

            match o {
                Expression::Ref { ref_, type_ } => {
                    write_field_concrete_ref(heap, *ref_, field, e.clone());
                }
                sym_ref @ Expression::SymbolicRef { var, type_ } => {
                    init_symbolic_reference(heap, alias_map, var, type_, ref_counter, st);
                    let concrete_refs = &alias_map[var];
                    write_field_symbolic_ref(heap, concrete_refs, field, sym_ref, e);
                }

                _ => todo!(),
            }
            todo!()
        }
        Lhs::LhsElem { var, index, type_ } => {
            let StackFrame { pc, t, params, .. } = stack.last_mut().unwrap();
            let ref_ = params
                .get(var)
                .unwrap_or_else(|| panic!("infeasible, array does not exit"));

            // match ref_ {
            //     Expression::Ref { ref_, type_ } => {
            //         write_field_concrete_ref(heap, *ref_, field, e);
            //     }
            //     sym_ref @ Expression::SymbolicRef { var, type_ } => {
            //         init(heap, &mut state.alias_map, var, type_, &mut state.ref_counter);
            //         let concrete_refs = &state.alias_map[var];
            //         write_field_symbolic_ref(heap, concrete_refs, field, sym_ref, e);
            //     },
            //     _ => panic!("expected ref, found expr {:?}", &ref_),
            // }
        }
    }
}

// fn evaluateRhs(state: &mut State, rhs: &Rhs) -> Expression {
fn evaluateRhs(
    heap: &mut Heap,
    stack: &mut Vec<StackFrame>,
    alias_map: &mut AliasMap,
    ref_counter: &mut i64,
    rhs: &Rhs,
    st: &SymbolicTable,
) -> Expression {
    match rhs {
        Rhs::RhsExpression { value, type_ } => {
            match value {
                Expression::Var { var, type_ } => lookup_in_stack(var, stack).unwrap().clone(),
                _ => value.clone(), // might have to expand on this when dealing with complex quantifying expressions and array
            }
        }
        Rhs::RhsField { var, field, type_ } => {
            if let Expression::Var { var, .. } = var {
                let StackFrame { pc, t, params, .. } = stack.last_mut().unwrap();
                let object = params.get(var).unwrap();
                exec_rhs_field(heap, alias_map, ref_counter, object, field, type_, st)
            } else {
                panic!(
                    "Currently only right hand sides of the form <variable>.<field> are allowed."
                )
            }
        }
        Rhs::RhsElem { var, index, type_ } => todo!("Arrays are wip"),
        Rhs::RhsCall { invocation, type_ } => {
            unreachable!("Don't know why this is unreachable tbh")
        }
        Rhs::RhsArray {
            array_type,
            sizes,
            type_,
        } => todo!("arrays are wip"),
        _ => unimplemented!(),
    }
}

fn exec_rhs_field(
    heap: &mut Heap,
    alias_map: &mut AliasMap,
    ref_counter: &mut i64,
    object: &Expression,
    field: &Identifier,
    type_: &RuntimeType,
    st: &SymbolicTable,
) -> Expression {
    match object {
        Expression::Conditional {
            guard,
            true_,
            false_,
            type_,
        } => {
            // bedoelt hij hier niet exec true_ ipv execField true_ ?
            // nope want hij wil nog steeds het field weten ervan
            let true_ = exec_rhs_field(heap, alias_map, ref_counter, true_, field, type_, st);
            let false_ = exec_rhs_field(heap, alias_map, ref_counter, false_, field, type_, st);

            Expression::Conditional {
                guard: guard.clone(),
                true_: Box::new(true_),
                false_: Box::new(false_),
                type_: type_.clone(),
            }
        }
        Expression::Lit {
            lit: Lit::NullLit, ..
        } => panic!("infeasible"),
        Expression::Ref { ref_, type_ } => read_field_concrete_ref(heap, *ref_, field),
        sym_ref @ Expression::SymbolicRef { var, type_ } => {
            init_symbolic_reference(heap, alias_map, var, type_, ref_counter, st);
            remove_symbolic_null(alias_map, var);
            let concrete_refs = &alias_map[var];
            dbg!(&alias_map);
            dbg!(&heap);
            read_field_symbolic_ref(heap, concrete_refs, sym_ref, field)
        }
        _ => todo!("Expected reference here, found: {:?}", object),
    }
}

fn true_lit() -> Expression {
    Expression::Lit {
        lit: Lit::BoolLit { bool_value: true },
        type_: RuntimeType::BoolRuntimeType,
    }
}

fn false_lit() -> Expression {
    Expression::Lit {
        lit: Lit::BoolLit { bool_value: false },
        type_: RuntimeType::BoolRuntimeType,
    }
}

fn remove_symbolic_null(alias_map: &mut AliasMap, var: &String) {
    alias_map.get_mut(var).unwrap().retain(|x| match x {
        Expression::Lit {
            lit: Lit::NullLit, ..
        } => false,
        _ => true,
    });
}

fn create_symbolic_var(name: String, type_: RuntimeType) -> Expression {
    match type_ {
        RuntimeType::ReferenceRuntimeType { .. } => Expression::SymbolicRef {
            var: name,
            type_: type_,
        },
        _ => Expression::SymbolicVar {
            var: name,
            type_: type_,
        },
    }
}

fn initialize_symbolic_var(name: &str, type_: &RuntimeType, ref_counter: &mut i64) -> Expression {
    let sym_name = format!("{}{}", name, *ref_counter);
    *ref_counter += 1;
    create_symbolic_var(sym_name, type_.clone())
}

fn verify_file(file_content: &str, method: &str, k: u64) -> SymResult {
    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();

    let c = parse(&tokens);
    let c = c.unwrap();

    // dbg!(&c);

    let mut i = 0;
    let declaration_member_initial_function = c.find_declaration(method).unwrap();
    let symbolic_table = SymbolicTable::from_ast(&c);
    let (result, flw) = labelled_statements(c, &mut i);

    let program = result.into_iter().collect();
    let flows: HashMap<u64, Vec<u64>> = flw
        .iter()
        .group_by(|x| x.0)
        .into_iter()
        .map(|(k, group)| (k, group.map(|(_, x)| *x).collect()))
        .collect();

    let flows: HashMap<u64, Vec<u64>> = utils::group_by(flw.into_iter());

    let pc = find_entry_for_static_invocation(method, &program);

    if let DeclarationMember::Method { params, .. } = &declaration_member_initial_function {
        // dbg!(&params);
        let params = params
            .iter()
            .map(|p| {
                (
                    p.name.clone(),
                    create_symbolic_var(p.name.clone(), p.type_.type_of()),
                )
            })
            .collect();
        // dbg!(&params);

        let mut state = State {
            pc,
            program,
            stack: vec![StackFrame {
                pc,
                t: None,
                params,
                current_member: declaration_member_initial_function,
            }],
            heap: HashMap::new(),
            precondition: true_lit(),
            constraints: HashSet::new(),
            alias_map: HashMap::new(),
            ref_counter: 1,
        };

        return sym_exec(&mut state, &flows, k, &symbolic_table);
    } else {
        panic!()
    }
}

#[test]
fn sym_exec_of_absolute_simplest() {
    let file_content = include_str!("../examples/absolute_simplest.oox");
    assert_eq!(verify_file(file_content, "f", 20), SymResult::Valid);
}

#[test]
fn sym_exec_min() {
    let file_content = include_str!("../examples/psv/min.oox");
    assert_eq!(verify_file(file_content, "min", 20), SymResult::Valid);
}

#[test]
fn sym_exec_method() {
    let file_content = include_str!("../examples/psv/method.oox");
    assert_eq!(verify_file(file_content, "min", 20), SymResult::Valid);
}

#[test]
fn sym_exec_fib() {
    let file_content = std::fs::read_to_string("./examples/psv/fib.oox").unwrap();
    assert_eq!(verify_file(&file_content, "main", 70), SymResult::Valid);
}

// #[test]
// fn sym_idk() {
//     // Expect a panic atm
//     let file_content = std::fs::read_to_string("./examples/psv/test.oox").unwrap();
//     assert_eq!(verify_file(&file_content, "main", 30), SymResult::Invalid);
// }

#[test]
fn sym_exec_div_by_n() {
    let file_content = std::fs::read_to_string("./examples/psv/divByN.oox").unwrap();
    // so this one is invalid at k = 100, in OOX it's invalid at k=105 🤨
    assert_eq!(
        verify_file(&file_content, "divByN_invalid", 30),
        SymResult::Valid
    );
}

#[test]
fn sym_exec_nonstatic_function() {
    let file_content = std::fs::read_to_string("./examples/nonstatic_function.oox").unwrap();
    // so this one is invalid at k = 100, in OOX it's invalid at k=105 🤨
    assert_eq!(verify_file(&file_content, "f", 20), SymResult::Valid);
}

#[test]
fn sym_exec_linked_list1() {
    let file_content = std::fs::read_to_string("./examples/intLinkedList.oox").unwrap();
    assert_eq!(verify_file(&file_content, "test2", 50), SymResult::Valid);
}


// #[test]
// fn sym_exec_linked_list1_invalid() {
//     let file_content = std::fs::read_to_string("./examples/intLinkedList.oox").unwrap();
//     assert_eq!(verify_file(&file_content, "test2_invalid", 50), SymResult::Valid);
// }

#[test]
fn sym_exec_linked_list3() {
    let file_content = std::fs::read_to_string("./examples/intLinkedList.oox").unwrap();
    assert_eq!(verify_file(&file_content, "test3_invalid1", 40), SymResult::Valid);
}