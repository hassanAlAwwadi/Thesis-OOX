use core::panic;
use std::collections::{HashMap, HashSet};

use itertools::Itertools;
use ordered_float::NotNan;
use z3::SatResult;

use crate::{
    cfg::{labelled_statements, CFGStatement},
    dsl::neg,
    eval::{self, evaluate},
    lexer::tokens,
    parser_pom::parse,
    stack::{lookup_in_stack, StackFrame},
    syntax::{
        BinOp, DeclarationMember, Expression, Identifier, Invocation, Lhs, Lit, NonVoidType,
        Parameter, Reference, Rhs, RuntimeType, Statement, UnOp,
    },
    typeable::Typeable,
    z3_checker, utils,
};

fn retval() -> String {
    "retval".to_string()
}

pub type Heap = HashMap<Reference, HeapValue>;

#[derive(Clone)]
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

fn sym_exec(state: &mut State, flows: &HashMap<u64, Vec<u64>>, k: u64) -> SymResult {
    if k == 0 {
        // finishing current branch
        dbg!("FINITO");
        return SymResult::Valid;
    }
    let next = action(state, k);

    // dbg!(&state.pc);

    match next {
        ActionResult::FunctionCall(next) => {
            // function call or return
            state.pc = next;
            sym_exec(state, flows, k - 1);
        }
        ActionResult::Return(return_pc) => {
            if let Some(neighbours) = flows.get(&return_pc) {
                for neighbour_pc in neighbours {
                    let mut new_state = state.clone();
                    new_state.pc = *neighbour_pc;

                    let result = sym_exec(&mut new_state, flows, k - 1);
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
                // dbg!(&neighbours);
                for neighbour_pc in neighbours {
                    let mut new_state = state.clone();
                    new_state.pc = *neighbour_pc;

                    let result = sym_exec(&mut new_state, flows, k - 1);
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
                );
            }
            let value = evaluateRhs(heap, stack, alias_map, ref_counter, rhs);
            let e = evaluate(heap, stack, alias_map, &value, ref_counter);
            execute_assign(heap, stack, alias_map, ref_counter, lhs, e);

            ActionResult::Continue
        }
        CFGStatement::Statement(Statement::Assert { assertion }) => {
            let expression =
                exec_assert(&constraints, assertion, heap, stack, alias_map, ref_counter);
            if expression == true_lit() {
                panic!("invalid");
            } else if expression == false_lit() {
                ActionResult::Continue
            } else {
                dbg!("invoke Z3 with:", &expression);
                let result = z3_checker::verify(&expression);
                if let SatResult::Unsat = result {
                } else {
                    panic!("invalid")
                }

                ActionResult::Continue
            }
        }
        CFGStatement::Statement(Statement::Assume { assumption }) => {
            let expression = evaluate(heap, stack, alias_map, assumption, ref_counter);
            dbg!(&assumption, &expression, stack.last().map(|s| &s.params));
            if expression == false_lit() {
                panic!("infeasible");
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
                exec_assert(constraints, requires, heap, stack, alias_map, ref_counter);
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
                );
                // some if true then unfeasible/invalid or something?
            }
            if stack.len() == 1 {
                ActionResult::Continue
                // we are pbobably done now
            } else {

            
                let rv = stack.last().unwrap().params.get(&retval()).unwrap();
                let return_value = evaluate(heap, stack, alias_map, rv, ref_counter);

                let StackFrame { pc, t,  .. } = stack.pop().unwrap();
                if let Some(lhs) = t {
                    // perhaps also write retval to current stack?
                    // will need to do this due to this case: `return o.func();`

                    execute_assign(heap, stack, alias_map, ref_counter, &lhs, return_value);
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
) -> ActionResult {
    let (declaration, member) = invocation.resolved().unwrap(); // i don't get this

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
                .map(|arg| evaluate(heap, stack, alias_map, arg, ref_counter))
                .collect::<Vec<_>>();

            exec_static_method(stack, return_point, member.clone(), lhs, &arguments, params);
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
        } => todo!(),
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

fn exec_static_method(
    stack: &mut Vec<StackFrame>,
    return_point: u64,
    member: DeclarationMember,
    lhs: Option<Lhs>,
    arguments: &[Expression],
    parameters: &[Parameter],
) {
    push_stack_frame(
        stack,
        return_point,
        member,
        lhs,
        parameters.iter().zip(arguments.iter()),
    )
}

fn push_stack_frame<'a, P>(
    stack: &mut Vec<StackFrame>,
    return_point: u64,
    member: DeclarationMember,
    lhs: Option<Lhs>,
    params: P,
) where
    P: Iterator<Item = (&'a Parameter, &'a Expression)>,
{
    let params = params.map(|(p, e)| (p.name.clone(), e.clone())).collect();
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

        neg(Expression::BinOp {
            bin_op: BinOp::Implies,
            lhs: Box::new(assumptions),
            rhs: Box::new(assertion.clone()),
            type_: RuntimeType::BoolRuntimeType,
        })
    } else {
        neg(assertion.clone())
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
    // dbg!(&expression);
    let z = evaluate(heap, stack, alias_map, &expression, ref_counter);
    // dbg!(&z);
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

pub fn init(
    heap: &mut Heap,
    alias_map: &mut AliasMap,
    sym_ref: &Identifier,
    type_ref: &RuntimeType,
    ref_counter: &mut i64,
) {
    if !alias_map.contains_key(sym_ref) {
        let ref_fresh = *ref_counter;
        *ref_counter += 1;
        heap.insert(ref_fresh, HeapValue::empty_object());

        // Find all other possible concrete references of the same type as sym_ref

        let existing_aliases = alias_map
            .values()
            .filter(|x| x.iter().any(|x| x.type_of() == *type_ref))
            .flat_map(|x| x.iter());

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
                    init(heap, alias_map, var, type_, ref_counter);
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
) -> Expression {
    match rhs {
        Rhs::RhsExpression { value, type_ } => {
            match value {
                Expression::Var { var, type_ } => lookup_in_stack(var, stack).unwrap().clone(),
                _ => value.clone(), // might have to expand on this when dealing with complex quantifying expressions and array
            }
        }
        Rhs::RhsField { var, field, type_ } => {
            exec_rhs_field(heap, stack, alias_map, ref_counter, var, field, type_)
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
    stack: &mut Vec<StackFrame>,
    alias_map: &mut AliasMap,
    ref_counter: &mut i64,
    var: &Expression,
    field: &Identifier,
    type_: &RuntimeType,
) -> Expression {
    let StackFrame { pc, t, params, .. } = stack.last_mut().unwrap();
    match var {
        Expression::Conditional {
            guard,
            true_,
            false_,
            type_,
        } => {
            // bedoelt hij hier niet exec true_ ipv execField true_ ?
            // nope want hij wil nog steeds het field weten ervan
            let true_ = exec_rhs_field(heap, stack, alias_map, ref_counter, true_, field, type_);
            let false_ = exec_rhs_field(heap, stack, alias_map, ref_counter, false_, field, type_);

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
            init(heap, alias_map, var, type_, ref_counter);
            let concrete_refs = &alias_map[var];
            read_field_symbolic_ref(heap, concrete_refs, sym_ref, field)
        }
        _ => todo!("Expected reference here"),
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

fn verify_file(file_content: &str, method: &str, k: u64) -> SymResult {
    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();

    let c = parse(&tokens);
    let c = c.unwrap();

    // dbg!(&c);

    let mut i = 0;
    let declaration_member_initial_function = c.find_declaration(method).unwrap();
    let (result, flw) = labelled_statements(c, &mut i);

    let program = result.into_iter().collect();
    let flows: HashMap<u64, Vec<u64>> = flw
        .iter()
        .group_by(|x| x.0)
        .into_iter()
        .map(|(k, group)| (k, group.map(|(_, x)| *x).collect()))
        .collect();


    let flows: HashMap<u64, Vec<u64>> = utils::group_by(flw.into_iter());
    dbg!(&flows);
    // dbg!(&program);

    let pc = find_entry_for_static_invocation(method, &program);

    if let DeclarationMember::Method { params, .. } = &declaration_member_initial_function {
        let params = params
            .iter()
            .map(|p| {
                (
                    p.name.clone(),
                    Expression::SymbolicVar {
                        var: p.name.clone(),
                        type_: p.type_.type_of(),
                    },
                )
            })
            .collect();

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
            ref_counter: 0,
        };

        return sym_exec(&mut state, &flows, k);
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


#[test]
fn sym_idk() {
    let file_content = std::fs::read_to_string("./examples/psv/test.oox").unwrap();
    assert_eq!(verify_file(&file_content, "main", 30), SymResult::Valid);
}
