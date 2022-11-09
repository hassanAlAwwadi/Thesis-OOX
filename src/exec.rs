use core::panic;
use std::collections::{HashMap, HashSet};

use crate::{
    cfg::CFGStatement,
    stack::StackFrame,
    syntax::{
        BinOp, Expression, Identifier, Lhs, Lit, NonVoidType, Reference, Rhs, RuntimeType,
        Statement, UnOp,
    },
    typeable::Typeable,
};

pub type Heap = HashMap<Reference, HeapValue>;

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
        RuntimeType::FloatRuntimeType => Lit::FloatLit { float_value: 0. },
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

fn sym_exec(state: State, k: u64) {}

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
) {
    let action = &program[&pc];

    match action {
        CFGStatement::Statement(Statement::Declare { type_, var }) => {
            let StackFrame { pc, t, params } = stack.first_mut().unwrap();
            params.insert(var.clone(), default(type_));

            branch()
        }
        CFGStatement::Statement(Statement::Assign { lhs, rhs }) => {
            if let Rhs::RhsCall { .. } = rhs {
                return branch();
            }
            let value = evaluateRhs(heap, stack, alias_map, ref_counter, rhs);
            execute_assign(heap, stack, alias_map, ref_counter, lhs, &value);

            branch()
        }
        CFGStatement::Statement(Statement::Assert { assertion }) => {
            let exp = constraints.iter().fold(
                Expression::UnOp {
                    un_op: UnOp::Negative,
                    value: Box::new(assertion.clone()),
                    type_: RuntimeType::BoolRuntimeType,
                },
                |x, b| Expression::BinOp {
                    bin_op: BinOp::And,
                    lhs: Box::new(x),
                    rhs: Box::new(b.clone()),
                    type_: RuntimeType::BoolRuntimeType,
                },
            );
            if exp == (Expression::Lit  { lit: Lit::BoolLit { bool_value: true }, type_: RuntimeType::BoolRuntimeType }) {
                panic!("invalid");
            } else if exp == (Expression::Lit  { lit: Lit::BoolLit { bool_value: false }, type_: RuntimeType::BoolRuntimeType }) {
                branch();
            } else {
                dbg!("invoke Z3 with:", exp);
                branch()
            }
        }
        _ => todo!(),
    }
    todo!()
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
    value: &Expression,
) -> () {
    match concrete_refs.as_slice() {
        [] => panic!(),
        [Expression::Ref { ref_, type_ }] => {
            write_field_concrete_ref(heap, *ref_, field, value.clone());
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
    e: &Expression,
) {
    match lhs {
        Lhs::LhsVar { var, type_ } => {
            let StackFrame { pc, t, params } = stack.first_mut().unwrap();
            params.insert(var.clone(), e.clone());
        }
        Lhs::LhsField {
            var,
            var_type,
            field,
            type_,
        } => {
            let StackFrame { pc, t, params } = stack.first_mut().unwrap();
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
            let StackFrame { pc, t, params } = stack.first_mut().unwrap();
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
            value.clone() // for now no simplification
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
    let StackFrame { pc, t, params } = stack.first_mut().unwrap();
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

fn branch() {}
