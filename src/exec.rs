use core::panic;
use std::collections::{HashMap, HashSet};

use crate::{
    cfg::CFGStatement,
    stack::StackFrame,
    syntax::{
        BinOp, Expression, Identifier, Lhs, Lit, NonVoidType, Reference, RuntimeType, Statement,
    },
};

type Heap = HashMap<Reference, HeapValue>;

enum HeapValue {
    ObjectValue {
        fields: HashMap<Identifier, Expression>,
        type_: RuntimeType,
    },
    ArrayValue(Vec<Expression>),
}

type PathConstraints = HashSet<Expression>;

// refactor to Vec<Reference>? neins, since it can also be ITE and stuff
type SymbolicToConcrete = HashMap<String, Vec<Expression>>;

enum Output {
    Valid,
    Invalid,
    Unknown,
}

struct State {
    pc: u64,
    program: HashMap<u64, CFGStatement>,
    stack: Vec<StackFrame>,
    heap: Heap,
    precondition: Expression,
    alias_map: SymbolicToConcrete,
}

trait Typeable {
    fn type_of(self) -> RuntimeType;
}

impl Typeable for &NonVoidType {
    fn type_of(self) -> RuntimeType {
        match self {
            NonVoidType::UIntType => RuntimeType::UIntRuntimeType,
            NonVoidType::IntType => RuntimeType::IntRuntimeType,
            NonVoidType::FloatType => RuntimeType::FloatRuntimeType,
            NonVoidType::BoolType => RuntimeType::BoolRuntimeType,
            NonVoidType::StringType => RuntimeType::StringRuntimeType,
            NonVoidType::CharType => RuntimeType::CharRuntimeType,
            NonVoidType::ReferenceType { identifier } => RuntimeType::ReferenceRuntimeType {
                type_: identifier.to_owned(),
            },
            NonVoidType::ArrayType { inner_type } => RuntimeType::ArrayRuntimeType {
                inner_type: Box::new(inner_type.type_of()),
            },
        }
    }
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

fn action(mut state: State, k: u64) {
    let action = &state.program[&state.pc];

    match action {
        CFGStatement::Statement(Statement::Declare { type_, var }) => {
            let StackFrame { pc, t, params } = state.stack.first_mut().unwrap();
            params.insert(var.clone(), default(type_));

            branch()
        }
        CFGStatement::Statement(Statement::Assign { lhs, rhs }) => {
            todo!()
        }
        _ => todo!(),
    }
    todo!()
}

fn read_field_concrete_ref(heap: &mut Heap, ref_: i64, field: Identifier) -> Expression {
    match heap.get_mut(&ref_).unwrap() {
        HeapValue::ObjectValue { fields, type_ } => fields[&field].clone(),
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
    sym_ref: Expression,
    field: Identifier,
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
            true_: Box::new(read_field_concrete_ref(heap, *ref_, field.clone())),
            false_: Box::new(read_field_symbolic_ref(heap, rs, sym_ref.clone(), field)),
            type_: RuntimeType::ANYRuntimeType,
        },
        _ => panic!(),
    }
}

fn write_field_concrete_ref(
    heap: &mut Heap,
    ref_: i64,
    field: Identifier,
    value: Expression,
) -> () {
    // let x = ;

    if let HeapValue::ObjectValue { fields, type_ } = heap.get_mut(&ref_).unwrap() {
        fields.insert(field, value);
    } else {
        panic!("expected object")
    }
}

fn write_field_symbolic_ref(
    heap: &mut Heap,
    concrete_refs: &Vec<Expression>,
    field: Identifier,
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
                        read_field_concrete_ref(heap, *ref_, field.clone()),
                    );
                    write_field_concrete_ref(heap, *ref_, field.clone(), ite)
                } else {
                    panic!("Should only contain refs");
                }
            }
        }
    }
}

fn executeAssign(mut state: State, lhs: Lhs, e: Expression) {
    match lhs {
        Lhs::LhsVar { var, type_ } => {
            let StackFrame { pc, t, params } = state.stack.first_mut().unwrap();
            params.insert(var.clone(), e);
        }
        Lhs::LhsField {
            var,
            var_type,
            field,
            type_,
        } => {
            let StackFrame { pc, t, params } = state.stack.first_mut().unwrap();
            let o = params
                .get(&var)
                .unwrap_or_else(|| panic!("infeasible, object does not exit"));

            let heap = &mut state.heap;

            match o {
                Expression::Ref { ref_, type_ } => {
                    write_field_concrete_ref(heap, *ref_, field, e);
                }
                sym_ref @ Expression::SymbolicRef { var, type_ } => {
                    let concrete_refs = &state.alias_map[var];
                    write_field_symbolic_ref(heap, concrete_refs, field, sym_ref, e);
                }

                _ => todo!(),
            }
            todo!()
        }
        Lhs::LhsElem { var, index, type_ } => todo!(),
    }
}

fn branch() {}
