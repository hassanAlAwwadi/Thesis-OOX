use std::collections::{HashSet, HashMap};

use crate::{syntax::{Expression, Statement, RuntimeType, Lit}, cfg::CFGStatement, stack::StackFrame};



type Heap = ();


type PathConstraints = HashSet<Expression>;

type SymbolicToConcrete = HashMap<String, Vec<String>>;

enum Output {
    Valid,
    Invalid,
    Unknown
}

struct State {
    pc: u64,
    program: HashMap<u64, CFGStatement>,
    stack: Vec<StackFrame>,
    heap: Heap,
    precondition: Expression, 
    alias_map: SymbolicToConcrete
}

trait Typeable {
    fn type_of(self) -> RuntimeType;
}



fn defaultValue<T: Typeable>(t: T) -> Expression {
    let type_ = t.type_of();
    let lit = 
    match type_ {
        RuntimeType::UIntRuntimeType => Lit::UIntLit { uint_value: 0 },
        RuntimeType::IntRuntimeType => Lit::IntLit { int_value: 0 },
        RuntimeType::FloatRuntimeType => Lit::FloatLit { float_value: 0. },
        RuntimeType::BoolRuntimeType => Lit::BoolLit { bool_value: false },
        RuntimeType::ARRAYRuntimeType => Lit::NullLit,
        RuntimeType::StringRuntimeType => Lit::NullLit,
        RuntimeType::CharRuntimeType => Lit::CharLit { char_value: '\0' },
        RuntimeType::ReferenceRuntimeType { .. } => Lit::NullLit,
        RuntimeType::ArrayRuntimeType { .. } => Lit::NullLit,
        RuntimeType::ANYRuntimeType => todo!(),
        RuntimeType::NUMRuntimeType => todo!(),
        RuntimeType::REFRuntimeType => todo!(),
        RuntimeType::VoidRuntimeType => todo!(),
        RuntimeType::UnknownRuntimeType => todo!(),
    };

    Expression::Lit {
        lit,
        type_,
    }
}


fn execute(state: State, k: u64) -> Output {
    if k == 0 {
        return Output::Valid;
    }



    todo!()
}

fn executeAction(state: State, k: u64) {
    let statement = &state.program[&state.pc];

    match statement {
        CFGStatement::Statement(Statement::Declare { type_, var }) => {

        },
        _ => todo!()
    }
}

// fn execute_declare(state: State, )