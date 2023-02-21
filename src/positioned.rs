use crate::syntax::{NonVoidType, Expression, Rhs, Lhs, Invocation, Method};


#[derive(Debug, Clone, Copy)]
pub enum SourcePos {
    UnknownPosition,
    SourcePos {
        line: usize,
        col: usize,
    }
}


pub trait WithPosition {
    fn get_position(&self) -> SourcePos;
}

impl WithPosition for NonVoidType {
    fn get_position(&self) -> SourcePos {
        *match self {
            NonVoidType::UIntType { info } => info,
            NonVoidType::IntType { info } => info,
            NonVoidType::FloatType { info } => info,
            NonVoidType::BoolType { info } => info,
            NonVoidType::StringType { info } => info,
            NonVoidType::CharType { info } => info,
            NonVoidType::ReferenceType { identifier, info } => info,
            NonVoidType::ArrayType { inner_type, info } => info,
        }
    }
}

impl WithPosition for Expression {
    fn get_position(&self) -> SourcePos {
        *match self {
            Expression::Forall { elem, range, domain, formula, type_, info } => info,
            Expression::Exists { elem, range, domain, formula, type_, info } => info,
            Expression::BinOp { bin_op, lhs, rhs, type_, info } => info,
            Expression::UnOp { un_op, value, type_, info } => info,
            Expression::Var { var, type_, info } => info,
            Expression::SymbolicVar { var, type_, info } => info,
            Expression::Lit { lit, type_, info } => info,
            Expression::SizeOf { var, type_, info } => info,
            Expression::Ref { ref_, type_, info } => info,
            Expression::SymbolicRef { var, type_, info } => info,
            Expression::Conditional { guard, true_, false_, type_, info } => info,
        }
    }
}

impl WithPosition for Rhs {
    fn get_position(&self) -> SourcePos {
        *match self {
            Rhs::RhsExpression { value, type_, info } => info,
            Rhs::RhsField { var, field, type_, info } => info,
            Rhs::RhsElem { var, index, type_, info } => info,
            Rhs::RhsCall { invocation, type_, info } => info,
            Rhs::RhsArray { array_type, sizes, type_, info } => info,
        }
    }
}

impl WithPosition for Lhs {
    fn get_position(&self) -> SourcePos {
        match self {
            Lhs::LhsVar { var, type_, info } => *info,
            Lhs::LhsField { var, var_type, field, type_, info } => *info,
            Lhs::LhsElem { var, index, type_, info } => *info,
        }
    }
}

impl WithPosition for Invocation {
    fn get_position(&self) -> SourcePos {
        match self {
            Invocation::InvokeMethod { lhs, rhs, arguments, resolved, info } => *info,
            Invocation::InvokeSuperMethod { rhs, arguments, resolved, info } => *info,
            Invocation::InvokeConstructor { class_name, arguments, resolved, info } => *info,
            Invocation::InvokeSuperConstructor { arguments, resolved, info } => *info,
        }
    }
}

impl WithPosition for Method {
    fn get_position(&self) -> SourcePos {
        self.info
    }
}