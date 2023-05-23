use std::fmt::Display;
use std::rc::Rc;

use itertools::Either;

use crate::syntax::{Expression, Invocation, Lhs, Method, NonVoidType, Rhs};
use crate::{TypeExpr, FILE_NAMES};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum SourcePos {
    UnknownPosition,
    SourcePos {
        line: usize,
        col: usize,
        /// Ideally this would be a &str, but due to borrowing we would need to add lifetimes everywhere.
        file_number: usize,
    },
}

impl SourcePos {
    pub fn new(line: usize, col: usize, file_number: usize) -> SourcePos {
        SourcePos::SourcePos {
            line,
            col,
            file_number,
        }
    }
}

impl Display for SourcePos {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let SourcePos::SourcePos {
            line,
            col,
            file_number,
        } = self
        {
            let paths = FILE_NAMES.lock().unwrap();
            write!(
                f,
                "{}:{}:{}",
                paths.get(*file_number).map(AsRef::as_ref).unwrap_or("?"),
                line,
                col
            )
        } else {
            Ok(())
        }
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
            NonVoidType::ReferenceType { info, .. } => info,
            NonVoidType::ArrayType { info, .. } => info,
        }
    }
}

impl WithPosition for Expression {
    fn get_position(&self) -> SourcePos {
        *match self {
            Expression::Forall { info, .. } => info,
            Expression::Exists { info, .. } => info,
            Expression::BinOp { info, .. } => info,
            Expression::UnOp { info, .. } => info,
            Expression::Var { info, .. } => info,
            Expression::SymbolicVar { info, .. } => info,
            Expression::Lit { info, .. } => info,
            Expression::SizeOf { info, .. } => info,
            Expression::Ref { info, .. } => info,
            Expression::SymbolicRef { info, .. } => info,
            Expression::Conditional { info, .. } => info,
        }
    }
}

impl WithPosition for Rhs {
    fn get_position(&self) -> SourcePos {
        *match self {
            Rhs::RhsExpression { info, .. } => info,
            Rhs::RhsField { info, .. } => info,
            Rhs::RhsElem { info, .. } => info,
            Rhs::RhsCall { info, .. } => info,
            Rhs::RhsArray { info, .. } => info,
            Rhs::RhsCast { info, .. } => info,
        }
    }
}

impl WithPosition for &Rhs {
    fn get_position(&self) -> SourcePos {
        Rhs::get_position(self)
    }
}

impl WithPosition for Lhs {
    fn get_position(&self) -> SourcePos {
        match self {
            Lhs::LhsVar { info, .. } => *info,
            Lhs::LhsField { info, .. } => *info,
            Lhs::LhsElem { info, .. } => *info,
        }
    }
}

impl WithPosition for &Lhs {
    fn get_position(&self) -> SourcePos {
        match self {
            Lhs::LhsVar { info, .. } => *info,
            Lhs::LhsField { info, .. } => *info,
            Lhs::LhsElem { info, .. } => *info,
        }
    }
}

impl WithPosition for Invocation {
    fn get_position(&self) -> SourcePos {
        match self {
            Invocation::InvokeMethod { info, .. } => *info,
            Invocation::InvokeSuperMethod { info, .. } => *info,
            Invocation::InvokeConstructor { info, .. } => *info,
            Invocation::InvokeSuperConstructor { info, .. } => *info,
        }
    }
}

impl WithPosition for Method {
    fn get_position(&self) -> SourcePos {
        self.info
    }
}

impl WithPosition for &Expression {
    fn get_position(&self) -> SourcePos {
        match self {
            Expression::Forall { info, .. } => *info,
            Expression::Exists { info, .. } => *info,
            Expression::BinOp { info, .. } => *info,
            Expression::UnOp { info, .. } => *info,
            Expression::Var { info, .. } => *info,
            Expression::SymbolicVar { info, .. } => *info,
            Expression::Lit { info, .. } => *info,
            Expression::SizeOf { info, .. } => *info,
            Expression::Ref { info, .. } => *info,
            Expression::SymbolicRef { info, .. } => *info,
            Expression::Conditional { info, .. } => *info,
        }
    }
}

impl WithPosition for Either<Rc<Expression>, TypeExpr> {
    fn get_position(&self) -> SourcePos {
        match self {
            Either::Left(guard) => guard.get_position(),
            Either::Right(guard) => guard.get_position(),
        }
    }
}

impl WithPosition for TypeExpr {
    fn get_position(&self) -> SourcePos {
        match self {
            TypeExpr::InstanceOf { info, .. } => *info,
            TypeExpr::NotInstanceOf { info, .. } => *info,
        }
    }
}

impl WithPosition for &TypeExpr {
    fn get_position(&self) -> SourcePos {
        match self {
            TypeExpr::InstanceOf { info, .. } => *info,
            TypeExpr::NotInstanceOf { info, .. } => *info,
        }
    }
}
