use std::{ops::Deref, borrow::Borrow};

use crate::syntax::{RuntimeType, NonVoidType, Expression};

pub trait Typeable {
    fn type_of(&self) -> RuntimeType;

    const NUM_TYPES: &'static [RuntimeType] = &[RuntimeType::NUMRuntimeType, RuntimeType::IntRuntimeType, RuntimeType::UIntRuntimeType, RuntimeType::FloatRuntimeType];

    fn is_of_type(&self, other: impl Typeable) -> bool {
        use RuntimeType::*;
        match (self.type_of(), other.type_of()) {
            (ANYRuntimeType, _) => true,
            (_, ANYRuntimeType) => true,
            (NUMRuntimeType, b) => Self::NUM_TYPES.contains(&b),
            (a, NUMRuntimeType) => Self::NUM_TYPES.contains(&a),
            // matching REF types
            (REFRuntimeType, REFRuntimeType) => true,
            (REFRuntimeType, ReferenceRuntimeType {..}) => true,
            (REFRuntimeType, ArrayRuntimeType {.. }) => true,
            (REFRuntimeType, StringRuntimeType) => true,
            (REFRuntimeType, ARRAYRuntimeType) => true,
            (ReferenceRuntimeType {..}, REFRuntimeType) => true,
            (ArrayRuntimeType {.. }, REFRuntimeType) => true,
            (StringRuntimeType, REFRuntimeType) => true,
            (ARRAYRuntimeType, REFRuntimeType) => true,
            // Matching ARRAY types
            (ARRAYRuntimeType, (ArrayRuntimeType {..})) => true,
            (ArrayRuntimeType{..}, ARRAYRuntimeType) => true,
            (a, b) => a == b
        }
    }
}

impl<B: Borrow<NonVoidType>> Typeable for B {
    fn type_of(&self) -> RuntimeType {
        match self.borrow() {
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
                inner_type: Box::new(inner_type.as_ref().type_of()),
            },
        }
    }
}


impl Typeable for Expression {
    fn type_of(&self) -> RuntimeType {
        use Expression::*;
        match &self {
            Forall {  type_,.. } => type_,
            Exists { type_ ,.. } => type_,
            BinOp { type_ ,.. } => type_,
            UnOp {  type_ ,.. } => type_,
            Var {  type_ ,.. } => type_,
            SymbolicVar { type_ ,.. } => type_,
            Lit { type_ ,.. } => type_,
            SizeOf {  type_ ,.. } => type_,
            Ref { type_ ,.. } => type_,
            SymbolicRef {  type_ ,.. } => type_,
            Conditional {  type_ ,.. } => type_,
        }.clone()
    }
}