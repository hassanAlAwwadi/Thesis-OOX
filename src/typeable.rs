use std::{borrow::Borrow, ops::Deref};

use ordered_float::NotNan;

use crate::{
    exec::HeapValue,
    syntax::{DeclarationMember, Expression, Invocation, Lit, NonVoidType, RuntimeType, Type, Rhs, Lhs, Method}, symbol_table::SymbolTable,
};

pub trait Typeable {
    fn type_of(&self) -> RuntimeType;

    const NUM_TYPES: &'static [RuntimeType] = &[
        RuntimeType::NUMRuntimeType,
        RuntimeType::IntRuntimeType,
        RuntimeType::UIntRuntimeType,
        RuntimeType::FloatRuntimeType,
    ];

    fn is_of_type(&self, other: impl Typeable, st: &SymbolTable) -> bool {
        use RuntimeType::*;
        match (self.type_of(), other.type_of()) {
            (ANYRuntimeType, _) => true,
            (_, ANYRuntimeType) => true,
            (NUMRuntimeType, b) => Self::NUM_TYPES.contains(&b),
            (a, NUMRuntimeType) => Self::NUM_TYPES.contains(&a),
            // matching REF types
            (REFRuntimeType, REFRuntimeType) => true,
            (REFRuntimeType, ReferenceRuntimeType { .. }) => true,
            (REFRuntimeType, ArrayRuntimeType { .. }) => true,
            (REFRuntimeType, StringRuntimeType) => true,
            (REFRuntimeType, ARRAYRuntimeType) => true,
            (ReferenceRuntimeType { .. }, REFRuntimeType) => true,
            (ArrayRuntimeType { .. }, REFRuntimeType) => true,
            (StringRuntimeType, REFRuntimeType) => true,
            (ARRAYRuntimeType, REFRuntimeType) => true,
            // Matching ARRAY types
            (ARRAYRuntimeType, (ArrayRuntimeType { .. })) => true,
            (ArrayRuntimeType { .. }, ARRAYRuntimeType) => true,
            (ReferenceRuntimeType { type_: a }, ReferenceRuntimeType { type_: b}) => st.get_all_instance_types(&b).contains(&a),
            (a, b) => a == b,
        }
    }

    /// Returns the default expression for the type,
    /// For integers this would be 0, etc.
    fn default(&self) -> Expression {
        let type_ = self.type_of();
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
            Forall { type_, .. } => type_,
            Exists { type_, .. } => type_,
            BinOp { type_, .. } => type_,
            UnOp { type_, .. } => type_,
            Var { type_, .. } => type_,
            SymbolicVar { type_, .. } => type_,
            Lit { type_, .. } => type_,
            SizeOf { type_, .. } => type_,
            Ref { type_, .. } => type_,
            SymbolicRef { type_, .. } => type_,
            Conditional { type_, .. } => type_,
        }
        .clone()
    }
}

impl Typeable for &Expression {
    fn type_of(&self) -> RuntimeType {
        use Expression::*;
        match &self {
            Forall { type_, .. } => type_,
            Exists { type_, .. } => type_,
            BinOp { type_, .. } => type_,
            UnOp { type_, .. } => type_,
            Var { type_, .. } => type_,
            SymbolicVar { type_, .. } => type_,
            Lit { type_, .. } => type_,
            SizeOf { type_, .. } => type_,
            Ref { type_, .. } => type_,
            SymbolicRef { type_, .. } => type_,
            Conditional { type_, .. } => type_,
        }
        .clone()
    }
}

impl Typeable for RuntimeType {
    fn type_of(&self) -> RuntimeType {
        self.clone()
    }
}

impl Typeable for DeclarationMember {
    fn type_of(&self) -> RuntimeType {
        use DeclarationMember::*;
        match self {
            Constructor(method) => method.return_type.type_of(),
            Method(method) => method.return_type.type_of(),
            Field { type_, .. } => type_.type_of(),
        }
    }
}

impl Typeable for Type {
    fn type_of(&self) -> RuntimeType {
        self.type_
            .as_ref()
            .map_or(RuntimeType::VoidRuntimeType, |t| t.type_of())
    }
}

impl Typeable for HeapValue {
    fn type_of(&self) -> RuntimeType {
        match self {
            HeapValue::ObjectValue { type_, .. } => type_.clone(),
            HeapValue::ArrayValue { type_, .. } => type_.clone(),
        }
    }
}

pub fn runtime_to_nonvoidtype(type_: RuntimeType) -> Option<NonVoidType> {
    match type_ {
        RuntimeType::UIntRuntimeType => Some(NonVoidType::UIntType),
        RuntimeType::IntRuntimeType => Some(NonVoidType::IntType),
        RuntimeType::FloatRuntimeType => Some(NonVoidType::FloatType),
        RuntimeType::BoolRuntimeType => Some(NonVoidType::BoolType),
        RuntimeType::StringRuntimeType => Some(NonVoidType::StringType),
        RuntimeType::CharRuntimeType => Some(NonVoidType::CharType),
        RuntimeType::ReferenceRuntimeType { type_ } => {
            Some(NonVoidType::ReferenceType { identifier: type_ })
        }
        RuntimeType::ArrayRuntimeType { inner_type } => Some(NonVoidType::ArrayType {
            inner_type: runtime_to_nonvoidtype(*inner_type).map(Box::new)?,
        }),
        _ => None,
    }
}

impl Typeable for Lit {
    fn type_of(&self) -> RuntimeType {
        match self {
            Lit::BoolLit { .. } => RuntimeType::BoolRuntimeType,
            Lit::UIntLit { .. } => RuntimeType::UIntRuntimeType,
            Lit::IntLit { .. } => RuntimeType::IntRuntimeType,
            Lit::FloatLit { .. } => RuntimeType::FloatRuntimeType,
            Lit::StringLit { .. } => RuntimeType::StringRuntimeType,
            Lit::CharLit { .. } => RuntimeType::CharRuntimeType,
            Lit::NullLit => RuntimeType::REFRuntimeType,
        }
    }
}

impl Typeable for Invocation {
    fn type_of(&self) -> RuntimeType {
        match self {
            Invocation::InvokeMethod {
                resolved: Some(resolved),
                ..
            } => {
                let (_, (_, method)) = resolved
                    .iter()
                    .next()
                    .expect("Expected at least one resolved method");
                method.type_of()
            }
            Invocation::InvokeSuperMethod {
                resolved: Some(resolved),
                ..
            } => resolved.1.type_of(),
            Invocation::InvokeConstructor {
                resolved: Some(resolved),
                ..
            } => resolved.1.type_of(),
            Invocation::InvokeSuperConstructor {
                resolved: Some(resolved),
                ..
            } => resolved.1.type_of(),
            _ => panic!("type_of on unresolved invocation"),
        }
    }
}

impl Typeable for Lhs {
    fn type_of(&self) -> RuntimeType {
        match self {
            Lhs::LhsVar { type_, .. } => type_,
            Lhs::LhsField {  type_, .. } => type_,
            Lhs::LhsElem { type_, .. } => type_,
        }.clone()
    }
}

impl Typeable for &Lhs {
    fn type_of(&self) -> RuntimeType {
        match self {
            Lhs::LhsVar { type_, .. } => type_,
            Lhs::LhsField {  type_, .. } => type_,
            Lhs::LhsElem { type_, .. } => type_,
        }.clone()
    }
}

impl Typeable for Rhs {
    fn type_of(&self) -> RuntimeType {
        match self {
            Rhs::RhsExpression { type_, .. } => type_,
            Rhs::RhsField { type_, .. } => type_,
            Rhs::RhsElem { type_, .. } => type_,
            Rhs::RhsCall { type_, .. } => type_,
            Rhs::RhsArray { type_, .. } => type_,
        }.clone()
    }
}

impl Typeable for Method {
    fn type_of(&self) -> RuntimeType {
        self.return_type.type_of()
    }
}