use derivative::Derivative;
use ordered_float::NotNan;

mod identifier;
mod classes;
mod interfaces;

pub use identifier::*;

pub type Reference = i64;

pub type Float = NotNan<f64>;
use std::{
    cell::{Cell, Ref, RefCell},
    collections::HashMap,
    fmt::{Debug, Display},
    ops::Deref,
    rc::{Rc, Weak},
    str::FromStr,
};

use crate::{positioned::SourcePos, typeable::Typeable};

pub use self::{
    classes::Class, interfaces::find_interface_method, interfaces::Interface,
    interfaces::InterfaceMember,
};


#[derive(Debug, Derivative)]
#[derivative(PartialEq, Eq)]
pub struct CompilationUnit {
    pub members: Vec<Declaration>,
}

impl CompilationUnit {
    pub fn find_class_declaration_member(
        &self,
        identifier: &str,
        class_name: Option<&str>,
    ) -> Option<Rc<Method>> {
        for member in &self.members {
            if let Declaration::Class(class) = member {
                if Some(class.name.as_str()) != class_name {
                    continue;
                }
                for declaration_member in &class.members {
                    match declaration_member {
                        DeclarationMember::Constructor(method) if method.name == identifier => {
                            return Some(method.clone());
                        }
                        DeclarationMember::Method(method) if identifier == method.name => {
                            return Some(method.clone());
                        }
                        _ => (),
                    }
                }
            }
        }
        None
    }
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum Declaration {
    Class(Rc<Class>),
    Interface(Rc<Interface>),
}

impl Declaration {
    pub fn try_into_class(&self) -> Option<Rc<Class>> {
        if let Declaration::Class(class) = self {
            Some(class.clone())
        } else {
            None
        }
    }

    pub fn name(&self) -> &Identifier {
        match self {
            Declaration::Class(class) => &class.name,
            Declaration::Interface(interface) => &interface.name,
        }
    }
}

/// Non-abstract, with concrete body
#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub struct Method {
    pub is_static: bool,
    pub return_type: Type,
    pub name: Identifier,
    pub params: Vec<Parameter>,
    pub specification: Specification,
    pub body: RefCell<Statement>, // This is a RefCell to allow interior mutability for inserting the exceptional clauses and types

    #[derivative(PartialEq = "ignore")]
    pub info: SourcePos,
}

impl Method {
    pub fn requires(&self) -> Option<Rc<Expression>> {
        self.specification.requires.clone()
    }

    pub fn post_condition(&self) -> Option<Rc<Expression>> {
        self.specification.ensures.clone()
    }

    pub fn exceptional(&self) -> Option<Rc<Expression>> {
        self.specification.exceptional.clone()
    }
}

/// Abstract method, has no body implementation
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbstractMethod {
    pub is_static: bool,
    pub return_type: Type,
    pub name: Identifier,
    pub params: Vec<Parameter>,
    pub specification: Specification,
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum DeclarationMember {
    /// Note: is_static is always false for constructors
    Constructor(Rc<Method>),
    Method(Rc<Method>),
    Field {
        type_: NonVoidType,
        name: Identifier,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
}

impl DeclarationMember {
    pub fn name(&self) -> &Identifier {
        match &self {
            DeclarationMember::Constructor(method) => &method.name,
            DeclarationMember::Method(method) => &method.name,
            DeclarationMember::Field { name, .. } => name,
        }
    }

    pub fn params(&self) -> Option<&Vec<Parameter>> {
        match &self {
            DeclarationMember::Constructor(method) => Some(&method.params),
            DeclarationMember::Method(method) => Some(&method.params),
            DeclarationMember::Field { .. } => None,
        }
    }

    pub fn method(&self) -> Option<Rc<Method>> {
        match self {
            DeclarationMember::Constructor(method) => Some(method.clone()),
            DeclarationMember::Method(method) => Some(method.clone()),
            DeclarationMember::Field { .. } => None,
        }
    }
    pub fn is_constructor(&self) -> bool {
        if let DeclarationMember::Constructor(_) = self {
            true
        } else {
            false
        }
    }
}

#[derive(Debug, Clone, Derivative)]
#[derive(Eq, PartialEq)]
pub struct Parameter {
    pub type_: NonVoidType,
    pub name: Identifier,

    #[derivative(PartialEq = "ignore")]
    pub info: SourcePos,
}

impl Parameter {
    pub fn new(type_: NonVoidType, name: Identifier) -> Parameter {
        Parameter {
            type_,
            name,
            info: SourcePos::UnknownPosition,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Specification {
    pub requires: Option<Rc<Expression>>,
    pub ensures: Option<Rc<Expression>>,
    pub exceptional: Option<Rc<Expression>>,
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum Statement {
    Declare {
        type_: NonVoidType,
        var: Identifier,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Assign {
        lhs: Lhs,
        rhs: Rhs,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Call {
        invocation: Invocation,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Skip,
    Assert {
        assertion: Expression,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Assume {
        assumption: Expression,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    While {
        guard: Expression,
        body: Box<Statement>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Ite {
        guard: Expression,
        true_body: Box<Statement>,
        false_body: Box<Statement>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Continue {
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Break {
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Return {
        expression: Option<Expression>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Throw {
        message: String,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Try {
        try_body: Box<Statement>,
        catch_body: Box<Statement>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Block {
        body: Box<Statement>,
    },
    Seq {
        stat1: Box<Statement>,
        stat2: Box<Statement>,
    },
}

#[derive(Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum Invocation {
    /// in OOX: `f.method(..), this.method(..), Foo.method(..);`
    InvokeMethod {
        lhs: Identifier,
        rhs: Identifier,
        arguments: Vec<Rc<Expression>>,

        #[derivative(PartialEq = "ignore")]
        resolved: Option<HashMap<Identifier, (Declaration, Rc<Method>)>>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    /// in OOX: `super.method(..);`
    InvokeSuperMethod {
        rhs: Identifier,
        arguments: Vec<Rc<Expression>>,

        #[derivative(PartialEq = "ignore")]
        resolved: Option<Box<(Declaration, Rc<Method>)>>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    /// in OOX: `new Foo(..)`
    InvokeConstructor {
        class_name: Identifier,
        arguments: Vec<Rc<Expression>>,

        #[derivative(PartialEq = "ignore")]
        resolved: Option<Box<(Declaration, Rc<Method>)>>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    /// invocation of the constructor of the superclass. i.e. `super(..);`
    InvokeSuperConstructor {
        arguments: Vec<Rc<Expression>>,

        #[derivative(PartialEq = "ignore")]
        resolved: Option<Box<(Declaration, Rc<Method>)>>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
}

impl Invocation {
    // pub fn resolved(&self) -> Box<dyn Iterator<Item=&(Declaration, Rc<Method>)>> {
    //     match &self {
    //         Invocation::InvokeMethod { resolved, .. } => Box::new(resolved.as_ref().unwrap().iter()),
    //         Invocation::InvokeConstructor { resolved, .. } => {
    //             todo!()
    //             // Box::new(resolved.as_ref().map(Box::as_ref).map(std::iter::once))
    //         },
    //         Invocation::InvokeSuperConstructor { resolved, .. } => {
    //             todo!()
    //             // Box::new(resolved.as_ref().map(Box::as_ref))
    //         },
    //         _ => todo!(),
    //     }
    // }

    pub fn argument_types(&self) -> impl ExactSizeIterator<Item=RuntimeType> + '_ + Clone {
        self
            .arguments()
            .iter()
            .map(AsRef::as_ref)
            .map(Typeable::type_of)
    }

    pub fn arguments(&self) -> &Vec<Rc<Expression>> {
        match &self {
            Invocation::InvokeMethod { arguments, .. } => arguments,
            Invocation::InvokeSuperMethod { arguments, .. } => arguments,
            Invocation::InvokeConstructor { arguments, .. } => arguments,
            Invocation::InvokeSuperConstructor { arguments, .. } => arguments,
        }
    }

    pub fn identifier(&self) -> &Identifier {
        match &self {
            Invocation::InvokeMethod { rhs, .. } => rhs,
            Invocation::InvokeConstructor { class_name, .. } => class_name,
            Invocation::InvokeSuperMethod { rhs, .. } => rhs,
            _ => panic!("Invocation of super(); - does not have an identifier"),
        }
    }
}

impl Debug for Invocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvokeMethod {
                lhs,
                rhs,
                arguments,
                resolved,
                info,
            } => f
                .debug_struct("InvokeMethod")
                .field("lhs", lhs)
                .field("rhs", rhs)
                .field("arguments", arguments)
                .field("resolved", &resolved.is_some())
                .finish(),
            Self::InvokeSuperMethod {
                rhs,
                arguments,
                resolved,
                info,
            } => f
                .debug_struct("InvokeSuperMethod")
                .field("rhs", rhs)
                .field("arguments", arguments)
                .field("resolved", &resolved.is_some())
                .finish(),
            Self::InvokeConstructor {
                class_name,
                arguments,
                resolved,
                info,
            } => f
                .debug_struct("InvokeConstructor")
                .field("class_name", class_name)
                .field("arguments", arguments)
                .field("resolved", &resolved.is_some())
                .finish(),
            Self::InvokeSuperConstructor {
                arguments,
                resolved,
                info,
            } => f
                .debug_struct("InvokeSuperConstructor")
                .field("arguments", arguments)
                .field("resolved", &resolved.is_some())
                .finish(),
        }
    }
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum Lhs {
    LhsVar {
        var: Identifier,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    LhsField {
        var: Identifier,
        var_type: RuntimeType,
        field: Identifier,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    LhsElem {
        var: Identifier,
        index: Rc<Expression>,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum Rhs {
    RhsExpression {
        value: Expression,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    RhsField {
        var: Expression,
        field: Identifier,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    RhsElem {
        var: Expression,
        index: Expression,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    RhsCall {
        invocation: Invocation,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    RhsArray {
        array_type: NonVoidType,
        sizes: Vec<Expression>,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
}

#[derive(Clone, Derivative)]
#[derivative(PartialEq, Hash, Eq)]
pub enum Expression {
    Forall {
        elem: Identifier,
        range: Identifier,
        domain: Identifier,
        formula: Box<Expression>,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    Exists {
        elem: Identifier,
        range: Identifier,
        domain: Identifier,
        formula: Box<Expression>,
        type_: RuntimeType,
        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    BinOp {
        bin_op: BinOp,
        lhs: Rc<Expression>,
        rhs: Rc<Expression>,
        type_: RuntimeType,
        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    UnOp {
        un_op: UnOp,
        value: Rc<Expression>,
        type_: RuntimeType,
        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    Var {
        var: Identifier,
        type_: RuntimeType,
        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    SymbolicVar {
        // symbolic variables of primitives such as integers, boolean, floats
        var: Identifier,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    Lit {
        lit: Lit,
        type_: RuntimeType,

        #[derivative(Hash = "ignore", PartialEq = "ignore")]
        info: SourcePos,
    },
    SizeOf {
        var: Identifier,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    Ref {
        ref_: Reference,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    SymbolicRef {
        // symbolic references to arrays, objects
        var: Identifier,
        type_: RuntimeType, // If this is REFRuntimeType, this means that we have different types in the aliasmap and a state split may be necessary if we invoke a method

        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    Conditional {
        guard: Rc<Expression>,
        true_: Rc<Expression>,
        false_: Rc<Expression>,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
}

impl Expression {
    pub const TRUE: Expression = Expression::Lit {
        lit: Lit::BoolLit { bool_value: true },
        type_: RuntimeType::BoolRuntimeType,
        info: SourcePos::UnknownPosition,
    };
    pub const FALSE: Expression = Expression::Lit {
        lit: Lit::BoolLit { bool_value: false },
        type_: RuntimeType::BoolRuntimeType,
        info: SourcePos::UnknownPosition,
    };

    pub const NULL: Expression = Expression::Lit {
        lit: Lit::NullLit,
        type_: RuntimeType::REFRuntimeType,
        info: SourcePos::UnknownPosition,
    };

    pub fn bool(v: bool) -> Rc<Expression> {
        if v {
            Rc::new(Expression::TRUE)
        } else {
            Rc::new(Expression::FALSE)
        }
    }

    pub fn int(v: i64) -> Rc<Expression> {
        Rc::new(Expression::Lit {
            lit: Lit::IntLit { int_value: v },
            type_: RuntimeType::IntRuntimeType,
            info: SourcePos::UnknownPosition,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    Implies,
    And,
    Or,
    Equal,
    NotEqual,
    LessThan,
    LessThanEqual,
    GreaterThan,
    GreaterThanEqual,
    Plus,
    Minus,
    Multiply,
    Divide,
    Modulo,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnOp {
    Negative,
    Negate,
}

#[derive(Debug, Clone, PartialEq, Hash)]
pub enum Lit {
    BoolLit { bool_value: bool },
    UIntLit { uint_value: u64 },
    IntLit { int_value: i64 },
    FloatLit { float_value: Float },
    StringLit { string_value: String },
    CharLit { char_value: char },
    NullLit,
}

impl Eq for Lit {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type {
    pub type_: Option<NonVoidType>,
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum NonVoidType {
    UIntType {
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    IntType {
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    FloatType {
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    BoolType {
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    StringType {
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    CharType {
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    ReferenceType {
        identifier: Identifier,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    ArrayType {
        inner_type: Box<NonVoidType>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
}

// how is this used during parsing? or is it only used during execution
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RuntimeType {
    UnknownRuntimeType,
    VoidRuntimeType,
    UIntRuntimeType,
    IntRuntimeType,
    FloatRuntimeType,
    BoolRuntimeType,
    StringRuntimeType,
    CharRuntimeType,
    ReferenceRuntimeType { type_: Identifier },
    ArrayRuntimeType { inner_type: Box<RuntimeType> },
    ANYRuntimeType,
    NUMRuntimeType,
    REFRuntimeType, // is this symbolic or something? why not use ReferenceRuntimeType
    ARRAYRuntimeType,
}

impl RuntimeType {
    /// Assumes this is a ReferenceRuntimeType and returns identifier of the reference class
    pub fn as_reference_type(&self) -> Option<&Identifier> {
        if let RuntimeType::ReferenceRuntimeType { type_ } = self {
            return Some(type_);
        }
        None
    }

    pub fn get_reference_type(&self) -> Option<Identifier> {
        self.as_reference_type().cloned()
    }

    pub fn get_inner_array_type(&self) -> Option<RuntimeType> {
        if let RuntimeType::ArrayRuntimeType { inner_type } = self {
            return Some(inner_type.deref().clone());
        }
        None
    }
}
