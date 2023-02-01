use ordered_float::NotNan;

pub type Identifier = String;
pub type Reference = i64;

pub type Float = NotNan<f64>;
use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
    fmt::{Debug, Display},
    rc::{Rc, Weak},
};

use self::interfaces::InterfaceMembers;
pub use self::{interfaces::Interface, classes::Class};

mod interfaces;
mod classes;


#[derive(Debug)]
pub struct CompilationUnit<D = Declaration> {
    pub members: Vec<D>,
}

impl CompilationUnit {
    pub fn find_class_declaration_member(
        &self,
        identifier: &str,
        class_name: Option<&str>,
    ) -> Option<Rc<DeclarationMember>> {
        for member in &self.members {
            if let Declaration::Class(class)  = member {
                if Some(class.name.as_str()) != class_name {
                    continue;
                }
                for declaration_member in &class.members {
                    match declaration_member.as_ref() {
                        DeclarationMember::Constructor { name, .. } if identifier == name => {
                            return Some(declaration_member.clone());
                        }
                        DeclarationMember::Method { name, .. } if identifier == name => {
                            return Some(declaration_member.clone());
                        }
                        _ => (),
                    }
                }
            }
        }
        None
    }
}


#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Declaration {
    Class(Rc<Class>),
    Interface(Rc<Interface>),
}

impl Declaration {
    pub fn as_class(&self) -> Option<Rc<Class>> {
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

/// Intermediate state, where the Declaration does not know the declarations of its extends and implements
/// After resolving this will be replaced with a Declaration in the syntax tree.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum UnresolvedDeclaration {
    Class(UnresolvedClass),
    Interface(UnresolvedInterface)
}
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct UnresolvedClass {
    pub name: Identifier,
    pub extends: Option<Identifier>,
    pub implements: Vec<Identifier>,
    pub members: Vec<Rc<DeclarationMember>>,
}
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct UnresolvedInterface  {
    pub name: Identifier,
    pub extends: Vec<Identifier>,
    pub members: Vec<Rc<InterfaceMembers>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclarationMember {
    Constructor {
        name: Identifier,
        params: Vec<Parameter>,
        specification: Specification,
        body: Statement,
    },
    Method {
        is_static: bool,
        return_type: Type,
        name: Identifier,
        params: Vec<Parameter>,
        specification: Specification,
        body: Statement,
    },
    Field {
        type_: NonVoidType,
        name: Identifier,
    },
}

impl DeclarationMember {
    fn specification(&self) -> Option<&Specification> {
        match &self {
            DeclarationMember::Constructor { specification, .. } => Some(specification),
            DeclarationMember::Method { specification, .. } => Some(specification),
            DeclarationMember::Field { .. } => None,
        }
    }

    pub fn requires(&self) -> Option<Rc<Expression>> {
        self.specification().and_then(|s| s.requires.clone())
    }

    pub fn post_condition(&self) -> Option<Rc<Expression>> {
        self.specification().and_then(|s| s.ensures.clone())
    }

    pub fn exceptional(&self) -> Option<Rc<Expression>> {
        self.specification().and_then(|s| s.exceptional.clone())
    }

    pub fn name(&self) -> &Identifier {
        match &self {
            DeclarationMember::Constructor { name, .. } => name,
            DeclarationMember::Method { name, .. } => name,
            DeclarationMember::Field { name, .. } => name,
        }
    }

    pub fn params(&self) -> Option<&Vec<Parameter>> {
        match &self {
            DeclarationMember::Constructor { params, .. } => Some(params),
            DeclarationMember::Method { params, .. } => Some(params),
            DeclarationMember::Field { .. } => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parameter {
    pub type_: NonVoidType,
    pub name: Identifier,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Specification {
    pub requires: Option<Rc<Expression>>,
    pub ensures: Option<Rc<Expression>>,
    pub exceptional: Option<Rc<Expression>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    Declare {
        type_: NonVoidType,
        var: Identifier,
    },
    Assign {
        lhs: Lhs,
        rhs: Rhs,
    },
    Call {
        invocation: Invocation,
    },
    Skip,
    Assert {
        assertion: Expression,
    },
    Assume {
        assumption: Expression,
    },
    While {
        guard: Expression,
        body: Box<Statement>,
    },
    Ite {
        guard: Expression,
        true_body: Box<Statement>,
        false_body: Box<Statement>,
    },
    Continue,
    Break,
    Return {
        expression: Option<Expression>,
    },
    Throw {
        message: String,
    },
    Try {
        try_body: Box<Statement>,
        catch_body: Box<Statement>,
    },
    Block {
        body: Box<Statement>,
    },
    Seq {
        stat1: Box<Statement>,
        stat2: Box<Statement>,
    },
}

#[derive(Clone, PartialEq, Eq)]
pub enum Invocation {
    InvokeMethod {
        // f.method(..), this.method(..), Foo.method(..);
        lhs: Identifier,
        rhs: Identifier,
        arguments: Vec<Expression>,
        resolved: Option<HashMap<Identifier, (Declaration, Rc<DeclarationMember>)>>, // What is this? -- potential case for Weak<..>
    },
    InvokeSuperMethod {
        // super.method(..);
        rhs: Identifier,
        arguments: Vec<Expression>,
        resolved: Option<Box<(Declaration, Rc<DeclarationMember>)>>,
    },
    InvokeConstructor {
        // new Foo(..)
        class_name: Identifier,
        arguments: Vec<Expression>,
        resolved: Option<Box<(Declaration, Rc<DeclarationMember>)>>, // What is this?
    },
    InvokeSuperConstructor {
        // super(..);
        arguments: Vec<Expression>,
        resolved: Option<Box<(Declaration, Rc<DeclarationMember>)>>,
    },
}

impl Invocation {
    // pub fn resolved(&self) -> impl Iterator<Item=&(Declaration, DeclarationMember)>{
    //     match &self {
    //         Invocation::InvokeMethod { resolved, .. } => resolved.as_ref().unwrap().iter(),
    //         Invocation::InvokeConstructor { resolved, .. } => resolved.as_ref().map(Box::as_ref).map(std::iter::once),
    //         Invocation::InvokeSuperConstructor { resolved, .. } => {
    //             resolved.as_ref().map(Box::as_ref)
    //         }
    //     }
    // }

    pub fn arguments(&self) -> &Vec<Expression> {
        match &self {
            Invocation::InvokeMethod { arguments, .. } => arguments.as_ref(),
            Invocation::InvokeSuperMethod { arguments, .. } => arguments.as_ref(),
            Invocation::InvokeConstructor { arguments, .. } => arguments.as_ref(),
            Invocation::InvokeSuperConstructor { arguments, .. } => arguments.as_ref(),
        }
    }

    pub fn identifier(&self) -> &String {
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
            } => f
                .debug_struct("InvokeConstructor")
                .field("class_name", class_name)
                .field("arguments", arguments)
                .field("resolved", &resolved.is_some())
                .finish(),
            Self::InvokeSuperConstructor {
                arguments,
                resolved,
            } => f
                .debug_struct("InvokeSuperConstructor")
                .field("arguments", arguments)
                .field("resolved", &resolved.is_some())
                .finish(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lhs {
    LhsVar {
        var: Identifier,
        type_: RuntimeType,
    },
    LhsField {
        var: Identifier,
        var_type: RuntimeType,
        field: Identifier,
        type_: RuntimeType,
    },
    LhsElem {
        var: Identifier,
        index: Rc<Expression>,
        type_: RuntimeType,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Rhs {
    RhsExpression {
        value: Expression,
        type_: RuntimeType,
    },
    RhsField {
        var: Expression,
        field: Identifier,
        type_: RuntimeType,
    },
    RhsElem {
        var: Expression,
        index: Expression,
        type_: RuntimeType,
    },
    RhsCall {
        invocation: Invocation,
        type_: RuntimeType,
    },
    RhsArray {
        array_type: NonVoidType,
        sizes: Vec<Expression>,
        type_: RuntimeType,
    },
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Expression {
    Forall {
        elem: Identifier,
        range: Identifier,
        domain: Identifier,
        formula: Box<Expression>,
        type_: RuntimeType,
    },
    Exists {
        elem: Identifier,
        range: Identifier,
        domain: Identifier,
        formula: Box<Expression>,
        type_: RuntimeType,
    },
    BinOp {
        bin_op: BinOp,
        lhs: Rc<Expression>,
        rhs: Rc<Expression>,
        type_: RuntimeType,
    },
    UnOp {
        un_op: UnOp,
        value: Rc<Expression>,
        type_: RuntimeType,
    },
    Var {
        var: Identifier,
        type_: RuntimeType,
    },
    SymbolicVar {
        // symbolic variables of primitives such as integers, boolean, floats
        var: Identifier,
        type_: RuntimeType,
    },
    Lit {
        lit: Lit,
        type_: RuntimeType,
    },
    SizeOf {
        var: Identifier,
        type_: RuntimeType,
    },
    Ref {
        ref_: Reference,
        type_: RuntimeType,
    },
    SymbolicRef {
        // symbolic references to arrays, objects
        var: Identifier,
        type_: RuntimeType, // If this is REFRuntimeType, this means that we have different types in the aliasmap and a state split may be necessary if we invoke a method
    },
    Conditional {
        guard: Rc<Expression>,
        true_: Rc<Expression>,
        false_: Rc<Expression>,
        type_: RuntimeType,
    },
}

impl Expression {
    pub const TRUE: Expression = Expression::Lit {
        lit: Lit::BoolLit { bool_value: true },
        type_: RuntimeType::BoolRuntimeType,
    };
    pub const FALSE: Expression = Expression::Lit {
        lit: Lit::BoolLit { bool_value: false },
        type_: RuntimeType::BoolRuntimeType,
    };

    pub const NULL: Expression = Expression::Lit {
        lit: Lit::NullLit,
        type_: RuntimeType::REFRuntimeType,
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
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NonVoidType {
    UIntType,
    IntType,
    FloatType,
    BoolType,
    StringType,
    CharType,
    ReferenceType { identifier: String },
    ArrayType { inner_type: Box<NonVoidType> },
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
}
