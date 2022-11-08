pub type Identifier = String;
pub type Reference = i64;

#[derive(Debug)]
pub struct CompilationUnit {
    pub members: Vec<Declaration>,
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Class {
        name: Identifier,
        members: Vec<DeclarationMember>,
    },
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub struct Parameter {
    pub type_: NonVoidType,
    pub name: Identifier,
}

#[derive(Debug, Clone)]
pub struct Specification {
    pub requires: Option<Expression>,
    pub ensures: Option<Expression>,
    pub exceptional: Option<Expression>,
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub enum Invocation {
    InvokeMethod {
        lhs: Identifier,
        rhs: Identifier,
        arguments: Vec<Expression>,
        resolved: Option<Box<(Declaration, DeclarationMember)>>, // What is this?
    },
    InvokeConstructor {
        class_name: Identifier,
        arguments: Vec<Expression>,
        resolved: Option<Box<(Declaration, DeclarationMember)>>, // What is this?
    },
}

#[derive(Debug, Clone)]
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
        index: Expression,
        type_: RuntimeType,
    },
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
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
        lhs: Box<Expression>,
        rhs: Box<Expression>,
        type_: RuntimeType,
    },
    UnOp {
        un_op: UnOp,
        value: Box<Expression>,
        type_: RuntimeType,
    },
    Var {
        var: Identifier,
        type_: RuntimeType,
    },
    SymbolicVar {
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
        var: Identifier,
        type_: RuntimeType,
    },
    Conditional {
        guard: Box<Expression>,
        true_: Box<Expression>,
        false_: Box<Expression>,
        type_: RuntimeType,
    },
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub enum UnOp {
    Negative,
    Negate,
}

#[derive(Debug, Clone)]
pub enum Lit {
    BoolLit { bool_value: bool },
    UIntLit { uint_value: u64 },
    IntLit { int_value: i64 },
    FloatLit { float_value: f64 },
    StringLit { string_value: String },
    CharLit { char_value: char },
    NullLit,
}

#[derive(Debug, Clone)]
pub struct Type {
    pub type_: Option<NonVoidType>,
}

#[derive(Debug, Clone)]
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
#[derive(Debug, Clone, PartialEq, Eq)]
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
