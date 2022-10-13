pub type Identifier = String;
type Reference = i64;

pub struct CompilationUnit {
    pub members: Vec<Declaration>,
}

pub enum Declaration {
    Class {
        name: Identifier,
        members: Vec<DeclarationMember>,
    },
}

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

pub struct Parameter {
    pub type_: NonVoidType,
    pub name: Identifier,
}

struct Specification {
    requires: Option<Expression>,
    ensures: Option<Expression>,
    exceptional: Option<Expression>,
}

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

enum BinOp {
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

enum UnOp {
    Negative,
    Negate,
}

enum Lit {
    BoolLit { bool_value: bool },
    UIntLit { uint_value: u64 },
    IntLit { int_value: i64 },
    FloatLit { float_value: f64 },
    StringLit { string_value: String },
    CharLit { char_value: char },
    NullLit,
}

struct Type {
    type_: Option<NonVoidType>,
}

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
    REFRuntimeType,
    ARRAYRuntimeType,
}
