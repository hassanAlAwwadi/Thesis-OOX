//! Takes a syntax tree and outputs a list of syntax trees, each with one mutation.
//! A mutation is a small change in the source code, for example a change in comparison direction, `2 > 1` becomes `2 < 1`
//! A mutation should result in a type correct program
//!
//! Mutations can be used to verify software testing tools

use std::collections::HashMap;

use itertools::Itertools;

use crate::syntax::*;

type Environment = HashMap<Identifier, NonVoidType>;

/// A function that takes an A, returning T
/// T is usually a collection representing all mutated A.
type Mutator<A, T> = &'static dyn Fn(A) -> T;
type MutatorWithEnv<A, T> = &'static dyn Fn(A, &Environment) -> T;

#[derive(Copy, Clone)]
enum MutationOperator {
    StatementMutation(Mutator<Statement, Vec<Statement>>),
    VarMutation(MutatorWithEnv<Identifier, Vec<Identifier>>),
    LitMutation(Mutator<Lit, Vec<Lit>>),
    BinOpMutation(Mutator<BinOp, Vec<BinOp>>),
}

#[rustfmt::skip]
fn operators() -> Vec<(&'static str, MutationOperator)> {
    use MutationOperator::*;
    use Statement::*;
    vec![
        (
            "del",
            StatementMutation(&|stat| {
                if deletable_stat(stat) {
                    vec![Statement::Skip]
                } else {
                    vec![]
                }
            }),
        ),
        (
            "flow",
            StatementMutation(&|stat| match stat {
                Continue { info } => vec![Break { info }],
                Break { info } => vec![Continue { info }],
                _ => vec![],
            }),
        ),
        (
            "var",
            VarMutation(&|original_var, env| {
                let var_type = env[&original_var].clone();
                env.iter()
                    .filter(|(var, type_)| same_type(type_, &var_type) && **var != original_var)
                    .map(|(var, _)| var.clone()).collect()
            })
        ),
        (
            "lit",
            LitMutation(&|lit| match lit {
                Lit::IntLit { int_value }   => vec![ Lit::IntLit { int_value: int_value + 1 },
                                                     Lit::IntLit { int_value: int_value - 1 }],
                Lit::BoolLit { bool_value } => vec![Lit::BoolLit { bool_value: !bool_value }],
                _ => vec![]
            })
        ),
        (
            "eq",
            BinOpMutation(&|bin_op| match bin_op {
                BinOp::Equal    =>  vec![BinOp::NotEqual],
                BinOp::NotEqual =>  vec![BinOp::Equal],
                _ => vec![]
            })
        ),
        (
            "cmp",
            BinOpMutation(&|bin_op| match bin_op {
                BinOp::LessThan         =>  vec![BinOp::LessThanEqual, BinOp::GreaterThan, BinOp::GreaterThanEqual],
                BinOp::LessThanEqual    =>  vec![BinOp::LessThan, BinOp::GreaterThan, BinOp::GreaterThanEqual],
                BinOp::GreaterThan      =>  vec![BinOp::LessThan, BinOp::LessThanEqual, BinOp::GreaterThanEqual],
                BinOp::GreaterThanEqual =>  vec![BinOp::LessThan, BinOp::LessThanEqual, BinOp::GreaterThan],
                BinOp::NotEqual         =>  vec![BinOp::Equal],
                _ => vec![]
            })
        ),
        (
            "arith",
            BinOpMutation(&|bin_op| match bin_op {
                BinOp::Plus     => vec![BinOp::Minus, BinOp::Multiply, BinOp::Divide],
                BinOp::Minus    => vec![BinOp::Plus, BinOp::Multiply, BinOp::Divide, BinOp::Modulo],
                BinOp::Multiply => vec![BinOp::Plus, BinOp::Minus, BinOp::Divide, BinOp::Modulo],
                BinOp::Divide   => vec![BinOp::Plus, BinOp::Minus, BinOp::Multiply, BinOp::Modulo],
                BinOp::Modulo   => vec![BinOp::Plus, BinOp::Minus, BinOp::Multiply, BinOp::Divide],
                _ => vec![]
            })
        ),
        (   
            "bool",
            BinOpMutation(&|bin_op| match bin_op {
                BinOp::And      => vec![BinOp::Or, BinOp::Implies],
                BinOp::Or       => vec![BinOp::And, BinOp::Implies],
                BinOp::Implies  => vec![BinOp::And, BinOp::Or],
                _ => vec![]
            })
        ),
        // unop?
    ]
}

fn mutate_compilation_unit(mutation: MutationOperator, compilation_unit: &CompilationUnit) -> Vec<CompilationUnit> {
    let mutated_members = mutate_declarations(mutation, &compilation_unit.members);

    mutated_members.into_iter().map(|members| CompilationUnit { members }).collect()
}

fn mutate_declarations(mutation: MutationOperator, declarations: &[Declaration]) -> Vec<Vec<Declaration>> {
    declarations.iter().map(|decl| mutate_declaration(mutation, decl)).collect()
}

fn mutate_declaration(mutation: MutationOperator, declaration: &Declaration) -> Vec<Declaration> {
    match declaration {
        Declaration::Class(class) => todo!(),
        Declaration::Interface(_) => todo!(),
    }
    todo!()
}


// Helpers

fn deletable_stat(statement: Statement) -> bool {
    match statement {
        Statement::Declare { .. } => false,
        Statement::Assign { .. } => true,
        Statement::Call { .. } => true,
        Statement::Skip { .. } => false,
        Statement::Assert { .. } => false,
        Statement::Assume { .. } => false,
        Statement::While { .. } => false,
        Statement::Ite { .. } => false,
        Statement::Continue { .. } => true,
        Statement::Break { .. } => true,
        Statement::Return { .. } => false,
        Statement::Throw { .. } => true,
        Statement::Try { .. } => false,
        Statement::Block { .. } => false,
        Statement::Seq { .. } => false,
    }
}

fn same_type(t1: &NonVoidType, t2: &NonVoidType) -> bool {
    match (t1, t2) {
        (NonVoidType::UIntType { .. }, NonVoidType::UIntType { .. }) => true,
        (NonVoidType::IntType { .. }, NonVoidType::IntType { .. }) => true,
        (NonVoidType::FloatType { .. }, NonVoidType::FloatType { .. }) => true,
        (NonVoidType::BoolType { .. }, NonVoidType::BoolType { .. }) => true,
        (NonVoidType::StringType { .. }, NonVoidType::StringType { .. }) => true,
        (NonVoidType::CharType { .. }, NonVoidType::CharType { .. }) => true,
        (NonVoidType::ReferenceType { .. }, NonVoidType::ReferenceType { .. }) => true, // How are these same type?
        (NonVoidType::ArrayType { .. }, NonVoidType::ArrayType { .. }) => true,
        _ => false,
    }
}
