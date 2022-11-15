use std::collections::HashMap;

use crate::syntax::{Expression, Identifier, Lhs, DeclarationMember};


#[derive(Clone, Debug)]
pub struct StackFrame {
    pub pc: u64,
    pub t: Option<Lhs>,
    pub params: HashMap<Identifier, Expression>,
    pub current_member: DeclarationMember
}

pub fn lookup_in_stack<'a>(identifier: &Identifier, stack: &'a Vec<StackFrame>) -> Option<&'a Expression> {
    stack.last().unwrap().params.get(identifier)
}