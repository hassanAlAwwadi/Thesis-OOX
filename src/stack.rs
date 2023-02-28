use std::{collections::HashMap, rc::Rc};

use crate::syntax::{Expression, Identifier, Lhs, Method};

#[derive(Clone, Debug)]
pub struct StackFrame {
    pub pc: u64,
    pub t: Option<Lhs>,
    pub params: HashMap<Identifier, Rc<Expression>>,
    pub current_member: Rc<Method>,
}

pub fn lookup_in_stack<'a>(
    identifier: &Identifier,
    stack: &'a Vec<StackFrame>,
) -> Option<Rc<Expression>> {
    stack.last().unwrap().params.get(identifier).cloned()
}

/// Writes identifier with value expression to the top of the stack
pub fn write_to_stack<'a, E>(identifier: Identifier, value: E, stack: &'a mut Vec<StackFrame>)
where
    E: Into<Rc<Expression>>,
{
    stack
        .last_mut()
        .unwrap()
        .params
        .insert(identifier, value.into());
}

/// Removes identifier with value expression from the top of the stack
pub fn remove_from_stack<'a>(identifier: &Identifier, stack: &'a mut Vec<StackFrame>) {
    stack.last_mut().unwrap().params.remove(identifier);
}
