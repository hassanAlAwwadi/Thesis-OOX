use std::{collections::HashMap, rc::Rc};

use im_rc::Vector;

use crate::syntax::{Expression, Identifier, Lhs, Method};

#[derive(Clone)]
pub struct Stack(Vector<StackFrame>);

impl Stack {
    pub fn new(frames: Vector<StackFrame>) -> Stack {
        Stack(frames)
    }

    pub fn push(&mut self, stack_frame: StackFrame) {
        self.0.push_back(stack_frame);
    }

    pub fn current_stackframe(&self) -> Option<&StackFrame> {
        self.0.last()
    }

    pub fn current_variables(&self) -> Option<&HashMap<Identifier, Rc<Expression>>> {
        self.current_stackframe().map(|s| &s.params)
    }

    // Inserts a variable in the current (latest) stackframe.
    pub fn insert_variable(&mut self, var: Identifier, value: impl Into<Rc<Expression>>) {
        let stack_frame = self.0.back_mut().unwrap();

        stack_frame.params.insert(var, value.into());
    }
    /// Removes identifier with value expression from the top of the stack
    pub fn remove_variable<'a>(&mut self, identifier: &Identifier) {
        let stack_frame = self.0.back_mut().unwrap();
        stack_frame.params.remove(identifier);
    }

    pub fn lookup<'a>(
        &self,
        identifier: &Identifier,
    ) -> Option<Rc<Expression>> {
        self.current_variables().unwrap().get(identifier).cloned()
    }
    

    pub fn pop(&mut self) -> Option<StackFrame> {
        self.0.pop_back()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

#[derive(Clone, Debug)]
pub struct StackFrame {
    pub pc: u64,
    pub t: Option<Lhs>,
    pub params: HashMap<Identifier, Rc<Expression>>,
    pub current_member: Rc<Method>,
}

