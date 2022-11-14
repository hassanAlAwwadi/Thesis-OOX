use std::collections::HashMap;

use crate::syntax::{Expression, Identifier, Lhs, DeclarationMember};



pub struct StackFrame {
    pub pc: u64,
    pub t: Option<Lhs>,
    pub params: HashMap<Identifier, Expression>,
    pub current_member: DeclarationMember
}