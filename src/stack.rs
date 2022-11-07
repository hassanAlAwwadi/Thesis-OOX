use std::collections::HashMap;

use crate::syntax::{Expression, Identifier, Lhs};



pub struct StackFrame {
    pub pc: u64,
    pub t: Lhs,
    pub params: HashMap<Identifier, Expression>
}