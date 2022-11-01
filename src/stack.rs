use crate::syntax::{Lhs, Parameter};



pub(crate) struct StackFrame {
    pc: u64,
    lhs: Lhs,
    local_vars: Vec<(String, Parameter)>,
}