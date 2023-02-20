use std::{cell::RefCell, rc::Rc};

use super::{DeclarationMember, Identifier, Interface};
use std::fmt::Debug;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Class {
    pub name: Identifier,
    pub members: Vec<DeclarationMember>,

    pub extends: Option<Identifier>,
    pub implements: Vec<Identifier>,
}
