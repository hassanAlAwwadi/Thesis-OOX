use std::{cell::RefCell, rc::Rc};

use super::{DeclarationMember, Identifier, Interface};
use std::fmt::Debug;

#[derive(Clone, Eq, PartialEq)]
pub struct Class {
    pub name: Identifier,
    pub members: Vec<Rc<DeclarationMember>>,

    pub extends: Option<Identifier>,
    pub implements: Vec<Identifier>,
}

impl Debug for Class {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Class")
            .field("name", &self.name)
            .field("members", &self.members)
            .field("extends", &self.extends)
            .field("implements", &self.implements)
            .finish()
    }
}
