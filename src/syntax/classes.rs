use std::{rc::Rc, cell::RefCell};

use super::{Identifier, DeclarationMember, Interface};
use std::fmt::Debug;


#[derive(Clone, Eq, PartialEq)]
pub struct Class {
    pub name: Identifier,
    pub extends: Option<Rc<Class>>,
    pub subclasses: RefCell<Vec<Rc<Class>>>, // classes that extend from this class.
    pub implements: Vec<Rc<Interface>>,
    pub members: Vec<Rc<DeclarationMember>>,
}

impl Debug for Class {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Class")
            .field("name", &self.name)
            .field("extends",&self.extends.is_some())
            .field("subclasses", &self.subclasses.borrow().len())
            .field("implements", &self.implements.len())
            .field("members", &self.members)
            .finish()
    }
}