use std::{rc::Rc, cell::RefCell};

use super::{Identifier, DeclarationMember, Interface};
use std::fmt::Debug;


#[derive(Clone, Eq, PartialEq)]
pub struct Class {
    pub name: Identifier,
    pub extends_old: Option<Rc<Class>>,
    pub subclasses_old: RefCell<Vec<Rc<Class>>>, // classes that extend from this class.
    pub implements_old: Vec<Rc<Interface>>,
    pub members: Vec<Rc<DeclarationMember>>,

    pub extends: Option<Identifier>,
    pub implements: Vec<Identifier>,
}

impl Debug for Class {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Class")
            .field("name", &self.name)
            .field("extends",&self.extends_old.is_some())
            .field("subclasses", &self.subclasses_old.borrow().len())
            .field("implements", &self.implements_old.len())
            .field("members", &self.members)
            .finish()
    }
}