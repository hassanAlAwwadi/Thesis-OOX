use std::{rc::Rc, cell::RefCell};

use super::{Identifier, NonVoidType, Parameter, Statement, classes::Class};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Interface {
    pub name: Identifier,
    pub extends: Vec<Rc<Interface>>, // interfaces that this interface extends
    pub subinterfaces: RefCell<Vec<Rc<Interface>>>, // interfaces that extend this interface
    pub implemented: RefCell<Vec<Rc<Class>>>, // classes that implement this interface
    pub members: Vec<Rc<InterfaceMembers>>
}


#[derive(Debug, Clone, Eq, PartialEq)]
pub enum InterfaceMembers {
    Method {
        type_: Option<NonVoidType>,
        identifier: Identifier,
        parameters: Vec<Parameter>,
        body: Option<Statement>,
    }
}