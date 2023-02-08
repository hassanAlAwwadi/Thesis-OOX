use std::{cell::RefCell, rc::Rc};

use itertools::Itertools;

use super::{classes::Class, Identifier, NonVoidType, Parameter, Statement, Type};
use std::fmt::Debug;

#[derive(Clone, Eq, PartialEq)]
pub struct Interface {
    pub name: Identifier,
    pub extends: Vec<Rc<Interface>>, // interfaces that this interface extends
    pub subinterfaces: RefCell<Vec<Rc<Interface>>>, // interfaces that extend this interface
    pub implemented: RefCell<Vec<Rc<Class>>>, // classes that implement this interface
    pub members: Vec<Rc<InterfaceMember>>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum InterfaceMember {
    Method(InterfaceMethod),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct InterfaceMethod {
    pub type_: Type,
    pub name: Identifier,
    pub parameters: Vec<Parameter>,
    pub body: Option<Statement>,

}

/// Searches for interface methods, with the name method_name.
/// Suboptimal return of InterfaceMethods -- wrap in Rc
pub fn find_interface_method<'a>(
    method_name: &'a str,
    members: &'a Vec<Rc<InterfaceMember>>,
) -> Option<InterfaceMethod> {
    members
        .iter()
        .find_map(|member| {
            let InterfaceMember::Method(interface@InterfaceMethod{ name, body, .. }) = member.as_ref();
            if name == method_name {
                return Some(interface);
            }
            
            None
        })
        .cloned()
}


impl Debug for Interface {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Interface")
            .field("name", &self.name)
            .field("extends", &self.extends.iter().map(|interface| &interface.name).collect_vec())
            .field("subinterfaces", &self.subinterfaces.borrow().iter().map(|interface| &interface.name).collect_vec())
            .field("implemented", &self.implemented.borrow().iter().map(|interface| &interface.name).collect_vec())
            .field("members", &self.members)
            .finish()
    }
}
