use std::{cell::RefCell, rc::Rc};

use itertools::Itertools;

use super::{
    classes::Class, AbstractMethod, Identifier, Method, NonVoidType, Parameter, Statement, Type,
};
use std::fmt::Debug;

#[derive(Clone)]
pub struct Interface {
    pub name: Identifier,
    pub members: Vec<InterfaceMember>,

    pub extends: Vec<Identifier>,
}

#[derive(Debug, Clone)]
pub enum InterfaceMember {
    DefaultMethod(Rc<Method>),
    AbstractMethod(Rc<AbstractMethod>),
}

/// Searches for interface methods, with the name method_name.
/// Suboptimal return of InterfaceMethods -- wrap in Rc
/// Does it search for default or abstract?
pub fn find_interface_method<'a>(
    method_name: &'a str,
    members: &'a Vec<InterfaceMember>,
) -> Option<InterfaceMember> {
    members.iter().find_map(|member| match member {
        InterfaceMember::DefaultMethod(method) if method.name == method_name => {
            Some(member.clone())
        }
        InterfaceMember::AbstractMethod(abstract_method) if abstract_method.name == method_name => {
            Some(member.clone())
        }
        _ => None,
    })
}

impl Debug for Interface {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Interface")
            .field("name", &self.name)
            .field("members", &self.members)
            .field("extends", &self.extends)
            .finish()
    }
}
