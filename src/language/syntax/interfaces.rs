use std::{ rc::Rc};

use derivative::Derivative;

use super::{
     AbstractMethod, Identifier, Method, 
};
use std::fmt::Debug;

#[derive(Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub struct Interface {
    pub name: Identifier,
    pub members: Vec<InterfaceMember>,

    pub extends: Vec<Identifier>,
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum InterfaceMember {
    DefaultMethod(Rc<Method>),
    AbstractMethod(Rc<AbstractMethod>),
}

impl InterfaceMember {
    pub fn try_into_default_method(&self) -> Option<Rc<Method>> {
        if let InterfaceMember::DefaultMethod(method) = self {
            return Some(method.clone());
        }
        None
    }
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
