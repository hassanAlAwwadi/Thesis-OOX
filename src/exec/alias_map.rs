use std::rc::Rc;

use itertools::Itertools;

use crate::{typeable::Typeable, Expression, Identifier};
use crate::{Lit, RuntimeType};

use crate::exec::ImHashMap;

pub type AliasMap = ImHashMap<Identifier, AliasEntry>;

/// An entry in the aliasmap. Every initialised symbolic reference should have an entry in the alias map.
/// If it is not in the aliasmap it has not been lazily-initialised and has not been used in the OOX program yet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AliasEntry {
    /// Expressions can only be `Expression::Ref` or null literal
    pub aliases: Vec<Rc<Expression>>,
    uniform_type: bool, // whether all aliases have the same type, or subclasses appear.
}

impl AliasEntry {
    // pub fn aliases(&self) -> impl Iterator<Item=&Rc<Expression>> + Clone {
    //     self.aliases.iter()
    // }

    /// Assumes that the uniform_type is correct with respect to aliases.
    pub fn new_with_uniform_type(aliases: Vec<Rc<Expression>>, uniform_type: bool) -> AliasEntry {
        AliasEntry {
            aliases,
            uniform_type,
        }
    }

    pub fn new(aliases: Vec<Rc<Expression>>) -> AliasEntry {
        let uniform_type = aliases
            .iter()
            .map(AsRef::as_ref)
            .filter(|e| **e != Expression::NULL)
            .map(Typeable::type_of)
            .all_equal();

        AliasEntry {
            aliases,
            uniform_type: uniform_type,
        }
    }

    pub fn aliases(&self) -> &Vec<Rc<Expression>> {
        &self.aliases
    }

    /// Returns Some type if all alias types are equal, otherwise return None.
    pub fn uniform_type(&self) -> Option<RuntimeType> {
        if self.uniform_type {
            self.aliases
                .iter()
                .map(AsRef::as_ref)
                .filter(|e| **e != Expression::NULL)
                .next()
                .map(Typeable::type_of)
        } else {
            None
        }
    }

    pub fn remove_null(&mut self) {
        self.aliases.retain(|x| match x.as_ref() {
            Expression::Lit {
                lit: Lit::NullLit, ..
            } => false,
            _ => true,
        });
    }
}
