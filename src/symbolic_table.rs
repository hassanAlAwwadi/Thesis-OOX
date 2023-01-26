use std::{cell::Ref, collections::HashMap, rc::Rc};

use itertools::Itertools;

use crate::syntax::{CompilationUnit, Declaration, DeclarationMember, Identifier, NonVoidType};

pub type Fields = Vec<(Identifier, NonVoidType)>;

pub struct SymbolicTable {
    pub class_to_fields: HashMap<String, Fields>,
    pub classes: HashMap<String, Rc<Declaration>>,
}

impl SymbolicTable {
    pub fn from_ast(compilation_unit: &CompilationUnit) -> SymbolicTable {
        let mut class_to_fields = HashMap::new();
        let mut classes = HashMap::new();
        for member in &compilation_unit.members {
            let Declaration::Class {
                name: class_name,
                members,
                ..
            } = member.as_ref();
            let mut fields = Vec::new();
            for declaration_member in members {
                match declaration_member.as_ref() {
                    DeclarationMember::Field { type_, name } => {
                        fields.push((name.to_owned(), type_.to_owned()))
                    }
                    _ => (),
                };
            }
            class_to_fields.insert(class_name.clone(), fields);
            classes.insert(class_name.clone(), member.clone());
        }

        SymbolicTable {
            class_to_fields,
            classes,
        }
    }

    pub fn get_all_fields(&self, class_name: &str) -> &Fields {
        &self.class_to_fields[class_name]
    }

    /// Returns class_name and all subclasses of class_name,
    /// in other words all possible instance types for this class.
    pub fn get_all_instance_types(&self, class_name: &str) -> impl Iterator<Item = Identifier> {
        let subclass_names = self.subclasses(class_name).into_iter().map(|d| {
            let Declaration::Class { name, .. } = d.as_ref();
            name.clone()
        });
        std::iter::once(class_name.to_string()).chain(subclass_names)
    }

    fn subclasses<'a>(&'a self, class_name: &str) -> Vec<Rc<Declaration>> {
        let declaration = &self.classes[class_name];
        let Declaration::Class { subclasses, .. } = declaration.as_ref();

        fn helper(subclass: Rc<Declaration>) -> Vec<Rc<Declaration>> {
            let Declaration::Class { subclasses, .. } = subclass.as_ref();

            std::iter::once(subclass.clone())
                .chain(subclasses.borrow().iter().cloned().flat_map(helper))
                .collect_vec()
        }

        subclasses
            .borrow()
            .iter()
            .cloned()
            .flat_map(helper)
            .collect_vec()
    }
}
