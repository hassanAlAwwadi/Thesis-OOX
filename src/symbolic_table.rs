use std::{cell::Ref, collections::HashMap, rc::Rc};

use itertools::Itertools;

use crate::syntax::{CompilationUnit, Declaration, DeclarationMember, Identifier, NonVoidType};

pub type Fields = Vec<(Identifier, NonVoidType)>;

pub struct SymbolicTable {
    pub class_to_fields: HashMap<Identifier, Fields>,
    pub classes: HashMap<Identifier, Rc<Declaration>>,
    pub class_to_instance_types: HashMap<Identifier, Vec<Identifier>>,
}

impl SymbolicTable {
    pub fn from_ast(compilation_unit: &CompilationUnit) -> SymbolicTable {
        let mut class_to_fields = HashMap::new();
        let mut classes = HashMap::new();
        for member in &compilation_unit.members {
            let class_name = member.name();
            let fields = Self::collect_fields(member);
            class_to_fields.insert(class_name.clone(), fields);
            classes.insert(class_name.clone(), member.clone());
        }

        let mut class_to_instance_types = classes
            .keys()
            .map(|class_name| {
                (
                    class_name.clone(),
                    std::iter::once(class_name.clone())
                        .chain(Self::subclasses(&classes, class_name).into_iter().map(|d| {
                            let Declaration::Class { name, .. } = d.as_ref();
                            name.clone()
                        }))
                        .collect_vec(),
                )
            })
            .collect::<HashMap<_, _>>();

        SymbolicTable {
            class_to_fields,
            classes,
            class_to_instance_types
        }
    }

    pub fn get_all_fields(&self, class_name: &str) -> &Fields {
        &self.class_to_fields[class_name]
    }

    /// Returns class_name and all subclasses of class_name,
    /// in other words all possible instance types for this class.
    pub fn get_all_instance_types(&self, class_name: &str) -> &Vec<Identifier> {
        &self.class_to_instance_types[class_name]
    }
    /// Get all subclasses of the class_name
    fn subclasses<'a>(
        classes: &HashMap<String, Rc<Declaration>>,
        class_name: &str,
    ) -> Vec<Rc<Declaration>> {
        let declaration = &classes[class_name];
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

    /// Collects fields from declaration, by looking at the class and its superclasses
    /// The order of the fields is prioritised by class hierarchy.
    fn collect_fields(
        class: &Rc<Declaration>) -> Fields {
            let mut fields = Vec::new();

            let Declaration::Class {
                members,
                extends,
                ..
            } = class.as_ref();

            for declaration_member in members {
                match declaration_member.as_ref() {
                    DeclarationMember::Field { type_, name } => {
                        fields.push((name.to_owned(), type_.to_owned()))
                    }
                    _ => (),
                };
            }

            if let Some(extends) = extends {
                [Self::collect_fields(extends), fields].concat()
            } else {
                fields
            }
        }
}
