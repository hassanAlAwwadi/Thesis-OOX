use std::{cell::Ref, collections::HashMap, rc::Rc};

use itertools::Itertools;

use crate::syntax::{
    self, Class, CompilationUnit, Declaration, DeclarationMember, Identifier, NonVoidType,
};

pub type Fields = Vec<(Identifier, NonVoidType)>;

pub struct SymbolicTable {
    pub class_to_fields: HashMap<Identifier, Fields>,
    pub classes: HashMap<Identifier, Declaration>,
    pub class_to_instance_types: HashMap<Identifier, Vec<Identifier>>,
}

impl SymbolicTable {
    pub fn from_ast(compilation_unit: &CompilationUnit) -> SymbolicTable {
        let mut class_to_fields = HashMap::new();
        let mut classes = HashMap::new();
        for member in &compilation_unit.members {
            match member.clone() {
                Declaration::Class(class) => {
                    let class_name = member.name();
                    let fields = Self::collect_fields(class);
                    class_to_fields.insert(class_name.clone(), fields);
                    classes.insert(class_name.clone(), member.clone());
                }
                Declaration::Interface(_) => todo!(),
            }
        }

        let mut class_to_instance_types = classes
            .keys()
            .map(|class_name| {
                (
                    class_name.clone(),
                    std::iter::once(class_name.clone())
                        .chain(
                            Self::subclasses(&classes, class_name)
                                .into_iter()
                                .map(|class| class.name.clone()),
                        )
                        .collect_vec(),
                )
            })
            .collect::<HashMap<_, _>>();

        SymbolicTable {
            class_to_fields,
            classes,
            class_to_instance_types,
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
        classes: &HashMap<String, Declaration>,
        class_name: &str,
    ) -> Vec<Rc<syntax::Class>> {
        let declaration = &classes[class_name];
        let class = declaration.as_class().expect("expected class");

        fn helper(subclass: Rc<syntax::Class>) -> Vec<Rc<syntax::Class>> {
            std::iter::once(subclass.clone())
                .chain(
                    subclass
                        .subclasses
                        .borrow()
                        .iter()
                        .cloned()
                        .flat_map(helper),
                )
                .collect_vec()
        }

        let x = class
            .subclasses
            .borrow()
            .iter()
            .cloned()
            .flat_map(helper)
            .collect_vec();
        x
    }

    /// Collects fields from declaration, by looking at the class and its superclasses
    /// The order of the fields is prioritised by class hierarchy.
    fn collect_fields(class: Rc<syntax::Class>) -> Fields {
        let mut fields = Vec::new();

        for declaration_member in &class.members {
            match declaration_member.as_ref() {
                DeclarationMember::Field { type_, name } => {
                    fields.push((name.to_owned(), type_.to_owned()))
                }
                _ => (),
            };
        }

        if let Some(extends) = class.extends.clone() {
            [Self::collect_fields(extends), fields].concat()
        } else {
            fields
        }
    }
}
