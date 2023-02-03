use std::{cell::Ref, collections::HashMap, rc::Rc};

use itertools::Itertools;

use crate::syntax::{
    self, Class, CompilationUnit, Declaration, DeclarationMember, Identifier, NonVoidType,
};

pub type Fields = Vec<(Identifier, NonVoidType)>;

pub struct SymbolicTable {
    pub class_to_fields: HashMap<Identifier, Fields>,
    pub declarations: HashMap<Identifier, Declaration>,
    pub decl_to_instance_types: HashMap<Identifier, Vec<Identifier>>,
}

impl SymbolicTable {
    pub fn from_ast(compilation_unit: &CompilationUnit) -> SymbolicTable {
        let mut class_to_fields = HashMap::new();
        let mut declarations = HashMap::new();
        for member in &compilation_unit.members {
            match member.clone() {
                Declaration::Class(class) => {
                    let class_name = member.name();
                    let fields = Self::collect_fields(class);
                    class_to_fields.insert(class_name.clone(), fields);
                    declarations.insert(class_name.clone(), member.clone());
                }
                Declaration::Interface(interface) => {
                    declarations.insert(interface.name.clone(), member.clone());
                }
            }
        }
        // For each declaration, all possible types that can be represented at runtime,
        // considering inheritance and interfaces.
        let decl_to_instance_types = declarations
            .iter()
            .map(
                |(name, decl)| {
                    let derived_classes = Self::derived_classes(decl.clone())
                        .into_iter()
                        .map(|class| class.name.clone())
                        .unique()
                        .collect_vec();
                    (name.clone(), derived_classes)
                },
            )
            .collect::<HashMap<_, _>>();

        SymbolicTable {
            class_to_fields,
            declarations,
            decl_to_instance_types,
        }
    }

    pub fn get_all_fields(&self, class_name: &str) -> &Fields {
        &self.class_to_fields[class_name]
    }

    /// Returns class_name and all subclasses of class_name,
    /// in other words all possible instance types for this class.
    pub fn get_all_instance_types(&self, class_name: &str) -> &Vec<Identifier> {
        &self.decl_to_instance_types[class_name]
    }

    /// Get all derived classes of the declaration
    /// This includes childs of child etc.
    fn derived_classes<'a>(declaration: Declaration) -> Vec<Rc<syntax::Class>> {
        let derived_classes = match declaration {
            Declaration::Class(class) => class_helper(class),
            Declaration::Interface(interface) => interface_helper(interface),
        };

        fn class_helper(subclass: Rc<syntax::Class>) -> Vec<Rc<syntax::Class>> {
            std::iter::once(subclass.clone())
                .chain(
                    subclass
                        .subclasses
                        .borrow()
                        .iter()
                        .cloned()
                        .flat_map(class_helper),
                )
                .collect_vec()
        }

        fn interface_helper(subinterface: Rc<syntax::Interface>) -> Vec<Rc<syntax::Class>> {
            let implemented = subinterface.implemented.borrow();
            let subinterfaces = subinterface.subinterfaces.borrow();

            let subclasses_from_subclasses = implemented.iter().cloned().flat_map(class_helper);
            let subclasses_from_interfaces = subinterfaces
                .iter().cloned().flat_map(interface_helper).into_iter();
                
            subclasses_from_subclasses
                .chain(subclasses_from_interfaces)
                .collect()
        }

        derived_classes
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
