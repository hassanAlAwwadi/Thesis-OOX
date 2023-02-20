use std::{collections::HashMap, rc::Rc};

use itertools::Itertools;

use crate::{
    error,
    syntax::{
        self, Class, CompilationUnit, Declaration, DeclarationMember, Identifier, Interface,
        NonVoidType, RuntimeType,
    },
};

pub type Fields = Vec<(Identifier, NonVoidType)>;

pub type Field = (Identifier, NonVoidType);

type SymbolError = String;

#[derive(Default)]
struct InheritanceTable {
    pub class_extends: HashMap<Identifier, Option<Rc<Class>>>, // class to class it extends (or None if not)
    pub interface_extends: HashMap<Identifier, Vec<Rc<Interface>>>, // interface to interface it extends
    pub implements: HashMap<Identifier, Vec<Rc<Interface>>>,        // class_name -> implements
    pub subclasses: HashMap<Identifier, Vec<Rc<Class>>>, // class_name -> direct subclasses
    pub implemented: HashMap<Identifier, Vec<Rc<Class>>>, // interface_name -> direct classes that implement this interface
    pub subinterfaces: HashMap<Identifier, Vec<Rc<Interface>>>, // interface_name -> direct interfaces that extend this interface
}

pub struct SymbolTable {
    pub class_to_fields: HashMap<Identifier, Fields>,
    // pub declaration_to_methods: HashMap<Identifier, DeclarationMember>,
    inheritance_table: InheritanceTable,

    pub declarations: HashMap<Identifier, Declaration>,
    pub decl_to_instance_types: HashMap<Identifier, Vec<Identifier>>,
}

impl SymbolTable {
    pub fn from_ast(compilation_unit: &CompilationUnit) -> Result<SymbolTable, SymbolError> {
        let mut class_to_fields = HashMap::new();

        let mut it: InheritanceTable = Default::default();

        // let mut class_to_methods = HashMap::new();
        let mut declarations = HashMap::new();
        for member in &compilation_unit.members {
            declarations.insert(member.name().clone(), member.clone());
        }

        // Bookmark extends & implements
        for (decl_name, member) in &declarations {
            match member.clone() {
                Declaration::Class(class) => {
                    it.subclasses.insert(class.name.clone(), Vec::new());
                    if let Some(extends_name) = &class.extends {
                        let extend_class =
                            Self::get_class_from_declarations(&declarations, &extends_name)?;

                        it.class_extends.insert(decl_name.clone(), Some(extend_class));
                        it.subclasses
                            .entry(extends_name.clone())
                            .or_default()
                            .push(class.clone());
                    } else {
                        it.class_extends.insert(decl_name.clone(), None);
                    }
                    for interface_name in class.implements.iter() {
                        let interface = Self::get_interface(&declarations, &interface_name)?;
                        it.implements
                            .entry(decl_name.clone())
                            .or_default()
                            .push(interface);
                        it.implemented
                            .entry(interface_name.clone())
                            .or_default()
                            .push(class.clone());
                    }
                }
                Declaration::Interface(interface) => {
                    it.interface_extends.insert(interface.name.clone(), Vec::new());
                    it.subinterfaces.insert(interface.name.clone(), Vec::new());
                    it.implemented.insert(interface.name.clone(), Vec::new());
                    for interface_name in &interface.extends {
                        let extend_interface = Self::get_interface(&declarations, &interface_name)?;
                        it.interface_extends
                            .entry(decl_name.clone())
                            .or_default()
                            .push(extend_interface);
                        it.subinterfaces
                            .entry(interface_name.clone())
                            .or_default()
                            .push(interface.clone());
                    }
                }
            }
        }

        for (decl_name, member) in &declarations {
            if let Declaration::Class(class) = member.clone() {
                let fields = Self::collect_fields(class, &it);
                // let methods = Self::collect_methods(class);
                class_to_fields.insert(decl_name.clone(), fields);
            }
        }

        // For each declaration, all possible types that can be represented at runtime,
        // considering inheritance and interfaces.
        let decl_to_instance_types = declarations
            .iter()
            .map(|(name, decl)| {
                let derived_classes = Self::derived_classes(decl.clone(), &it)
                    .into_iter()
                    .map(|class| class.name.clone())
                    .unique()
                    .collect_vec();
                (name.clone(), derived_classes)
            })
            .collect::<HashMap<_, _>>();

        Ok(SymbolTable {
            class_to_fields,
            declarations,
            inheritance_table: it,
            decl_to_instance_types,
        })
    }

    pub fn get_all_fields(&self, class_name: &str) -> &Fields {
        &self.class_to_fields[class_name]
    }

    /// Returns class_name and all subclasses of class_name,
    /// in other words all possible instance types for this class.
    pub fn get_all_instance_types(&self, class_name: &str) -> &Vec<Identifier> {
        &self.decl_to_instance_types[class_name]
    }

    pub fn lookup_field(&self, class_name: &str, field: &str) -> Option<&Field> {
        self.class_to_fields[class_name]
            .iter()
            .find(|(f, _)| f == field)
    }

    pub fn get_class(&self, class_name: &str) -> Result<Rc<Class>, SymbolError> {
        Self::get_class_from_declarations(&self.declarations, class_name)
    }

    pub fn class_extends(&self, class_name: &str) -> Option<Rc<Class>> {
        self.inheritance_table.class_extends[class_name].clone()
    }

    pub fn class_implements(&self, class_name: &str) -> &Vec<Rc<Interface>> {
        &self.inheritance_table.implements[class_name]
    }

    pub fn interface_implemented(&self, interface_name: &str) -> &Vec<Rc<Class>> {
        &self.inheritance_table.implemented[interface_name]
    }

    pub fn subclasses(&self, class_name: &str) -> &Vec<Rc<Class>> {
        &self.inheritance_table.subclasses[class_name]
    }

    pub fn interface_extends(&self, interface_name: &str) -> &Vec<Rc<Interface>> {
        &self.inheritance_table.interface_extends[interface_name]
    }

    fn get_class_from_declarations(
        declarations: &HashMap<Identifier, Declaration>,
        class_name: &str,
    ) -> Result<Rc<Class>, SymbolError> {
        match declarations.get(class_name) {
            Some(Declaration::Class(class)) => Ok(class.clone()),
            Some(Declaration::Interface(_)) => {
                Err(error::expected_class_found_interface(class_name))
            }

            None => Err(error::class_does_not_exist(class_name)),
        }
    }

    fn get_interface(
        declarations: &HashMap<Identifier, Declaration>,
        interface_name: &str,
    ) -> Result<Rc<Interface>, SymbolError> {
        match declarations.get(interface_name) {
            Some(Declaration::Interface(interface)) => Ok(interface.clone()),
            Some(Declaration::Class(_)) => {
                Err(error::expected_interface_found_class(interface_name))
            }

            None => Err(error::class_does_not_exist(interface_name)),
        }
    }

    // pub fn lookup_method(&self, class_name: &str, method_name: &str) -> Option<

    // pub fn match_method(&self, class_name: &str, method_name: &str, return_type: RuntimeType, arg_types: Vec<RuntimeType>) {
    //     self.lookupMethod
    // }

    /// Get all derived classes of the declaration
    /// This includes childs of child etc.
    fn derived_classes<'a>(
        declaration: Declaration,
        it: &InheritanceTable,
    ) -> Vec<Rc<syntax::Class>> {
        let derived_classes = match declaration {
            Declaration::Class(class) => class_helper(class, it),
            Declaration::Interface(interface) => interface_helper(interface, it),
        };

        fn class_helper(
            subclass: Rc<syntax::Class>,
            it: &InheritanceTable,
        ) -> Vec<Rc<syntax::Class>> {
            let subclasses = it.subclasses.get(&subclass.name).unwrap();
            std::iter::once(subclass.clone())
                .chain(
                    subclasses
                        .iter()
                        .cloned()
                        .flat_map(|subclass| class_helper(subclass, it)),
                )
                .collect_vec()
        }

        fn interface_helper(
            subinterface: Rc<syntax::Interface>,
            it: &InheritanceTable,
        ) -> Vec<Rc<syntax::Class>> {
            let implemented = &it.implemented[&subinterface.name];
            let subinterfaces = &it.subinterfaces[&subinterface.name];

            let subclasses_from_subclasses = implemented
                .iter()
                .cloned()
                .flat_map(|implemented| class_helper(implemented, it));
            let subclasses_from_interfaces = subinterfaces
                .iter()
                .cloned()
                .flat_map(|subinterface| interface_helper(subinterface, it))
                .into_iter();

            subclasses_from_subclasses
                .chain(subclasses_from_interfaces)
                .collect()
        }

        derived_classes
    }

    /// Collects fields from declaration, by looking at the class and its superclasses
    /// The order of the fields is prioritised by class hierarchy.
    fn collect_fields(class: Rc<syntax::Class>, it: &InheritanceTable) -> Fields {
        let mut fields = Vec::new();

        for declaration_member in &class.members {
            match declaration_member {
                DeclarationMember::Field { type_, name } => {
                    fields.push((name.to_owned(), type_.to_owned()))
                }
                _ => (),
            };
        }

        if let Some(extends) = it.class_extends[&class.name].clone() {
            [Self::collect_fields(extends, it), fields].concat()
        } else {
            fields
        }
    }

    // fn collect_methods(declaration: Declaration) -> Vec<Rc<DeclarationMember>> {
    //     match declaration {
    //         Declaration::Class(class) => Self::collect_methods_class(class),
    //         Declaration::Interface(interface) => Self::collect_methods_interface(interface),
    //     }
    // }

    // fn collect_methods_class(class: Rc<Class>) -> Vec<Rc<DeclarationMember>> {
    //         let mut methods = Vec::new();
    //     for declaration_member in &class.members {
    //         match declaration_member.as_ref() {
    //             DeclarationMember::Field { type_, name } => {
    //                 ()
    //             }
    //             _ => methods.push(declaration_member.clone()),
    //         };
    //     }

    //     let methods = if let Some(extends) = class.extends.clone() {
    //         [Self::collect_methods_class(extends.into()), methods].concat()
    //     } else {
    //         methods
    //     };
    //     let interface_methods = class.implements.iter().cloned().flat_map(|interface| Self::collect_methods_interface(interface)).collect();
    //     methods.extend(interface_methods);
    //     methods
    // }

    // fn collect_methods_interface(interface: Rc<Interface>) -> Vec<Rc<DeclarationMember>> {
    //     todo!()
    // }
}
