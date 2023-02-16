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

pub struct SymbolTable {
    pub class_to_fields: HashMap<Identifier, Fields>,
    // pub declaration_to_methods: HashMap<Identifier, DeclarationMember>,
    pub class_extends: HashMap<Identifier, Rc<Class>>, // class to class it extends
    pub interface_extends: HashMap<Identifier, Vec<Rc<Interface>>>, // interface to interface it extends
    pub implements: HashMap<Identifier, Vec<Rc<Interface>>>, // class_name -> implements
    pub subclasses: HashMap<Identifier, Vec<Rc<Class>>>, // class_name -> direct subclasses
    pub implemented: HashMap<Identifier, Vec<Rc<Class>>>, // interface_name -> direct classes that implement this interface
    pub subinterfaces: HashMap<Identifier, Vec<Rc<Interface>>>, // interface_name -> direct interfaces that extend this interface

    pub declarations: HashMap<Identifier, Declaration>,
    pub decl_to_instance_types: HashMap<Identifier, Vec<Identifier>>,
}

impl SymbolTable {
    pub fn from_ast(compilation_unit: &CompilationUnit) -> Result<SymbolTable, SymbolError> {
        let mut class_to_fields = HashMap::new();

        let mut class_extends = HashMap::new();
        let mut interface_extends = HashMap::<Identifier, Vec<Rc<Interface>>>::new();
        let mut implements = HashMap::<Identifier, Vec<Rc<Interface>>>::new();
        let mut subclasses = HashMap::<Identifier, Vec<Rc<Class>>>::new();
        let mut implemented = HashMap::<Identifier, Vec<Rc<Class>>>::new();
        let mut subinterfaces = HashMap::<Identifier, Vec<Rc<Interface>>>::new();

        // let mut class_to_methods = HashMap::new();
        let mut declarations = HashMap::new();
        for member in &compilation_unit.members {
            declarations.insert(member.name().clone(), member.clone());
        }

        // Bookmark extends & implements
        for (decl_name, member) in &declarations {
            match member.clone() {
                Declaration::Class(class) => {
                    if let Some(extends_name) = &class.extends {
                        let extend_class = Self::get_class(&declarations, &extends_name)?;

                        class_extends.insert(decl_name.clone(), extend_class);
                        subclasses
                            .entry(extends_name.clone())
                            .or_default()
                            .push(class.clone());
                    }
                    for interface_name in class.implements.iter() {
                        let interface = Self::get_interface(&declarations, &interface_name)?;
                        implements.entry(decl_name.clone()).or_default().push(interface);
                        implemented
                        .entry(interface_name.clone())
                        .or_default()
                        .push(class.clone());
                    }
                }
                Declaration::Interface(interface) => {
                    for interface_name in &interface.extends {
                        let extend_interface = Self::get_interface(&declarations, &interface_name)?;
                        interface_extends.entry(decl_name.clone()).or_default().push(extend_interface);
                        subinterfaces
                        .entry(interface_name.clone())
                        .or_default()
                        .push(interface.clone());
                    }
                },
            }
        }

        for (decl_name, member) in &declarations {
            if let Declaration::Class(class) = member.clone() {
                let fields = Self::collect_fields(class);
                // let methods = Self::collect_methods(class);
                class_to_fields.insert(decl_name.clone(), fields);
            }
        }

        // For each declaration, all possible types that can be represented at runtime,
        // considering inheritance and interfaces.
        let decl_to_instance_types = declarations
            .iter()
            .map(|(name, decl)| {
                let derived_classes = Self::derived_classes(decl.clone())
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
            class_extends,
            interface_extends,
            implements,
            subclasses,
            implemented,
            subinterfaces,
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

    fn get_class(
        declarations: &HashMap<Identifier, Declaration>,
        class_name: &str,
    ) -> Result<Rc<Class>, SymbolError> {
        match declarations.get(class_name) {
            Some(Declaration::Class(class)) => Ok(class.clone()),
            Some(Declaration::Interface(_)) => 
                Err(error::expected_class_found_interface(class_name)),
            
            None => Err(error::extended_class_does_not_exist(class_name)),
        }
    }

    fn get_interface(
        declarations: &HashMap<Identifier, Declaration>,
        interface_name: &str,
    ) -> Result<Rc<Interface>, SymbolError> {
        match declarations.get(interface_name) {
            Some(Declaration::Interface(interface)) => Ok(interface.clone()),
            Some(Declaration::Class(_)) => 
            Err(error::expected_interface_found_class(interface_name)),
            
            None => Err(error::extended_class_does_not_exist(interface_name)),
        }
    }

    // pub fn lookup_method(&self, class_name: &str, method_name: &str) -> Option<

    // pub fn match_method(&self, class_name: &str, method_name: &str, return_type: RuntimeType, arg_types: Vec<RuntimeType>) {
    //     self.lookupMethod
    // }

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
                        .subclasses_old
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
                .iter()
                .cloned()
                .flat_map(interface_helper)
                .into_iter();

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

        if let Some(extends) = class.extends_old.clone() {
            [Self::collect_fields(extends), fields].concat()
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
