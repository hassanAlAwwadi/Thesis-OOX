use std::{collections::HashMap, rc::Rc};

use itertools::Itertools;

use crate::{
    error,
    syntax::{
        self, Class, CompilationUnit, Declaration, DeclarationMember, Identifier, Interface,
        NonVoidType, RuntimeType,
    }, positioned::WithPosition,
};

pub type Fields = Vec<(Identifier, NonVoidType)>;

pub type Field = (Identifier, NonVoidType);

type SymbolError = String;

#[derive(Default, Debug)]
struct InterfaceData {
    extends: Vec<Rc<Interface>>,       // interfaces it extends
    implemented: Vec<Rc<Class>>,       // direct classes that implement this interface
    subinterfaces: Vec<Rc<Interface>>, // direct interfaces that extend this interface
}

#[derive(Default, Debug)]
struct ClassData {
    extends: Option<Rc<Class>>,
    implements: Vec<Rc<Interface>>,
    subclasses: Vec<Rc<Class>>,
}

#[derive(Debug)]
struct InheritanceTable {
    pub class: HashMap<Identifier, ClassData>,
    pub interface: HashMap<Identifier, InterfaceData>,
}

impl InheritanceTable {
    fn new(
        class_names: impl Iterator<Item = Identifier>,
        interface_names: impl Iterator<Item = Identifier>,
    ) -> InheritanceTable {
        InheritanceTable {
            class: class_names.map(|name| (name, Default::default())).collect(),
            interface: interface_names
                .map(|name| (name, Default::default()))
                .collect(),
        }
    }
}

#[derive(Debug)]
pub struct SymbolTable {
    pub class_to_fields: HashMap<Identifier, Fields>,
    // pub declaration_to_methods: HashMap<Identifier, DeclarationMember>,
    inheritance_table: InheritanceTable,

    pub declarations: HashMap<Identifier, Declaration>,
    pub decl_to_instance_types: HashMap<Identifier, Vec<Identifier>>,
    pub subtypes: HashMap<Identifier, Vec<Identifier>>
}

impl SymbolTable {
    pub fn from_ast(compilation_unit: &CompilationUnit) -> Result<SymbolTable, SymbolError> {
        let mut class_to_fields = HashMap::new();
        let class_names = compilation_unit.members.iter().filter_map(|d| {
            if let Declaration::Class(c) = d {
                Some(c.name.clone())
            } else {
                None
            }
        });
        let interface_names = compilation_unit.members.iter().filter_map(|d| {
            if let Declaration::Interface(i) = d {
                Some(i.name.clone())
            } else {
                None
            }
        });
        let mut it: InheritanceTable = InheritanceTable::new(class_names, interface_names);

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
                        let extend_class =
                            Self::get_class_from_declarations(&declarations, &extends_name)?;

                        it.class.get_mut(decl_name).unwrap().extends = Some(extend_class);
                        it.class.get_mut(extends_name).unwrap().subclasses.push(class.clone());
                    } else {
                        it.class.get_mut(decl_name).unwrap().extends = None;
                    }
                    for interface_name in class.implements.iter() {
                        let interface = Self::get_interface(&declarations, &interface_name)?;
                        it.interface.get_mut(&interface.name).unwrap().implemented
                            .push(class.clone());
                        it.class.get_mut(decl_name).unwrap().implements
                            .push(interface);
                    }
                }
                Declaration::Interface(interface) => {
                    for interface_name in &interface.extends {
                        let extend_interface = Self::get_interface(&declarations, &interface_name)?;
                        it.interface.get_mut(decl_name).unwrap().extends
                            .push(extend_interface);
                        it.interface.get_mut(interface_name).unwrap().subinterfaces
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
                let derived_classes = Self::derived_declarations(decl.clone(), &it)
                    .into_iter()
                    .filter_map(|d| d.try_into_class())
                    .map(|class| class.name.clone())
                    .unique()
                    .collect_vec();
                (name.clone(), derived_classes)
            })
            .collect::<HashMap<_, _>>();
        
        let subtypes = declarations
        .iter()
        .map(|(name, decl)| {
            let derived_classes = Self::derived_declarations(decl.clone(), &it)
                .into_iter()
                .map(|d| d.name().clone())
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
            subtypes
        })
    }

    pub fn get_all_fields(&self, class_name: &Identifier) -> &Fields {
        &self.class_to_fields[class_name]
    }

    /// Returns class_name and all subclasses of class_name,
    /// in other words all possible instance types for this class.
    pub fn get_all_instance_types(&self, class_name: &Identifier) -> &Vec<Identifier> {
        &self.decl_to_instance_types[class_name]
    }

    pub fn lookup_field(&self, class_name: &Identifier, field: &str) -> Option<&Field> {
        self.class_to_fields[class_name]
            .iter()
            .find(|(f, _)| *f == field)
    }

    pub fn get_class(&self, class_name: &Identifier) -> Result<Rc<Class>, SymbolError> {
        Self::get_class_from_declarations(&self.declarations, class_name)
    }

    pub fn class_extends(&self, class_name: &Identifier) -> Option<Rc<Class>> {
        self.inheritance_table.class[class_name].extends.clone()
    }

    pub fn class_implements(&self, class_name: &Identifier) -> &Vec<Rc<Interface>> {
        &self.inheritance_table.class[class_name].implements
    }

    pub fn interface_implemented(&self, interface_name: &Identifier) -> &Vec<Rc<Class>> {
        &self.inheritance_table.interface[interface_name].implemented
    }

    pub fn subclasses(&self, class_name: &Identifier) -> &Vec<Rc<Class>> {
        &self.inheritance_table.class[class_name].subclasses
    }

    pub fn interface_extends(&self, interface_name: &Identifier) -> &Vec<Rc<Interface>> {
        &self.inheritance_table.interface[interface_name].extends
    }

    fn get_class_from_declarations(
        declarations: &HashMap<Identifier, Declaration>,
        class_name: &Identifier,
    ) -> Result<Rc<Class>, SymbolError> {
        match declarations.get(class_name) {
            Some(Declaration::Class(class)) => Ok(class.clone()),
            Some(Declaration::Interface(_)) => {
                Err(error::expected_class_found_interface(class_name, class_name.get_position()))
            }

            None => Err(error::class_does_not_exist(class_name, class_name.get_position())),
        }
    }

    fn get_interface(
        declarations: &HashMap<Identifier, Declaration>,
        interface_name: &Identifier,
    ) -> Result<Rc<Interface>, SymbolError> {
        match declarations.get(interface_name) {
            Some(Declaration::Interface(interface)) => Ok(interface.clone()),
            Some(Declaration::Class(_)) => {
                Err(error::expected_interface_found_class(interface_name, interface_name.get_position()))
            }

            None => Err(error::class_does_not_exist(interface_name, interface_name.get_position())),
        }
    }

    // pub fn lookup_method(&self, class_name: &str, method_name: &str) -> Option<

    // pub fn match_method(&self, class_name: &str, method_name: &str, return_type: RuntimeType, arg_types: Vec<RuntimeType>) {
    //     self.lookupMethod
    // }

    /// Get all derived declarations of the declaration
    /// This includes childs of child etc.
    fn derived_declarations<'a>(
        declaration: Declaration,
        it: &InheritanceTable,
    ) -> Vec<Declaration> {
        let derived_classes = match declaration {
            Declaration::Class(class) => class_helper(class, it),
            Declaration::Interface(interface) => interface_helper(interface, it),
        };

        fn class_helper(
            subclass: Rc<syntax::Class>,
            it: &InheritanceTable,
        ) -> Vec<Declaration> {
            let subclasses = &it.class[&subclass.name].subclasses;
            std::iter::once(Declaration::Class(subclass.clone()))
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
        ) -> Vec<Declaration> {
            let implemented = &it.interface[&subinterface.name].implemented;
            let subinterfaces = &it.interface[&subinterface.name].subinterfaces;

            let subclasses_from_subclasses = implemented
                .iter()
                .cloned()
                .flat_map(|implemented| class_helper(implemented, it));
            let subclasses_from_interfaces = subinterfaces
                .iter()
                .cloned()
                .flat_map(|subinterface| interface_helper(subinterface, it))
                .into_iter();

            std::iter::once(Declaration::Interface(subinterface.clone()))
            .chain(
            subclasses_from_subclasses
                .chain(subclasses_from_interfaces))
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
                DeclarationMember::Field { type_, name, .. } => {
                    fields.push((name.to_owned(), type_.to_owned()))
                }
                _ => (),
            };
        }

        if let Some(extends) = it.class[&class.name].extends.clone() {
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
