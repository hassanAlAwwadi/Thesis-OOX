// since the class and method declaration must be inserted into the abstract syntax tree, this mess is needed.

use std::{borrow::BorrowMut, cell::RefCell, collections::HashMap, ops::Deref, rc::Rc};

use itertools::Itertools;

use crate::syntax::{
    self, Class, CompilationUnit, Declaration, DeclarationMember, Identifier, Interface,
    Invocation, NonVoidType, Parameter, Rhs, RuntimeType, Specification, Statement,
    UnresolvedClass, UnresolvedDeclaration, UnresolvedInterface,
};

pub fn set_resolvers(
    compilation_unit: CompilationUnit<UnresolvedDeclaration>,
) -> CompilationUnit<Declaration> {
    let members = resolve_inheritance(compilation_unit.members);

    // dbg!(&members);

    let mut compilation_unit = CompilationUnit { members };

    let old_members = compilation_unit.members.clone();

    for declaration in compilation_unit.members.iter_mut() {
        match declaration {
            Declaration::Class(class) => {
                let syntax::Class {
                    name,
                    members,
                    extends,
                    implements,
                    subclasses,
                } = class.as_ref().clone();
                let members = members
                    .into_iter()
                    .map(|dcl| match dcl.as_ref().clone() {
                        DeclarationMember::Method {
                            name: method_name,
                            body,
                            params,
                            is_static,
                            return_type,
                            specification,
                        } => {
                            let mut local_variables: HashMap<&String, NonVoidType> = HashMap::new(); // 'this' must also be set
                            for param in &params {
                                local_variables.insert(&param.name, param.type_.to_owned());
                            }
                            let mut new_body = body;
                            helper(
                                &mut new_body,
                                &old_members,
                                &name,
                                &mut local_variables,
                                extends.clone(),
                                &implements
                            );

                            DeclarationMember::Method {
                                name: method_name,
                                body: new_body,
                                params,
                                is_static,
                                return_type,
                                specification,
                            }
                        }
                        DeclarationMember::Constructor {
                            name,
                            params,
                            body,
                            specification,
                        } => {
                            let mut local_variables: HashMap<&String, NonVoidType> = HashMap::new(); // 'this' must also be set
                            for param in &params {
                                local_variables.insert(&param.name, param.type_.to_owned());
                            }
                            let mut new_body = body;
                            helper(
                                &mut new_body,
                                &old_members,
                                &name,
                                &mut local_variables,
                                extends.clone(),
                                &implements
                            );

                            DeclarationMember::Constructor {
                                body: new_body,
                                name,
                                params,
                                specification,
                            }
                        }
                        field => field,
                    })
                    .map(Rc::new)
                    .collect_vec();

                *class = Rc::new(
                    syntax::Class {
                        name,
                        members,
                        extends,
                        implements,
                        subclasses,
                    }
                    .into(),
                );
            }
            Declaration::Interface(interface) => {
                let mut new_interface = interface.as_ref().clone();
                let members = interface.members.iter().map(|member| match member.as_ref() {
                    syntax::InterfaceMember::Method(method) => {
                        let method = method.clone();
                        let mut local_variables: HashMap<&String, NonVoidType> = HashMap::new(); // 'this' must also be set
                        for param in &method.parameters {
                            local_variables.insert(&param.name, param.type_.to_owned());
                        }
                        if let Some(body) = method.body {
                            let mut new_body = body;
                            helper(
                                &mut new_body,
                                &old_members,
                                &interface.name,
                                &mut local_variables,
                                None,
                                &interface.extends
                            );
                            
                            Rc::new(syntax::InterfaceMember::Method(syntax::InterfaceMethod { body: Some(new_body), ..method }))
                        } else {
                            member.clone()
                        }
                            
                    },
                }).collect_vec();

                new_interface.members = members;
                *interface = Rc::new(new_interface);
            },
        }
    }
    compilation_unit
}

/// Set resolvers in the body statement
fn helper<'a>(
    statement: &'a mut Statement,
    declarations: &Vec<Declaration>,
    class_name: &String,
    local_variables: &mut HashMap<&'a String, NonVoidType>,
    extended_classes: Option<Rc<syntax::Class>>,
    implemented_interfaces: &Vec<Rc<syntax::Interface>>,
) {
    match statement {
        Statement::Call { invocation } => {
            match invocation {
                Invocation::InvokeSuperMethod { resolved, rhs, .. } => {
                    super_method_call_helper(resolved, declarations, class_name, &rhs)
                }
                Invocation::InvokeMethod {
                    lhs, rhs, resolved, ..
                } => {
                    if lhs == "this" {
                        method_call_helper(resolved, declarations, class_name, &rhs);
                    } else if let Some(NonVoidType::ReferenceType { identifier }) =
                        &local_variables.get(lhs)
                    {
                        // This is a normal method call
                        method_call_helper(resolved, declarations, identifier, &rhs);
                    } else {
                        // This is a static method call on a class
                        method_call_helper(resolved, declarations, &lhs, &rhs);
                    }
                }
                Invocation::InvokeConstructor {
                    class_name,
                    resolved,
                    ..
                } => constructor_call_helper(resolved, declarations, class_name),
                Invocation::InvokeSuperConstructor { resolved, .. } => {
                    constructor_super_call_helper(class_name, resolved, extended_classes)
                }
            }
        }

        Statement::Assign {
            lhs: _,
            rhs: Rhs::RhsCall { invocation, .. },
        } => {
            match invocation {
                Invocation::InvokeMethod {
                    lhs,
                    rhs,
                    arguments,
                    resolved,
                } => {
                    if let Some(NonVoidType::ReferenceType { identifier }) =
                        &local_variables.get(lhs)
                    {
                        // This is a normal method call
                        method_call_helper(resolved, declarations, identifier, &rhs);
                    } else {
                        // This is a static method call on a class
                        method_call_helper(resolved, declarations, &lhs, &rhs);
                    }
                }
                Invocation::InvokeConstructor {
                    class_name,
                    resolved,
                    ..
                } => {
                    constructor_call_helper(resolved, declarations, class_name);
                }
                _ => todo!(),
            }
        }
        Statement::Ite {
            guard,
            true_body,
            false_body,
        } => {
            helper(
                true_body,
                declarations,
                class_name,
                local_variables,
                extended_classes.clone(),
                implemented_interfaces
            );
            helper(
                false_body,
                declarations,
                class_name,
                local_variables,
                extended_classes,
                implemented_interfaces
            );
        }
        Statement::Seq { stat1, stat2 } => {
            helper(
                stat1,
                declarations,
                class_name,
                local_variables,
                extended_classes.clone(),
                implemented_interfaces
            );
            helper(stat2, declarations, class_name, local_variables, extended_classes,
                implemented_interfaces);
        }
        Statement::While { guard, body } => {
            helper(body, declarations, class_name, local_variables, extended_classes,
                implemented_interfaces);
        }
        Statement::Throw { .. } => (),
        Statement::Try {
            try_body,
            catch_body,
        } => {
            helper(
                try_body,
                declarations,
                class_name,
                local_variables,
                extended_classes.clone(),
                implemented_interfaces
            );
            helper(
                catch_body,
                declarations,
                class_name,
                local_variables,
                extended_classes,
                implemented_interfaces
            );
        }
        Statement::Block { body } => todo!(),
        Statement::Declare { type_, var } => {
            local_variables.insert(var, type_.clone());
        }
        _ => (),
    }

    // super.method()
    fn super_method_call_helper(
        resolved: &mut Option<Box<(Declaration, Rc<DeclarationMember>)>>,
        declarations: &Vec<Declaration>,
        class_name: &String,
        method_name: &String,
    ) {
        let declaration = find_declaration(class_name, declarations).unwrap();

        let class = declaration
            .as_class()
            .expect("cannot call super.method() for interface methods");

        let extends = class
            .extends
            .as_ref()
            .expect("expected at least one superclass")
            .clone();

        let (_super_class_name, super_class_method) = method_in_superclass(extends, method_name)
            .expect("at least one superclass should have this method");

        *resolved = Some(Box::new(super_class_method));
    }

    /// This method resolves the invocation by finding the declaration corresponding to the class type.
    /// Then it looks for any method that could be called by this invocation
    /// either by superclasses or subclasses.
    ///
    /// In case of an interface it works similarly, but searches for default implementations,
    /// and then resolves those default implementations to any class that does not override it.
    /// Or
    ///
    ///
    /// The result is added to resolved.
    #[inline(always)]
    fn method_call_helper(
        resolved: &mut Option<HashMap<Identifier, (Declaration, Rc<DeclarationMember>)>>,
        declarations: &Vec<Declaration>,
        class_name: &String,
        method_name: &String,
    ) {
        // dbg!(declarations, class_name, method_name);
        let decl = find_declaration(class_name, declarations).unwrap();

        // Check if class itself contains the method in question
        match decl {
            Declaration::Class(class) => {
                let method = find_method(&method_name, &class.members);

                let class_contains_method = method.is_some();

                let mut resolved_so_far = HashMap::new();

                // Find other potential methods in superclasses and subclasses

                // superclasses
                let overridable = if !class_contains_method {
                    if let Some(extends) = &class.extends {
                        // The method is not overridden by this class, check superclasses for the method
                        let (super_class_name, super_class_method) =
                            method_in_superclass(extends.clone(), method_name)
                                .expect("at least one superclass should have this method");
                        resolved_so_far.insert(class_name.clone(), super_class_method.clone());
                        super_class_method
                    } else {
                        // Method not found in superclass, but perhaps in interfaces there is a default implementation.
                        if let Some((interface_name, interface_method)) =
                            method_in_interfaces(&class.implements, method_name)
                        {
                            interface_method
                        } else {
                            panic!(
                                "Method {:?} is not found in class or any superclass, or interfaces for {:?}",
                                method_name, class_name
                            )
                        }
                    }
                } else {
                    (Declaration::Class(class.clone()), method.unwrap())
                };

                resolved_so_far.extend(
                    methods_in_subclasses(class, method_name, Some(overridable)).into_iter(),
                );

                *resolved = Some(resolved_so_far);
            }
            Declaration::Interface(interface) => {
                // IFoo foo;
                // foo.method();
                let overridable_method = method_in_interface(interface.clone(), method_name);

                let resolved_so_far = interface
                    .implemented
                    .borrow()
                    .iter()
                    .flat_map(|class| {
                        methods_in_subclasses(
                            class.clone(),
                            method_name,
                            overridable_method
                                .as_ref()
                                .map(|(_, method)| method.clone()),
                        )
                        .into_iter()
                    })
                    .collect();
                *resolved = Some(resolved_so_far);
            }
        }
    }

    fn find_declaration(
        decl_name: &String,
        declarations: &Vec<Declaration>,
    ) -> Option<Declaration> {
        declarations
            .iter()
            .filter_map(|declaration| match declaration {
                Declaration::Class(class) if *decl_name == class.name => {
                    Some(Declaration::Class(class.clone()))
                }
                Declaration::Interface(interface) if *decl_name == interface.name => {
                    Some(Declaration::Interface(interface.clone()))
                }
                _ => None,
            })
            .next()
    }

    fn find_method(
        method_name: &str,
        members: &Vec<Rc<DeclarationMember>>,
    ) -> Option<Rc<DeclarationMember>> {
        members
            .iter()
            .find(|member| {
                if let DeclarationMember::Method { name, .. } = member.as_ref() {
                    name == method_name
                } else {
                    false
                }
            })
            .cloned()
    }

    /// Find the first method with the name method_name
    /// in the chain of superclasses, or return None
    ///
    fn method_in_superclass(
        superclass: Rc<syntax::Class>,
        method_name: &str,
    ) -> Option<(Identifier, (Declaration, Rc<DeclarationMember>))> {
        // Find the first superclass (in the chain) with the method
        let method = find_method(method_name, &superclass.members);
        if let Some(method) = method {
            // Stop on the first overriden method in the chain.
            Some((
                superclass.name.to_string(),
                (Declaration::Class(superclass), method),
            ))
        } else if let Some(superclass) = superclass.extends.clone() {
            method_in_superclass(superclass, method_name)
        } else {
            None
        }
    }

    /// Finds all (declaration, method) pairs that match the method_name
    /// in the subclasses of class,
    /// Returns for each subclass what method it resolves to
    fn methods_in_subclasses(
        class: Rc<Class>,
        method_name: &str,
        overridable: Option<(Declaration, Rc<DeclarationMember>)>,
    ) -> HashMap<Identifier, (Declaration, Rc<DeclarationMember>)> {
        let method = find_method(method_name, &class.members);
        let mut methods = if let Some(method) = method.clone() {
            // this class contains the method, assign it to the type
            HashMap::from([(
                class.name.clone(),
                (Declaration::Class(class.clone()), method),
            )])
        } else {
            if let Some(overridable) = overridable.clone() {
                // this class does not contain the method, assign it to the overridable
                HashMap::from([(class.name.clone(), overridable.clone())]) // MUST class.name NOT BE OF OVERRIDABLE TYPE?
            } else {
                panic!("this class does not contain the method, but there is no method to inherit");
            }
        };

        // set new overridable to the method of this class if available, otherwise take the method from superclass.
        let overridable = method
            .map(|method: Rc<DeclarationMember>| (Declaration::Class(class.clone()), method))
            .or(overridable);

        methods.extend(class.subclasses.borrow().iter().flat_map(|subclass| {
            methods_in_subclasses(subclass.clone(), method_name, overridable.clone()).into_iter()
        }));
        methods
    }

    fn method_in_interfaces(
        interfaces: &Vec<Rc<Interface>>,
        method_name: &str,
    ) -> Option<(Identifier, (Declaration, Rc<DeclarationMember>))> {
        interfaces
            .iter()
            .map(|superinterface| method_in_interface(superinterface.clone(), method_name))
            .find_map(|result| result)
    }

    /// Try to find the method in the interface, or any of its extended interfaces.
    /// If a non-default method is encountered, (i.e. unimplemented method),
    /// we return None since this means that the classes/interfaces below must override it.
    ///
    /// We choose the first default implementation we find, but note that this may not be semantically correct.
    fn method_in_interface(
        interface: Rc<Interface>,
        method_name: &str,
    ) -> Option<(Identifier, (Declaration, Rc<DeclarationMember>))> {
        let method = syntax::find_interface_method(&method_name, &interface.members);

        if let Some(method) = method {
            if let Some(body) = method.body.clone() {
                Some((
                    interface.name.clone(),
                    (
                        Declaration::Interface(interface.clone()),
                        DeclarationMember::Method {
                            // this is suboptimal
                            is_static: false,
                            return_type: method.type_.clone(),
                            name: method.name.clone(),
                            params: method.parameters.clone(),
                            specification: Specification::default(),
                            body,
                        }
                        .into(),
                    ),
                ))
            } else {
                // Abstract method defined in this interface, no need to look in superinterfaces, but cannot provide overridable.
                None
            }
        } else {
            // find first non-default method in superinterfaces, or none.
            method_in_interfaces(&interface.extends, method_name)
        }
    }

    fn constructor_call_helper(
        resolved: &mut Option<Box<(Declaration, Rc<DeclarationMember>)>>,
        declarations: &Vec<Declaration>,
        called_constructor: &String,
    ) {
        for declaration in declarations {
            if let Declaration::Class(class) = declaration {
                for member in &class.members {
                    if let DeclarationMember::Constructor {
                        name: constructor_name,
                        ..
                    } = member.as_ref()
                    {
                        //dbg!("{:?}, {:?}, {:?}, {:?}", lhs, rhs, class_name, member_name);
                        if called_constructor == constructor_name {
                            *resolved = Some(Box::new((
                                Declaration::Class(class.clone()),
                                member.clone(),
                            )));
                            // very bad
                        }
                    }
                }
            }
        }
    }

    fn constructor_super_call_helper(
        class_name: &String,
        resolved: &mut Option<Box<(Declaration, Rc<DeclarationMember>)>>,
        extends: Option<Rc<syntax::Class>>,
    ) {
        let extends =
            extends.expect("super() found in constructor but class does not extend other class");

        for member in &extends.members {
            if let DeclarationMember::Constructor { .. } = member.as_ref() {
                *resolved = Some(Box::new((
                    Declaration::Class(extends.clone()),
                    member.clone(),
                )));
                // very bad
            }
        }
    }
}

/// A function that resolves declarations
fn resolve_inheritance(unresolved: Vec<UnresolvedDeclaration>) -> Vec<Declaration> {
    use UnresolvedDeclaration::*;

    let resolved_interfaces = resolve_interfaces(&unresolved);

    // dbg!(&resolved_interfaces);

    let classes_that_dont_extend = unresolved
        .iter()
        .filter_map(|u| {
            if let Class(class) = u {
                if class.extends.is_none() {
                    return Some(class);
                }
            }
            None
        })
        .collect_vec();
    let mut classes_that_do_extend = unresolved
        .iter()
        .filter_map(|u| {
            if let Class(class) = u {
                if class.extends.is_some() {
                    return Some(class);
                }
            }
            None
        })
        .collect_vec();

    let mut resolved = classes_that_dont_extend
        .iter()
        .copied()
        .map(|u| {
            let UnresolvedClass { name, members, implements, .. } = u.clone();

            let implements = find_interfaces(&implements, &resolved_interfaces)
            .expect("unresolved interface");

            let class = Rc::new(syntax::Class {
                name,
                extends: None,
                subclasses: RefCell::new(Vec::new()),
                implements: implements.clone(),
                members,
            });
            for interface in implements {
                interface.implemented.borrow_mut().push(class.clone());
            }
            class
        })
        .collect_vec();

    let max_iterations = 1000;
    let mut i = 0;
    loop {
        classes_that_do_extend.retain(|class| {
            let UnresolvedClass {
                name,
                extends,
                members,
                implements,
            } = class;

            let extends = extends.as_ref().unwrap().clone();
            let class_it_extends = resolved.iter().find(|class| extends == class.name).cloned();

            if let Some(class_it_extends) = class_it_extends {
                // Resolve implements
                let implements = find_interfaces(&implements, &resolved_interfaces)
                    .expect("unresolved interface");

                let resolved_class = Rc::new(syntax::Class {
                    name: name.clone(),
                    extends: Some(class_it_extends.clone()),
                    subclasses: RefCell::new(Vec::new()),
                    members: members.clone(),
                    implements: implements.clone(),
                });
                resolved.push(resolved_class.clone());
                // Also add this class to the list of extended classes of the superclass.
                let syntax::Class { subclasses, .. } = class_it_extends.as_ref();
                subclasses.borrow_mut().push(resolved_class.clone());

                for interface in implements {
                    interface
                        .implemented
                        .borrow_mut()
                        .push(resolved_class.clone());
                }

                false
            } else {
                true
            }
        });
        if classes_that_do_extend.len() == 0 {
            return resolved
                .into_iter()
                .map(Declaration::Class)
                .chain(resolved_interfaces.into_iter().map(Declaration::Interface))
                .collect_vec();
        }

        i += 1;
        if i == max_iterations {
            panic!("max iterations reached");
        }
    }
}

/// Returns Some if all interfaces are found, otherwise returns None
fn find_interfaces(interface_names: &[String], interfaces: &Vec<Rc<Interface>>) -> Option<Vec<Rc<Interface>>> {
    interface_names
        .iter()
        .map(|interface_name| {
            interfaces
                .iter()
                .cloned()
                .find(|i| i.name == *interface_name)
        })
        .collect::<Option<Vec<_>>>()
}

/// Assumes no cyclic inheritance between interfaces
fn resolve_interfaces(unresolved: &Vec<UnresolvedDeclaration>) -> Vec<Rc<Interface>> {
    let interfaces_that_dont_extend = unresolved
        .iter()
        .filter_map(|declaration| {
            if let UnresolvedDeclaration::Interface(UnresolvedInterface {
                name,
                extends,
                members,
            }) = declaration.clone()
            {
                if extends.is_empty() {
                    return Some(Rc::new(Interface {
                        name,
                        extends: Vec::new(),
                        subinterfaces: Default::default(),
                        implemented: Default::default(),
                        members,
                    }));
                }
            }
            None
        })
        .collect_vec();

    let mut interfaces_that_extend = unresolved
        .iter()
        .filter_map(|declaration| {
            if let UnresolvedDeclaration::Interface(interface) = declaration.clone() {
                if !interface.extends.is_empty() {
                    return Some(interface);
                }
            }
            None
        })
        .collect_vec();

    let mut resolved = interfaces_that_dont_extend;

    loop {
        interfaces_that_extend.retain(|declaration| {
            let UnresolvedInterface {
                name,
                extends,
                members,
            } = declaration;
            // try to find all extend interfaces
            let resolved_extends = extends
                .iter()
                .map(|interface_name| {
                    resolved
                        .iter()
                        .cloned()
                        .find(|resolved_interface| resolved_interface.name == *interface_name)
                })
                .collect::<Option<Vec<_>>>();

            if let Some(resolved_extends) = resolved_extends {
                // All its parent interfaces are already resolved so we can resolve this one
                let resolved_interface = Rc::new(syntax::Interface {
                    name: name.clone(),
                    extends: resolved_extends.clone(),
                    subinterfaces: RefCell::new(Vec::new()),
                    implemented: RefCell::new(Vec::new()),
                    members: members.clone(),
                });
                resolved.push(resolved_interface.clone());

                for extended_interface in resolved_extends {
                    extended_interface
                        .subinterfaces
                        .borrow_mut()
                        .push(resolved_interface.clone());
                }

                false
            } else {
                // Can't resolve yet since not all parent interfaces are resolved, continue
                true
            }
        });
        if interfaces_that_extend.len() == 0 {
            return resolved.into_iter().collect_vec();
        }
    }
}
