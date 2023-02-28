// since the class and method declaration must be inserted into the abstract syntax tree, this mess is needed.

use std::{collections::HashMap, rc::Rc};

use itertools::{Either, Itertools};

use crate::{
    error,
    positioned::WithPosition,
    symbol_table::SymbolTable,
    syntax::{
        self, Class, Declaration, DeclarationMember, Expression, Identifier, Interface, Method,
    },
    typeable::Typeable,
};

pub type ResolveError = String;

/// Resolves the invocation of a method call on an object e.g. `a.method()`.
/// It returns a mapping from runtimetype class to concrete method.
/// Any class that `a` may represent at runtime will be in this mapping.
#[inline(always)]
fn method_call_helper(
    decl_name: &Identifier,
    method_name: &Identifier,
    st: &SymbolTable,
) -> Result<HashMap<Identifier, (Declaration, Rc<Method>)>, ResolveError> {
    let decl = &st.declarations[decl_name];

    // Check if class itself contains the method in question
    match decl {
        Declaration::Class(class) => {
            let method = find_method(&method_name, &class.members);

            let class_contains_method = method.is_some();

            let mut resolved_so_far = HashMap::new();

            // Find other potential methods in superclasses and subclasses

            // superclasses
            let method = if !class_contains_method {
                if let Some(extends) = st.class_extends(&class.name) {
                    // The method is not overridden by this class, check superclasses for the method
                    let (_super_class_name, super_class_method) =
                        method_in_superclass(extends.clone(), method_name, st).ok_or_else(
                            || {
                                error::at_least_one_superclass_should_have_this_method(
                                    &class.name,
                                    method_name,
                                    method_name.get_position(),
                                )
                            },
                        )?;
                    // Class found, current class resolves to that superclass method
                    super_class_method
                } else {
                    // Method not found in superclass, but perhaps in interfaces there is a default implementation.
                    match method_in_interfaces(st.class_implements(&class.name), method_name, st) {
                        Either::Left(Some((_interface_name, interface_method))) => interface_method,
                        _ => {
                            // Method not found in any of the interfaces
                            return Err(error::could_not_resolve_method(
                                &class.name,
                                method_name,
                                method_name.get_position(),
                            ));
                        }
                    }
                }
            } else {
                resolved_so_far.insert(
                    class.name.clone(),
                    (Declaration::Class(class.clone()), method.clone().unwrap()),
                );
                (Declaration::Class(class.clone()), method.unwrap())
            };

            // Method found, current class resolves to that method
            resolved_so_far.insert(class.name.clone(), method.clone());

            let overridable = method;

            let subclass_methods =
                methods_in_subclasses(class.clone(), method_name, Some(overridable), st)?;
            resolved_so_far.extend(subclass_methods);

            return Ok(resolved_so_far);
        }
        Declaration::Interface(interface) => {
            // IFoo foo;
            // foo.method();

            let overridable_method = method_in_interface(interface.clone(), method_name, st)
                .left()
                .ok_or(error::could_not_resolve_method(
                    &interface.name,
                    method_name,
                    method_name.get_position(),
                ))?;

            let resolved_so_far = st
                .interface_implemented(&interface.name)
                .iter()
                .map(|class| {
                    methods_in_subclasses(
                        class.clone(),
                        method_name,
                        overridable_method
                            .as_ref()
                            .map(|(_, method)| method.clone()),
                        st,
                    )
                })
                .flatten_ok()
                .collect::<Result<HashMap<_, _>, _>>()?;
            return Ok(resolved_so_far);
        }
    }
}

fn find_declaration(
    decl_name: &Identifier,
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

/// Finds first normal Method, non-constructor, with given name
fn find_method(method_name: &str, members: &Vec<DeclarationMember>) -> Option<Rc<Method>> {
    members.iter().find_map(|member| {
        if let DeclarationMember::Method(method) = member {
            if method.name == method_name {
                return Some(method.clone());
            }
        }
        None
    })
}

/// Find the first method with the name method_name
/// in the chain of superclasses, or return None
///
fn method_in_superclass(
    superclass: Rc<syntax::Class>,
    method_name: &str,
    st: &SymbolTable,
) -> Option<(Identifier, (Declaration, Rc<Method>))> {
    // Find the first superclass (in the chain) with the method
    let member = find_method(method_name, &superclass.members);

    if let Some(method) = member {
        // Stop on the first overriden method in the chain.
        Some((
            superclass.name.clone(),
            (Declaration::Class(superclass), method.clone()),
        ))
    } else if let Some(superclass) = st.class_extends(&superclass.name).clone() {
        method_in_superclass(superclass, method_name, st)
    } else {
        None
    }
}

/// Finds all (declaration, method) pairs that match the method_name
/// in the subclasses of class,
/// Returns for each subclass what method it resolves to
fn methods_in_subclasses(
    class: Rc<Class>,
    method_name: &Identifier,
    overridable: Option<(Declaration, Rc<Method>)>,
    st: &SymbolTable,
) -> Result<HashMap<Identifier, (Declaration, Rc<Method>)>, ResolveError> {
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
            return Err(error::could_not_resolve_method(
                &class.name,
                method_name,
                method_name.get_position(),
            ));
        }
    };

    // set new overridable to the method of this class if available, otherwise take the method from superclass.
    let overridable = method
        .map(|method| (Declaration::Class(class.clone()), method))
        .or(overridable);

    let subclass_methods = st
        .subclasses(&class.name)
        .iter()
        .map(|subclass| {
            methods_in_subclasses(subclass.clone(), method_name, overridable.clone(), st)
        })
        .flatten_ok()
        .collect::<Result<HashMap<_, _>, _>>()?;
    methods.extend(subclass_methods);
    Ok(methods)
}

/// Tries to find the method_name in the list of interfaces, and their extended interfaces.
///
/// Either return a Left when the method was found, with a Some(..) if it was a default method, None otherwise.
/// Return a Right if the method was not found.
fn method_in_interfaces(
    interfaces: &Vec<Rc<Interface>>,
    method_name: &str,
    st: &SymbolTable,
) -> Either<Option<(Identifier, (Declaration, Rc<Method>))>, ()> {
    let method_declarations = interfaces
        .iter()
        .map(|superinterface| method_in_interface(superinterface.clone(), method_name, st))
        .filter_map(|result| {
            if let Either::Left(result) = result {
                Some(result)
            } else {
                None
            }
        })
        .collect_vec();

    if method_declarations.len() == 0 {
        return Either::Right(());
    }
    Either::Left(method_declarations.into_iter().find_map(|x| x))
}

/// Try to find the method in the interface, or any of its extended interfaces.
/// If a non-default method is encountered, (i.e. unimplemented method),
/// we return None since this means that the classes/interfaces below must override it.
///
/// We choose the first default implementation we find, but note that this may not be semantically correct.
/// Returns Left if the method is found, with or without implementation
/// Returns Right when the method is not found at all (= static semantic error)
fn method_in_interface(
    interface: Rc<Interface>,
    method_name: &str,
    st: &SymbolTable,
) -> Either<Option<(Identifier, (Declaration, Rc<Method>))>, ()> {
    let member = syntax::find_interface_method(&method_name, &interface.members);

    if let Some(member) = member {
        match member {
            syntax::InterfaceMember::DefaultMethod(method) => Either::Left(Some((
                interface.name.clone(),
                (Declaration::Interface(interface.clone()), method),
            ))),
            // Abstract method defined in this interface, no need to look in superinterfaces, but cannot provide overridable.
            syntax::InterfaceMember::AbstractMethod(_method) => Either::Left(None),
        }
    } else {
        // find first non-default method in superinterfaces, or none.
        if interface.extends.len() == 0 {
            return Either::Right(());
        }
        method_in_interfaces(st.interface_extends(&interface.name), method_name, st)
    }
}

pub(crate) fn resolve_method(
    class_name: &Identifier,
    method_name: &Identifier,
    st: &SymbolTable,
) -> Result<HashMap<Identifier, (Declaration, Rc<Method>)>, ResolveError> {
    method_call_helper(class_name, method_name, st)
}

/// Resolves method calls to super methods, `super.method(..)`.
pub fn resolve_super_method(
    class_name: &Identifier,
    method_name: &Identifier,
    st: &SymbolTable,
) -> Result<Box<(Declaration, Rc<Method>)>, ResolveError> {
    let decl = &st.declarations[class_name];

    let class =
        decl.try_into_class()
            .ok_or(error::cannot_call_super_method_on_interface_methods(
                method_name,
                method_name.get_position(),
            ))?;

    let extends = st
        .class_extends(&class.name)
        .as_ref()
        .ok_or(error::expected_superclass(
            class_name,
            method_name,
            method_name.get_position(),
        ))?
        .clone();

    let (_super_class_name, super_class_method) = method_in_superclass(extends, method_name, st)
        .ok_or(error::at_least_one_superclass_should_have_this_method(
            class_name,
            method_name,
            method_name.get_position(),
        ))?;

    Ok(Box::new(super_class_method))
}

/// Resolves constructor calls `new Foo(..)` to their method in the syntax tree.
/// This is needed so we know during symbolic execution what the parameters are,
/// whether the method is static and what its return type is.
pub fn resolve_constructor(
    called_constructor: &Identifier,
    arguments: &Vec<Rc<Expression>>,
    st: &SymbolTable,
) -> Result<Box<(syntax::Declaration, std::rc::Rc<syntax::Method>)>, ResolveError> {
    let class = st.get_class(called_constructor).unwrap();

    for member in &class.members {
        if let DeclarationMember::Constructor(method) = member {
            let method_param_types = method.params.iter().map(Typeable::type_of);

            if *called_constructor == method.name {
                let arguments_match_type = method.params.len() == arguments.len()
                    && method_param_types
                        .zip(arguments.iter())
                        .all(|(x, y)| y.is_of_type(x, st));
                if arguments_match_type {
                    return Ok(Box::new((
                        Declaration::Class(class.clone()),
                        method.clone(),
                    )));
                }
            }
        }
    }
    Err(error::could_not_resolve_constructor(
        called_constructor,
        &arguments.iter().map(|arg| arg.type_of()).collect_vec(),
        called_constructor.get_position(),
    ))
}

pub fn resolve_super_constructor(
    class_name: &Identifier,
    arguments: &Vec<Rc<Expression>>,
    st: &SymbolTable,
) -> Result<Box<(syntax::Declaration, std::rc::Rc<syntax::Method>)>, ResolveError> {
    let extends = st
        .class_extends(class_name)
        .expect("super() found in constructor but class does not extend other class");

    for member in &extends.members {
        if let DeclarationMember::Constructor(method) = member {
            let method_param_types = method.params.iter().map(Typeable::type_of);
            let arguments_match_type = method.params.len() == arguments.len()
                && method_param_types
                    .zip(arguments.iter())
                    .all(|(x, y)| y.is_of_type(x, st));
            if arguments_match_type {
                return Ok(Box::new((
                    Declaration::Class(extends.clone()),
                    method.clone(),
                )));
            }
        }
    }
    Err(error::constructor_not_found_in_superclass(
        class_name,
        &arguments.iter().map(|arg| arg.type_of()).collect_vec(),
        class_name.get_position(),
    ))
}
