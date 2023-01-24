// since the class and method declaration must be inserted into the abstract syntax tree, this mess is needed.

use std::{cell::RefCell, collections::HashMap, ops::Deref, rc::Rc};

use itertools::Itertools;

use crate::syntax::{
    CompilationUnit, Declaration, DeclarationMember, Invocation, NonVoidType, Parameter, Rhs,
    RuntimeType, Statement, UnresolvedDeclaration,
};

pub fn set_resolvers(
    compilation_unit: CompilationUnit<UnresolvedDeclaration>,
) -> CompilationUnit<Declaration> {
    let members = resolve_inheritance(compilation_unit.members);

    let mut compilation_unit = CompilationUnit { members };

    let old_members = compilation_unit.members.clone();

    for class in compilation_unit.members.iter_mut() {
        let Declaration::Class {
            name,
            mut members,
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
                        extends.as_ref(),
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
                        extends.as_ref(),
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

        *class = Rc::new(Declaration::Class {
            name,
            members,
            extends,
            implements,
            subclasses,
        });
    }
    compilation_unit
}

/// Set resolvers in the body statement
fn helper<'a>(
    statement: &'a mut Statement,
    declarations: &Vec<Rc<Declaration>>,
    class_name: &String,
    local_variables: &mut HashMap<&'a String, NonVoidType>,
    extends: Option<&Rc<Declaration>>,
) {
    match statement {
        Statement::Call { invocation } => {
            match invocation {
                Invocation::InvokeMethod {
                    lhs, rhs, resolved, ..
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
                } => constructor_call_helper(resolved, declarations, class_name),
                Invocation::InvokeSuperConstructor { resolved, .. } => {
                    constructor_super_call_helper(class_name, resolved, extends)
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
                extends,
            );
            helper(
                false_body,
                declarations,
                class_name,
                local_variables,
                extends,
            );
        }
        Statement::Seq { stat1, stat2 } => {
            helper(stat1, declarations, class_name, local_variables, extends);
            helper(stat2, declarations, class_name, local_variables, extends);
        }
        Statement::While { guard, body } => {
            helper(body, declarations, class_name, local_variables, extends);
        }
        Statement::Throw { .. } => (),
        Statement::Try {
            try_body,
            catch_body,
        } => {
            helper(try_body, declarations, class_name, local_variables, extends);
            helper(
                catch_body,
                declarations,
                class_name,
                local_variables,
                extends,
            );
        }
        Statement::Block { body } => todo!(),
        Statement::Declare { type_, var } => {
            local_variables.insert(var, type_.clone());
        }
        _ => (),
    }

    /// This method resolves the invocation by finding the declaration corresponding to the class type.
    /// Then it looks for any method that could be called by this invocation
    /// either by superclasses or subclasses.
    ///
    /// The result is added to resolved.
    #[inline(always)]
    fn method_call_helper(
        resolved: &mut Option<Vec<(Declaration, Rc<DeclarationMember>)>>,
        declarations: &Vec<Rc<Declaration>>,
        class_name: &String,
        method_name: &String,
    ) {
        let class = declarations
            .iter()
            .find(|declaration| {
                let Declaration::Class { name, .. } = declaration.as_ref();
                class_name == name
            })
            .unwrap();

        let Declaration::Class {
            name: other_class_name,
            members,
            extends,
            subclasses,
            ..
        } = class.as_ref();

        let method = members.iter().find(|member| {
            if let DeclarationMember::Method { name, .. } = member.as_ref() {
                name == method_name
            } else {
                false
            }
        }).unwrap();

        let mut resolved_so_far = vec![(class.as_ref().clone(), method.clone())];

        // Find other potential methods in superclasses and subclasses


        *resolved = Some(resolved_so_far);
    }

    fn constructor_call_helper(
        resolved: &mut Option<Box<(Declaration, Rc<DeclarationMember>)>>,
        declarations: &Vec<Rc<Declaration>>,
        called_constructor: &String,
    ) {
        for class in declarations {
            let Declaration::Class { members, .. } = class.as_ref();
            for member in members {
                if let DeclarationMember::Constructor {
                    name: constructor_name,
                    ..
                } = member.as_ref()
                {
                    //dbg!("{:?}, {:?}, {:?}, {:?}", lhs, rhs, class_name, member_name);
                    if called_constructor == constructor_name {
                        *resolved = Some(Box::new((class.as_ref().clone(), member.clone())));
                        // very bad
                    }
                }
            }
        }
    }

    fn constructor_super_call_helper(
        class_name: &String,
        resolved: &mut Option<Box<(Declaration, Rc<DeclarationMember>)>>,
        extends: Option<&Rc<Declaration>>,
    ) {
        let extends =
            extends.expect("super() found in constructor but class does not extend other class");
        // *resolved = Some(Box::new())

        let Declaration::Class { members, .. } = extends.as_ref();

        for member in members {
            if let DeclarationMember::Constructor { .. } = member.as_ref() {
                *resolved = Some(Box::new((extends.as_ref().clone(), member.clone())));
                // very bad
            }
        }
    }
}

/// A function that resolves declarations
fn resolve_inheritance(mut unresolved: Vec<Rc<UnresolvedDeclaration>>) -> Vec<Rc<Declaration>> {
    use UnresolvedDeclaration::*;

    let classes_that_dont_extend = unresolved
        .iter()
        .filter(|u| {
            let Class {
                extends,
                implements,
                ..
            } = u.as_ref();
            extends.is_none()
        })
        .collect_vec();
    let mut classes_that_do_extend = unresolved
        .iter()
        .filter(|u| {
            let Class {
                extends,
                implements,
                ..
            } = u.as_ref();
            extends.is_some()
        })
        .collect_vec();

    let mut resolved = classes_that_dont_extend
        .iter()
        .map(|u| {
            let Class {
                name,
                extends,
                implements,
                members,
            } = u.as_ref().clone();
            Rc::new(Declaration::Class {
                name,
                extends: None,
                subclasses: RefCell::new(Vec::new()),
                implements: vec![],
                members,
            })
        })
        .collect_vec();

    loop {
        classes_that_do_extend.retain(|class| {
            let Class {
                name,
                extends,
                members,
                ..
            } = class.as_ref();
            let extends = extends.as_ref().unwrap().clone();
            let class_it_extends = resolved.iter().find(|d| {
                let Declaration::Class {
                    name: other_class_name,
                    ..
                } = d.as_ref();
                &extends == other_class_name
            }).cloned();

            if let Some(class_it_extends) = class_it_extends {
                let resolved_class = Rc::new(Declaration::Class {
                    name: name.clone(),
                    extends: Some(class_it_extends.clone()),
                    subclasses: RefCell::new(Vec::new()),
                    members: members.clone(),
                    implements: vec![],
                });
                resolved.push(resolved_class.clone());
                // Also add this class to the list of extended classes of the superclass.
                let Declaration::Class { subclasses, .. } = class_it_extends.as_ref();
                subclasses.borrow_mut().push(resolved_class);

                false
            } else {
                true
            }
        });
        if classes_that_do_extend.len() == 0 {
            return resolved;
        }
    }
}
