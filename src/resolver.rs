// since the class and method declaration must be inserted into the abstract syntax tree, this mess is needed.

use std::{collections::HashMap, ops::Deref, rc::Rc};

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
        } = class.as_ref().clone();

        let method_bodies = members.iter_mut().filter_map(|dcl| match dcl {
            DeclarationMember::Method { name, body, params, .. } => Some((name, body, params)),
            DeclarationMember::Constructor { name, params, body, .. } => Some((name, body, params)),
            _ => None,
        });
        for (method_name, body, params) in method_bodies {
            let mut local_variables: HashMap<&String, NonVoidType> = HashMap::new(); // 'this' must also be set
            for param in params {
                local_variables.insert(&param.name, param.type_.to_owned());
            }
            helper(
                body,
                &old_members,
                &name,
                &mut local_variables,
                extends.as_ref(),
            );
        }

        *class = Rc::new(Declaration::Class {
            name,
            members,
            extends,
            implements,
        });
    }
    compilation_unit
}

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
                Invocation::InvokeSuperConstructor {
                    resolved,
                    ..
                } => constructor_super_call_helper(class_name, resolved, extends),
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

    #[inline(always)]
    fn method_call_helper(
        resolved: &mut Option<Box<(Declaration, DeclarationMember)>>,
        declarations: &Vec<Rc<Declaration>>,
        lhs: &String,
        rhs: &String,
    ) {
        for class in declarations {
            let Declaration::Class {
                name: class_name,
                members,
                ..
            } = class.as_ref();
            for member in members {
                if let DeclarationMember::Method {
                    name: member_name, ..
                } = &member
                {
                    //dbg!("{:?}, {:?}, {:?}, {:?}", lhs, rhs, class_name, member_name);
                    if lhs == class_name && rhs == member_name {
                        *resolved = Some(Box::new((class.as_ref().clone(), member.clone())));
                        // very bad
                    }
                }
            }
        }
    }

    fn constructor_call_helper(
        resolved: &mut Option<Box<(Declaration, DeclarationMember)>>,
        declarations: &Vec<Rc<Declaration>>,
        called_constructor: &String,
    ) {
        for class in declarations {
            let Declaration::Class { members, .. } = class.as_ref();
            for member in members {
                if let DeclarationMember::Constructor {
                    name: constructor_name,
                    ..
                } = &member
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
        resolved: &mut Option<Box<(Declaration, DeclarationMember)>>,
        extends: Option<&Rc<Declaration>>,
    ) {
        let extends =
            extends.expect("super() found in constructor but class does not extend other class");
        // *resolved = Some(Box::new())

        let Declaration::Class { members, .. } = extends.as_ref();

        for member in members {
            if let DeclarationMember::Constructor {
                ..
            } = &member
            {
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
            });

            if let Some(class_it_extends) = class_it_extends {
                resolved.push(Rc::new(Declaration::Class {
                    name: name.clone(),
                    extends: Some(class_it_extends.clone()),
                    members: members.clone(),
                    implements: vec![],
                }));
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
