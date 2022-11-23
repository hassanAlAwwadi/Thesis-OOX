

// since the class and method declaration must be inserted into the abstract syntax tree, this mess is needed.

use std::collections::HashMap;

use crate::syntax::{CompilationUnit, Declaration, Invocation, Statement, DeclarationMember, Rhs, RuntimeType, NonVoidType, Parameter};

pub fn set_resolvers(compilation_unit: &mut CompilationUnit) {
    let declarations: Vec<Declaration> = compilation_unit.members.clone();

    let members = compilation_unit.members.iter_mut().filter_map(|m| match m {
        Declaration::Class { members, name } => Some((name, members)),
    });

    for (name, class) in members {
        let method_bodies = class.iter_mut().filter_map(|dcl| match dcl {
            DeclarationMember::Method { body, params, ..} => Some((body, params)),
            _ => None,
        });
        for (body, params) in method_bodies {
            helper(body, &declarations, name, params);
        }
    }
}

fn helper(statement: &mut Statement, declarations: &Vec<Declaration>, class_name: &String, params: &Vec<Parameter>) {
    let mut local_variables: HashMap<&String, NonVoidType> = HashMap::new(); // 'this' must also be set
    for param in params {
        local_variables.insert(&param.name, param.type_.to_owned());
    }
    match statement {
        Statement::Call { invocation: Invocation::InvokeMethod { lhs, rhs, resolved, .. } } => {
            if let Some(NonVoidType::ReferenceType { identifier }) = &local_variables.get(lhs) {
                // This is a normal method call
                helper1(resolved,  declarations, identifier, &rhs);

            } else {
                // This is a static method call on a class
                helper1(resolved,  declarations, &lhs, &rhs);
            }
        },
        Statement::Assign { lhs: _, rhs: Rhs::RhsCall { invocation: Invocation::InvokeMethod { lhs, rhs, arguments, resolved }, .. } } => {
            if let Some(NonVoidType::ReferenceType { identifier }) = &local_variables.get(lhs) {
                // This is a normal method call
                helper1(resolved,  declarations, identifier, &rhs);

            } else {
                // This is a static method call on a class
                helper1(resolved,  declarations, &lhs, &rhs);
            }
        }
        Statement::Ite { guard, true_body, false_body } => {
            helper(true_body, declarations, class_name, params);
            helper(false_body, declarations, class_name, params);
        },
        Statement::Seq { stat1, stat2 } => {
            helper(stat1, declarations, class_name, params);
            helper(stat2, declarations, class_name, params);
        },
        Statement::While { guard, body } => {
            helper(body, declarations, class_name, params);
        },
        Statement::Throw { message } => todo!(),
        Statement::Try { try_body, catch_body } => todo!(),
        Statement::Block { body } => todo!(),
        Statement::Declare { type_, var } => {local_variables.insert(var, type_.clone());}
        _ => ()
    }

    #[inline(always)]
    fn helper1(resolved: &mut Option<Box<(Declaration, DeclarationMember)>>, declarations: &Vec<Declaration>, lhs: &String, rhs: &String) {
        for class@Declaration::Class { name: class_name, members} in declarations {
            for member in members {
                match &member {
                    DeclarationMember::Method {  name: member_name, .. } => {
                        //dbg!("{:?}, {:?}, {:?}, {:?}", lhs, rhs, class_name, member_name);
                        if lhs == class_name && rhs == member_name {
                            *resolved = Some(Box::new((class.clone(), member.clone()))); // very bad
                        }
                    }
                    DeclarationMember::Constructor { name, params, specification, body } => todo!(),
                    _ => ()
                }
            }
        }
    }
}