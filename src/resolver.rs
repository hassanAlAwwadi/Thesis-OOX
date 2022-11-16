

// since the class and method declaration must be inserted into the abstract syntax tree, this mess is needed.

use crate::syntax::{CompilationUnit, Declaration, Invocation, Statement, DeclarationMember, Rhs};

pub fn set_resolvers(compilation_unit: &mut CompilationUnit) {
    let declarations: Vec<Declaration> = compilation_unit.members.clone();

    let members = compilation_unit.members.iter_mut().filter_map(|m| match m {
        Declaration::Class { members, .. } => Some(members),
    });

    for class in members {
        let method_bodies = class.iter_mut().filter_map(|dcl| match dcl {
            DeclarationMember::Method { body, .. } => Some(body),
            _ => None,
        });
        for body in method_bodies {
            helper(body, &declarations);
        }
    }
}

fn helper(statement: &mut Statement, declarations: &Vec<Declaration>) {
    
    match statement {
        Statement::Call { invocation: Invocation::InvokeMethod { lhs, rhs, resolved, .. } } => {
            helper1(resolved,  declarations, &lhs, &rhs);
        },
        Statement::Assign { lhs: _, rhs: Rhs::RhsCall { invocation: Invocation::InvokeMethod { lhs, rhs, arguments, resolved }, .. } } => {
            helper1(resolved,  declarations, &lhs, &rhs);
        }
        Statement::Ite { guard, true_body, false_body } => {
            helper(true_body, declarations);
            helper(false_body, declarations);
        },
        Statement::Seq { stat1, stat2 } => {
            helper(stat1, declarations);
            helper(stat2, declarations);
        },
        Statement::While { guard, body } => todo!(),
        Statement::Throw { message } => todo!(),
        Statement::Try { try_body, catch_body } => todo!(),
        Statement::Block { body } => todo!(),
        _ => ()
    }

    #[inline(always)]
    fn helper1(resolved: &mut Option<Box<(Declaration, DeclarationMember)>>, declarations: &Vec<Declaration>, lhs: &String, rhs: &String) {
        for class@Declaration::Class { name: class_name, members} in declarations {
            for member in members {
                match &member {
                    DeclarationMember::Method {  name: member_name, .. } => {
                        dbg!("{:?}, {:?}, {:?}, {:?}", lhs, rhs, class_name, member_name);
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