use std::{collections::HashMap, rc::Rc};

use itertools::Itertools;

use crate::{
    cfg::CFGStatement,
    eval::evaluate,
    exec::State,
    symbolic_table::SymbolicTable,
    syntax::{Declaration, DeclarationMember, Invocation, Lhs, RuntimeType, Parameter, Expression}, stack::lookup_in_stack, typeable::Typeable,
};

use super::{exec_method, exec_static_method, find_entry_for_static_invocation, ActionResult};

/// A static method, or a method that is not overriden anywhere (non-polymorphic)
/// This means that there is only one method that can be called
/// Returns the next function entry CFG
pub(super) fn single_method_invocation(
    state: &mut State,
    invocation: &Invocation,
    resolved: &(Declaration, Rc<DeclarationMember>),
    return_point: u64,
    lhs: Option<Lhs>,
    program: &HashMap<u64, CFGStatement>,
    st: &SymbolicTable,
) -> u64 {
    let (
        Declaration::Class {
            name: class_name, ..
        },
        resolved_method,
    ) = resolved;
    if let DeclarationMember::Method {
        is_static,
        return_type,
        name,
        params,
        specification,
        body,
    } = resolved_method.as_ref()
    {
        if *is_static {
            // evaluate arguments
            let arguments = invocation
                .arguments()
                .into_iter()
                .map(|arg| evaluate(state, Rc::new(arg.clone()), st))
                .collect::<Vec<_>>();

            exec_static_method(
                state,
                return_point,
                resolved_method.clone(),
                lhs,
                &arguments,
                &params,
                st,
            );
            let next_entry =
                find_entry_for_static_invocation(class_name, invocation.identifier(), program);

            return next_entry;
        } else {
            non_static_resolved_method_invocation(state, invocation, class_name, resolved_method.clone(), params, return_point, lhs, program, st)
        }
    } else {
        panic!();
    }
}

/// Non-static case, multiple candidate methods that could be called
pub(super) fn multiple_method_invocation(
    state: &mut State,
    invocation_lhs: &String,
    invocation: &Invocation,
    potential_methods: &[(Declaration, Rc<DeclarationMember>)],
    return_point: u64,
    lhs: Option<Lhs>,
    program: &HashMap<u64, CFGStatement>,
    st: &SymbolicTable,
) -> ActionResult {
    let object = lookup_in_stack(invocation_lhs, &state.stack).unwrap();
    // object can be either a concrete reference to a heap object, or a symbolic object
    // the latter means that we have to split states here, one path for every alias object types,
    // if there is only one possible then we can also continue with that path
    match object.as_ref() {
        Expression::Ref { ref_, type_ } => {
            let this = (type_.clone(), invocation_lhs.to_owned());

            let method = potential_methods
                .iter()
                .find(|(d, dm)| {
                    let Declaration::Class { name, .. } = d;
                    if let RuntimeType::ReferenceRuntimeType { type_ } = type_ {
                        if type_ == name {
                            return true;
                        }
                    }
                    return false;
                })
                .unwrap();

            let (
                Declaration::Class {
                    name: class_name, ..
                },
                member,
            ) = method; // i don't get this

            if let DeclarationMember::Method { params, .. } = member.as_ref() {
                let next_entry = non_static_resolved_method_invocation(
                    state,
                    invocation,
                    class_name,
                    member.clone(),
                    params,
                    return_point,
                    lhs,
                    program,
                    st,
                );
                return ActionResult::FunctionCall(next_entry);
            } else {
                panic!()
            }
        }
        Expression::SymbolicRef { var, type_ } => {
            let aliases = &state.alias_map[var];

            let types = aliases
                .iter()
                .map(AsRef::as_ref)
                .map(Typeable::type_of)
                .unique()
                .collect_vec();
            // if symbolicref contains only objects of one type
            // we can resolve which method to call

            if types.len() == 1 {
                // we can resolve this
                let method = potential_methods.iter().find(|(d, dm)| {
                    let Declaration::Class { name, .. } = d;
                    if let RuntimeType::ReferenceRuntimeType { type_ } = &types[0] {
                        if type_ == name {
                            return true;
                        }
                    }
                    return false;
                }).unwrap();

                let (
                    Declaration::Class {
                        name: class_name, ..
                    },
                    member,
                ) = method; // i don't get this
    
                if let DeclarationMember::Method { params, .. } = member.as_ref() {
                    let next_entry = non_static_resolved_method_invocation(
                        state,
                        invocation,
                        class_name,
                        member.clone(),
                        params,
                        return_point,
                        lhs,
                        program,
                        st,
                    );
                    return ActionResult::FunctionCall(next_entry);
                } else {
                    panic!()
                }
            } else {
                // we need to split states
            }

            // otherwise we need to split states for each type.

            todo!()
        }
        _ => unreachable!(),
    };
}

/// Sane things below


pub(super) fn non_static_resolved_method_invocation(
    state: &mut State,
    invocation: &Invocation,
    class_name: &String,
    resolved_method: Rc<DeclarationMember>,
    params: &[Parameter],
    return_point: u64,
    lhs: Option<Lhs>,
    program: &HashMap<u64, CFGStatement>,
    st: &SymbolicTable,
) -> u64 {
    // evaluate arguments
    let arguments = invocation
        .arguments()
        .into_iter()
        .map(|arg| evaluate(state, Rc::new(arg.clone()), st))
        .collect::<Vec<_>>();

    let invocation_lhs = match invocation {
        Invocation::InvokeMethod { lhs, .. } => lhs, 
        Invocation::InvokeSuperMethod { .. } => "this", // we pass "this" object to superclass methods aswell.
        _ => panic!("expected invoke method or invokeSuperMethod")
    };

    let this = (
        RuntimeType::ReferenceRuntimeType {
            type_: class_name.clone(),
        },
        invocation_lhs.to_owned(),
    );

    exec_method(
        state,
        return_point,
        resolved_method,
        lhs,
        &arguments,
        &params,
        st,
        this,
    );
    let next_entry = find_entry_for_static_invocation(class_name, invocation.identifier(), program);

    return next_entry;
}