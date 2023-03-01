use std::{collections::HashMap, rc::Rc};

use itertools::Itertools;
use slog::debug;

use crate::{
    cfg::CFGStatement,
    eval::evaluate,
    exec::State,
    stack::lookup_in_stack,
    symbol_table::SymbolTable,
    syntax::{Declaration, Expression, Identifier, Invocation, Lhs, Method, RuntimeType},
    typeable::Typeable,
    utils,
};

use super::{
    exec_method, exec_static_method, find_entry_for_static_invocation, remove_symbolic_null,
    ActionResult, Engine,
};

/// A static method, or a method that is not overriden anywhere (non-polymorphic)
/// This means that there is only one method that can be called
/// Returns the next function entry CFG
pub(super) fn single_method_invocation(
    state: &mut State,
    invocation: &Invocation,
    resolved: &(Declaration, Rc<Method>),
    return_point: u64,
    lhs: Option<Lhs>,
    program: &HashMap<u64, CFGStatement>,
    en: &Engine,
) -> u64 {
    let (declaration, resolved_method) = resolved;
    let class_name = &declaration.name();

    if resolved_method.is_static {
        // evaluate arguments
        let arguments = invocation
            .arguments()
            .into_iter()
            .map(|arg| evaluate(state, arg.clone(), en))
            .collect::<Vec<_>>();

        exec_static_method(
            state,
            return_point,
            resolved_method.clone(),
            lhs,
            &arguments,
            &resolved_method.params,
            en,
        );
        let argument_types = invocation
            .arguments()
            .iter()
            .map(AsRef::as_ref)
            .map(Typeable::type_of);
        let next_entry = find_entry_for_static_invocation(
            class_name,
            invocation.identifier(),
            argument_types,
            program,
            en.st,
        );

        return next_entry;
    } else {
        non_static_resolved_method_invocation(
            state,
            invocation,
            class_name,
            resolved_method.clone(),
            return_point,
            lhs,
            program,
            en,
        )
    }
}

/// Non-static case, multiple candidate methods that could be called
///
/// For example a method from a superclass or an overriden method from a subclass could be called,
/// depending on the type of the object.
pub(super) fn multiple_method_invocation(
    state: &mut State,
    invocation_lhs: &Identifier,
    invocation: &Invocation,
    // For each type, the method implementation it resolves to.
    potential_methods: &HashMap<Identifier, (Declaration, Rc<Method>)>,
    return_point: u64,
    lhs: Option<Lhs>,
    program: &HashMap<u64, CFGStatement>,
    en: &Engine,
) -> ActionResult {
    let object = lookup_in_stack(invocation_lhs, &state.stack).unwrap();
    // object can be either a concrete reference to a heap object, or a symbolic object
    // the latter means that we have to split states here, one path for each distinct method that is resolved to,
    // if all aliases resolve to the same method, then we can also continue with that path
    match object.as_ref() {
        Expression::Ref { type_, .. } => {
            let reference_type_name = type_.as_reference_type().expect("expected reference type");

            let method = potential_methods.get(reference_type_name).unwrap();

            let (declaration, member) = method;

            let decl_name = declaration.name();

            let next_entry = non_static_resolved_method_invocation(
                state,
                invocation,
                decl_name,
                member.clone(),
                return_point,
                lhs,
                program,
                en,
            );
            return ActionResult::FunctionCall(next_entry);
        }
        Expression::SymbolicRef { var, .. } => {
            remove_symbolic_null(&mut state.alias_map, invocation_lhs);
            let alias_entry = &state.alias_map[var];

            // if symbolicref contains only objects of one type
            // we can resolve which method to call

            if let Some(RuntimeType::ReferenceRuntimeType { type_ }) = alias_entry.uniform_type() {
                // All aliases have the same type, so they all resolve to the same method.
                let (declaration, member) = potential_methods.get(&type_).unwrap();

                let decl_name = declaration.name();

                let next_entry = non_static_resolved_method_invocation(
                    state,
                    invocation,
                    decl_name,
                    member.clone(),
                    return_point,
                    lhs,
                    program,
                    en,
                );
                return ActionResult::FunctionCall(next_entry);
            } else {
                // Not all aliases have the same type, so it can happen that different types resolve to different methods.
                // First we check to which methods they resolve:

                // A mapping from a (class_name, method_name) -> array of aliases that resolve to this method.
                let resulting_alias = utils::group_by(alias_entry.aliases.iter().map(|alias| {
                    let (decl, method) = (potential_methods.get(
                        alias
                            .type_of()
                            .as_reference_type()
                            .expect("expected reference type"),
                    ))
                    .expect("Could not find method for the type");
                    ((decl.name().clone(), method.name.clone()), alias.clone())
                }));

                if resulting_alias.len() == 1 {
                    // not a uniform type, but all aliases resolve to the same method, we can continue with this path.
                    let ((decl_name, method_name), _objects) =
                        resulting_alias.iter().next().unwrap();
                    debug!(
                        state.logger,
                        "Symbolic object contains types that resolve to the same method {:?}::{:?}",
                        decl_name,
                        method_name
                    );

                    // All methods are be the same for each candidate class, so take the first.
                    let (_decl, method) = potential_methods.values().next().unwrap();

                    let next_entry = non_static_resolved_method_invocation(
                        state,
                        invocation,
                        decl_name,
                        method.clone(),
                        return_point,
                        lhs,
                        program,
                        en,
                    );
                    return ActionResult::FunctionCall(next_entry);
                }
                //dbg!(resulting_alias.keys());

                // We need to split states such that each resulting path has a single type for the object in the alias map.
                return ActionResult::StateSplitObjectTypes {
                    symbolic_object_ref: var.clone(),
                    resulting_alias,
                };
            }
        }
        _ => unreachable!("Expected Ref or SymbolicRef, found {:?}", object),
    };
}

/// Checks the aliases whether their type is unique, if so return that type
/// otherwise return None
fn find_unique_type(aliases: &Vec<Rc<Expression>>) -> Option<RuntimeType> {
    assert!(aliases.len() > 0);

    let all_have_same_type = aliases
        .iter()
        .map(AsRef::as_ref)
        .map(Typeable::type_of)
        .all_equal();

    if all_have_same_type {
        Some(aliases[0].type_of())
    } else {
        None
    }
}

/// Helper method for a non-static method invocation with an already resolved method.
fn non_static_resolved_method_invocation(
    state: &mut State,
    invocation: &Invocation,
    class_name: &Identifier,
    resolved_method: Rc<Method>,
    return_point: u64,
    lhs: Option<Lhs>,
    program: &HashMap<u64, CFGStatement>,
    en: &Engine,
) -> u64 {
    debug!(state.logger, "non-static method invocation");

    // evaluate arguments
    let arguments = invocation
        .arguments()
        .into_iter()
        .map(|arg| evaluate(state, arg.clone(), en))
        .collect::<Vec<_>>();

    let invocation_lhs = match invocation {
        Invocation::InvokeMethod { lhs, .. } => lhs,
        Invocation::InvokeSuperMethod { .. } => "this", // we pass "this" object to superclass methods aswell.
        _ => panic!("expected invoke method or invokeSuperMethod"),
    };

    // This is going to give problems, fix by looking up the type in stack?
    let this = (
        RuntimeType::ReferenceRuntimeType {
            type_: class_name.clone(),
        },
        invocation_lhs.to_owned().into(),
    );

    exec_method(
        state,
        return_point,
        resolved_method,
        lhs,
        &arguments,
        en,
        this,
    );
    let argument_types = invocation
        .arguments()
        .iter()
        .map(AsRef::as_ref)
        .map(Typeable::type_of);
    let next_entry = find_entry_for_static_invocation(
        class_name,
        invocation.identifier(),
        argument_types,
        program,
        en.st,
    );

    return next_entry;
}
