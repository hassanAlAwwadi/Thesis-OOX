use std::{collections::HashMap, rc::Rc};

use itertools::Itertools;
use slog::debug;

use crate::{
    cfg::CFGStatement,
    eval::evaluate,
    exec::State,
    symbol_table::SymbolTable,
    syntax::{Declaration, DeclarationMember, Invocation, Lhs, RuntimeType, Parameter, Expression, Identifier, Method}, stack::lookup_in_stack, typeable::Typeable, utils,
};

use super::{exec_method, exec_static_method, find_entry_for_static_invocation, ActionResult, remove_symbolic_null};

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
    st: &SymbolTable,
) -> u64 {
    let (
        declaration,
        resolved_method,
    ) = resolved;
    let class_name = &declaration.name();
    
    if resolved_method.is_static {
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
            &resolved_method.params,
            st,
        );
        let next_entry =
            find_entry_for_static_invocation(class_name, invocation.identifier(), program);

        return next_entry;
    } else {
        non_static_resolved_method_invocation(state, invocation, class_name, resolved_method.clone(), return_point, lhs, program, st)
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
    potential_methods: &HashMap<Identifier, (Declaration, Rc<Method>)>,
    return_point: u64,
    lhs: Option<Lhs>,
    program: &HashMap<u64, CFGStatement>,
    st: &SymbolTable,
) -> ActionResult {
    let object = lookup_in_stack(invocation_lhs, &state.stack).unwrap();
    // object can be either a concrete reference to a heap object, or a symbolic object
    // the latter means that we have to split states here, one path for every alias object types,
    // if there is only one possible then we can also continue with that path
    match object.as_ref() {
        Expression::Ref { ref_, type_, .. } => {
            let this = (type_.clone(), invocation_lhs.to_owned());

            let reference_type_name = type_.as_reference_type().expect("expected reference type");

            let method = potential_methods.get(reference_type_name)
                .unwrap();

            let (
                declaration,
                member,
            ) = method;

            let decl_name = declaration.name();

            let next_entry = non_static_resolved_method_invocation(
                state,
                invocation,
                decl_name,
                member.clone(),
                return_point,
                lhs,
                program,
                st,
            );
            return ActionResult::FunctionCall(next_entry);
            
        }
        Expression::SymbolicRef { var, type_, ..  } => {
            remove_symbolic_null(&mut state.alias_map, invocation_lhs);
            let alias_entry = &state.alias_map[var];

            // if symbolicref contains only objects of one type
            // we can resolve which method to call

            if let Some(RuntimeType::ReferenceRuntimeType { type_ }) = alias_entry.uniform_type() {
                // we can resolve this
                let (
                    declaration,
                    member,
                ) = potential_methods.get(&type_).unwrap();

                let decl_name = declaration.name();

                let next_entry = non_static_resolved_method_invocation(
                    state,
                    invocation,
                    decl_name,
                    member.clone(),
                    return_point,
                    lhs,
                    program,
                    st,
                );
                return ActionResult::FunctionCall(next_entry);
            } else {
                // we need to split states such that each resulting path has a single type for the object in the alias map.
                // dbg!(&alias_entry.aliases.iter().map(|a| (a.clone(), Typeable::type_of(a.as_ref()))).collect_vec());
                // dbg!(potential_methods.keys());
                let resulting_alias = utils::group_by(alias_entry.aliases.iter().map(|alias| (potential_methods.get(alias.type_of().as_reference_type().expect("expected reference type")).map(|(d, dm)| {
                    (d.name().clone(), dm.name.clone())
                }).expect("Could not find method for the type"), alias.clone())));

                if resulting_alias.len() == 1 {
                    // not a uniform type, but classes resolve to the same method, we can continue with this path.
                    let ((decl_name, _method_name), _objects) = resulting_alias.iter().next().unwrap();
                    debug!(state.logger, "Symbolic object contains types that resolve to the same method {:?}::{:?}", decl_name, _method_name);

                    let (
                        declaration,
                        member,
                    ) = potential_methods.get(decl_name).unwrap();

                    let decl_name = declaration.name();
        
                    let next_entry = non_static_resolved_method_invocation(
                        state,
                        invocation,
                        decl_name,
                        member.clone(),
                        return_point,
                        lhs,
                        program,
                        st,
                    );
                    return ActionResult::FunctionCall(next_entry);
                }
                dbg!(resulting_alias.keys());

                return ActionResult::StateSplitObjectTypes { symbolic_object_ref: var.clone(), resulting_alias }
            }

            // otherwise we need to split states for each type.


            todo!()
        }
        _ => unreachable!(),
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


/// Sane things below


pub(super) fn non_static_resolved_method_invocation(
    state: &mut State,
    invocation: &Invocation,
    class_name: &Identifier,
    resolved_method: Rc<Method>,
    return_point: u64,
    lhs: Option<Lhs>,
    program: &HashMap<u64, CFGStatement>,
    st: &SymbolTable,
) -> u64 {
    debug!(state.logger, "non-static method invocation");

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
        st,
        this,
    );
    let next_entry = find_entry_for_static_invocation(class_name, invocation.identifier(), program);

    return next_entry;
}