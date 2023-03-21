use std::{rc::Rc, collections::HashMap};

use slog::debug;

use crate::{syntax::{Expression, Identifier}, exec::AliasEntry};

use super::{State, Engine, exec_assume, write_to_stack};



/// This occurs when a lhs in a statement is a conditional
/// and requires the state to split into paths where the condition is true and false.
/// A lhs becomes a conditional for example when `Point p := a[i];` where `i` is a symbolic variable.
/// When later on p is referenced, e.g. `p.x` is called, it must be determined which element of a is referred to.
pub fn conditional_state_split(state: &mut State, en: &mut impl Engine, guard: Rc<Expression>, true_lhs: Rc<Expression>, false_lhs: Rc<Expression>, lhs_name: Identifier) {
    // split up the paths into two, one where guard == true and one where guard == false.
    // Do not increase path_length
    en.statistics().measure_branches(2);
    let mut true_state = state.clone();
    true_state.path_id = en.next_path_id();
    let feasible_path = exec_assume(
        &mut true_state,
        guard.clone(),
        en,
    );
    if feasible_path {
        write_to_stack(lhs_name.clone(), true_lhs, &mut true_state.stack);
        en.add_remaining_state(true_state);
    }
    // continue with false state
    let mut false_state = state;
    let feasible_path = exec_assume(
        &mut false_state,
        guard,
        en,
    );
    if feasible_path {
        write_to_stack(lhs_name, false_lhs, &mut false_state.stack);
    }
}


/// For each of the new aliases, create a new state and replace the symbolic object with those aliases.
/// The current state is mutated instead of added to the backlog.
pub(super) fn split_states_with_aliases(
    en: &mut impl Engine,
    state: &mut State,
    symbolic_object_ref: Identifier,
    aliases: HashMap<(Identifier, Identifier), Vec<Rc<Expression>>>,
) {
    assert!(aliases.len() > 1);
    en.statistics().measure_branches(aliases.len() as u32);

    debug!(state.logger, "Splitting up current path into {:?} paths due to polymorphic method invocation", aliases.len();
        "object" => #?symbolic_object_ref,
        "resulting_split" => #?aliases
    );

    // Turn it into an iterator over the objects
    let mut aliases = aliases.into_iter().map(|(_, objects)| objects);

    let objects = aliases.next().unwrap();
    state
        .alias_map
        .insert(symbolic_object_ref.clone(), AliasEntry::new(objects));

    for alias in aliases {
        let mut state = state.clone();
        state
            .alias_map
            .insert(symbolic_object_ref.clone(), AliasEntry::new(alias));
        state.path_id = en.next_path_id();
        en.add_remaining_state(state);
    }
}