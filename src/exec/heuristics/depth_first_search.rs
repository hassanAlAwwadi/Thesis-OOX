use std::{collections::HashMap, rc::Rc, cell::RefCell};

use slog::{Logger, debug};

use crate::{cfg::CFGStatement, symbol_table::SymbolTable, statistics::Statistics, stack::write_to_stack};

use super::{State, IdCounter, SymResult, ActionResult, exec_assume, DFSEngine, AliasEntry, action};


/// The main function for the symbolic execution, any path splitting due to the control flow graph or array initialization happens here.
/// Depth first search, without using any other heuristic.
pub(crate) fn sym_exec(
    state: State,
    program: &HashMap<u64, CFGStatement>,
    flows: &HashMap<u64, Vec<u64>>,
    k: u64,
    st: &SymbolTable,
    root_logger: Logger,
    path_counter: Rc<RefCell<IdCounter<u64>>>,
    statistics: &mut Statistics,
) -> SymResult {
    let mut remaining_states: Vec<State> = vec![];
    let mut state = state;

    loop {
        // dbg!(&remaining_states.len());
        if state.path_length >= k {
            // finishing current branch
            statistics.measure_finish();
            if let Some(next_state) = remaining_states.pop() {
                state = next_state;
            } else {
                // Finished
                return SymResult::Valid;
            }
        }

        let next = action(
            &mut state,
            program,
            k,
            &mut crate::exec::DFSEngine {
                remaining_states: &mut remaining_states,
                path_counter: path_counter.clone(),
                statistics,
                st,
            },
        );
        match next {
            ActionResult::FunctionCall(next) => {
                // function call or return
                state.pc = next;
            }
            ActionResult::Return(return_pc) => {
                if let Some(neighbours) = flows.get(&return_pc) {
                    let mut neighbours = neighbours.iter();
                    let first_neighbour = neighbours.next().unwrap();
                    state.pc = *first_neighbour;

                    for neighbour_pc in neighbours {
                        let mut new_state = state.clone();
                        new_state.pc = *neighbour_pc;

                        remaining_states.push(new_state);
                    }
                } else {
                    panic!("function pc does not exist");
                }
            }
            ActionResult::Continue => {
                if let Some(neighbours) = flows.get(&state.pc) {
                    //dbg!(&neighbours);
                    statistics.measure_branches((neighbours.len() - 1) as u32);

                    let mut neighbours = neighbours.iter();
                    let first_neighbour = neighbours.next().unwrap();
                    state.pc = *first_neighbour;
                    state.path_length += 1;

                    let new_path_ids = (1..).map(|_| path_counter.borrow_mut().next_id());

                    for (neighbour_pc, path_id) in neighbours.zip(new_path_ids) {
                        let mut new_state = state.clone();
                        new_state.path_id = path_id;
                        new_state.pc = *neighbour_pc;

                        remaining_states.push(new_state);
                    }
                } else {
                    // Function exit of the main function under verification
                    if let CFGStatement::FunctionExit { decl_name, .. } = &program[&state.pc] {
                        // Valid program exit, continue
                        statistics.measure_finish();
                        if let Some(next_state) = remaining_states.pop() {
                            state = next_state;
                        } else {
                            // Finished
                            return SymResult::Valid;
                        }
                    } else {
                        // Unexpected end of CFG
                        panic!("Unexpected end of CFG");
                    }
                }
            }
            ActionResult::InvalidAssertion(info) => {
                return SymResult::Invalid(info);
            }
            ActionResult::InfeasiblePath => {
                // Finish this branch
                statistics.measure_prune();
                if let Some(next_state) = remaining_states.pop() {
                    state = next_state;
                } else {
                    // Finished
                    return SymResult::Valid;
                }
            }
            ActionResult::Finish => {
                statistics.measure_finish();
                if let Some(next_state) = remaining_states.pop() {
                    state = next_state;
                } else {
                    // Finished
                    return SymResult::Valid;
                }
            }

            ActionResult::StateSplit((guard, true_lhs, false_lhs, lhs_name)) => {
                // split up the paths into two, one where guard == true and one where guard == false.
                // Do not increase path_length
                statistics.measure_branches(2);
                let mut true_state = state.clone();
                true_state.path_id = path_counter.borrow_mut().next_id();
                let feasible_path = exec_assume(
                    &mut true_state,
                    guard.clone(),
                    &mut DFSEngine {
                        remaining_states: &mut remaining_states,
                        path_counter: path_counter.clone(),
                        statistics,
                        st,
                    },
                );
                if feasible_path {
                    write_to_stack(lhs_name.clone(), true_lhs, &mut true_state.stack);
                    remaining_states.push(true_state);
                }
                // continue with false state
                let mut false_state = &mut state;
                let feasible_path = exec_assume(
                    &mut false_state,
                    guard,
                    &mut DFSEngine {
                        remaining_states: &mut remaining_states,
                        path_counter: path_counter.clone(),
                        statistics,
                        st,
                    },
                );
                if feasible_path {
                    write_to_stack(lhs_name, false_lhs, &mut false_state.stack);
                }
            }
            ActionResult::StateSplitObjectTypes {
                symbolic_object_ref,
                resulting_alias,
            } => {
                let alias = &state.alias_map[&symbolic_object_ref];

                assert!(resulting_alias.len() > 1);

                statistics.measure_branches(resulting_alias.len() as u32);

                debug!(state.logger, "Splitting up current path into {:?} paths due to polymorphic method invocation", resulting_alias.len();
                    "object" => #?symbolic_object_ref,
                    "resulting_split" => #?resulting_alias
                );

                let mut resulting_aliases = resulting_alias.into_iter();

                // first set the current state
                let (_, objects) = resulting_aliases.next().unwrap();
                state
                    .alias_map
                    .insert(symbolic_object_ref.clone(), AliasEntry::new(objects));

                // set remaining states
                let new_path_ids = (1..).map(|_| path_counter.borrow_mut().next_id());
                let new_states =
                    resulting_aliases
                        .zip(new_path_ids)
                        .map(|((_, objects), path_id)| {
                            let mut state = state.clone();
                            state
                                .alias_map
                                .insert(symbolic_object_ref.clone(), AliasEntry::new(objects));
                            state.path_id = path_id;
                            state
                        });

                remaining_states.extend(new_states);
            }
        }
    }
}