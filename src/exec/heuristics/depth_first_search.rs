use std::{cell::RefCell, collections::HashMap, rc::Rc};

use slog::{Logger};

use crate::{
    cfg::CFGStatement,
    statistics::Statistics,
    symbol_table::SymbolTable,
};

use super::{
    action, ActionResult, IdCounter, State, SymResult,
};

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
    _entry_method: crate::cfg::MethodIdentifier,
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
                    debug_assert!(neighbours.len() == 1);
                    let mut neighbours = neighbours.iter();
                    let first_neighbour = neighbours.next().unwrap();
                    state.pc = *first_neighbour;
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
        }
    }
}

