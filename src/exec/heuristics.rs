use std::{cell::RefCell, collections::HashMap, ops::DerefMut, rc::Rc};

use itertools::Itertools;
use slog::{o, Logger};

use crate::{
    cfg::CFGStatement,
    exec::{action, ActionResult},
    positioned::SourcePos,
    statistics::Statistics,
    symbol_table::SymbolTable,
    Options,
};

use execution_tree::ExecutionTree;

use super::{IdCounter, State, SymResult};

pub mod depth_first_search;
pub mod min_dist_to_uncovered;
pub mod path_merging;
pub mod random_path;
pub mod round_robin;

type Cost = u64;
pub type ProgramCounter = u64;

mod execution_tree;
mod utils;

/// Given a set of states, which are all assumed to be at the same program point,
/// execute one instruction and return the resulting set of states, possibly branched into different program points.
/// Often this will be just one state, but it may happen that states are split due to e.g. array initialisation or due to encountering a branch statement,
/// (if, while, function call with dynamic dispatch)
///
/// If instead an invalid assertion occured, return that assertion location.
fn execute_instruction_for_all_states(
    states: Vec<State>,
    program: &HashMap<u64, CFGStatement>,
    flows: &HashMap<u64, Vec<u64>>,
    st: &SymbolTable,
    root_logger: Logger,
    path_counter: Rc<RefCell<IdCounter<u64>>>,
    statistics: &mut Statistics,
    options: &Options,
) -> Result<HashMap<u64, Vec<State>>, SourcePos> {
    assert!(!states.is_empty());

    statistics.measure_statement_explored(states[0].pc);
    let mut remaining_states = states;

    let mut resulting_states: HashMap<u64, Vec<State>> = HashMap::new();

    // debug!(
    //     root_logger,
    //     "number of states: {:?}",
    //     &remaining_states.len()
    // );

    while let Some(mut state) = remaining_states.pop() {
        debug_assert!(remaining_states.iter().map(|s| s.pc).all_equal());

        // dbg!(&remaining_states.len());
        if state.path_length >= options.k
            || statistics.start_time.elapsed().as_secs() >= options.time_budget
        {
            // finishing current branch
            statistics.measure_finish();
            continue;
        }

        let next = action(
            &mut state,
            program,
            &mut crate::exec::EngineContext {
                remaining_states: &mut remaining_states,
                path_counter: path_counter.clone(),
                statistics,
                st,
                root_logger: &root_logger,
                options,
            },
        );
        match next {
            ActionResult::FunctionCall(next) => {
                // function call or return
                state.pc = next;
                resulting_states.entry(state.pc).or_default().push(state);
            }
            ActionResult::Return(return_pc) => {
                if let Some(neighbours) = flows.get(&return_pc) {
                    // A return statement always connects to one
                    debug_assert!(neighbours.len() == 1);
                    let mut neighbours = neighbours.iter();
                    let first_neighbour = neighbours.next().unwrap();
                    state.pc = *first_neighbour;

                    resulting_states.entry(state.pc).or_default().push(state);
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
                        new_state.logger = root_logger.new(o!("path_id" => path_id));

                        resulting_states
                            .entry(new_state.pc)
                            .or_default()
                            .push(new_state);
                    }
                    resulting_states.entry(state.pc).or_default().push(state);
                } else {
                    // Function exit of the main function under verification
                    if let CFGStatement::FunctionExit { .. } = &program[&state.pc] {
                        // Valid program exit, continue
                        statistics.measure_finish();
                    } else {
                        panic!("Unexpected end of CFG");
                    }
                }
            }
            ActionResult::InvalidAssertion(info) => {
                return Err(info);
            }
            ActionResult::InfeasiblePath => {
                statistics.measure_prune();
            }
            ActionResult::Finish => {
                statistics.measure_finish();
            }
        }
    }

    // if resulting_states.is_empty() {
    //     dbg!(&program[&current_pc.unwrap()]);
    // }

    // Finished
    Ok(resulting_states)
}

/// Marks a path as finished in the path tree. (only if there are no valid states left for that path)
/// It will move up tree through its parent, removing the finished state from the list of child states.
/// If there are no states left in the parent after this, this means that all paths under that branch have been explored,
/// meaning that we can remove that branch as well, repeating the process.
///
/// Returns whether the root node was reached, in that case the entire search space is explored (up to given limit k).
///
/// TODO:
/// Removing any branching node where there is only one unpruned/unfinished state left.
fn finish_state_in_path(mut leaf: Rc<RefCell<ExecutionTree>>) -> bool {
    loop {
        let parent = if let Some(parent) = leaf.borrow().parent().upgrade() {
            parent
        } else {
            return true;
        };

        match parent.borrow_mut().deref_mut() {
            ExecutionTree::Node { children, .. } => {
                children.retain(|child| !Rc::ptr_eq(child, &leaf));

                if children.is_empty() {
                    leaf = parent.clone();
                } else {
                    return false;
                }
            }
            ExecutionTree::Leaf { .. } => panic!("Expected a Node as parent"),
        };
    }
}
