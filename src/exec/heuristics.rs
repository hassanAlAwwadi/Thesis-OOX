use std::{collections::HashMap, cell::RefCell, rc::{Rc, Weak}, ops::DerefMut};

use slog::{Logger, debug};

use crate::{cfg::CFGStatement, symbol_table::SymbolTable, statistics::Statistics, exec::{action, ActionResult}};

use super::{State, SymResult, IdCounter};

pub mod depth_first_search;
pub mod random_path;
pub mod min_dist_to_uncovered;


type Cost = u64;
type ProgramCounter = u64;


// sane alternative?
#[derive(Debug)]
enum N {
    Node {
        parent: Weak<RefCell<N>>,
        statement: u64,
        children: Vec<Rc<RefCell<N>>>,
    },
    Leaf {
        parent: Weak<RefCell<N>>,
        statement: u64,
        states: Vec<State>,
    },
}


impl N {
    fn parent(&self) -> Weak<RefCell<N>> {
        match self {
            N::Node { parent, .. } => parent.clone(),
            N::Leaf { parent, .. } => parent.clone(),
        }
    }

    fn statement(&self) -> u64 {
        match self {
            N::Node { statement, .. } => *statement,
            N::Leaf { statement, .. } => *statement,
        }
    }
    /// Assume it is a leaf and take out the states.
    fn into_states(&mut self) -> Option<Vec<State>> {
        if let N::Leaf { states, .. } = self {
            // Take the state, leaving an empty array
            let states = std::mem::take(states);
            Some(states)
        } else {
            None
        }
    }

    fn set_states(&mut self, mut new_states: Vec<State>) {
        if let N::Leaf { states, statement, .. } = self {
            // Set the states
            *statement = new_states[0].pc;
            *states = new_states;
        } else {
            panic!()
        }
    }

    fn set_parent(&mut self, new_parent: Weak<RefCell<N>>) {
        match self {
            N::Node {
                parent,
                statement,
                children,
            } => *parent = new_parent,
            N::Leaf { parent, .. } => *parent = new_parent,
        }
    }
}


enum R {
    /// The new states at one increased path counter, this occurs when there is no branch statement.
    /// Often this will be just one state, but it may happen that states are split due to e.g. array initialisation.
    Step(Vec<State>),
    /// A branch statement (if, while, foo.bar() dynamic dispatch to different functions)
    StateSplit(HashMap<u64, Vec<State>>),
    /// The path is finished, pruned or an invalid assert occured.
    Exit(SymResult),
}

fn execute_instruction_for_all_statements(
    states: Vec<State>,
    program: &HashMap<u64, CFGStatement>,
    flows: &HashMap<u64, Vec<u64>>,
    k: u64,
    st: &SymbolTable,
    root_logger: Logger,
    path_counter: Rc<RefCell<IdCounter<u64>>>,
    statistics: &mut Statistics,
) -> R {
    let mut remaining_states = states;

    let mut resulting_states: HashMap<u64, Vec<State>> = HashMap::new();

    let mut current_pc = None;
    debug!(
        root_logger,
        "number of states: {:?}",
        &remaining_states.len()
    );
    assert!(remaining_states.len() > 0);
    let mut finished = false;

    while let Some(mut state) = remaining_states.pop() {
        if let Some(current_pc) = current_pc {
            assert_eq!(state.pc, current_pc);
        } else {
            current_pc = Some(state.pc);
        }
        // dbg!(&remaining_states.len());
        if state.path_length >= k {
            // finishing current branch
            statistics.measure_finish();
            continue;
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

                        resulting_states
                            .entry(new_state.pc)
                            .or_default()
                            .push(new_state);
                    }
                    resulting_states.entry(state.pc).or_default().push(state);
                } else {
                    // Function exit of the main function under verification
                    if let CFGStatement::FunctionExit { decl_name, .. } = &program[&state.pc] {
                        // Valid program exit, continue
                        statistics.measure_finish();
                        finished = true;
                    } else {
                        // Unexpected end of CFG
                        panic!("Unexpected end of CFG");
                    }
                }
            }
            ActionResult::InvalidAssertion(info) => {
                return R::Exit(SymResult::Invalid(info));
            }
            ActionResult::InfeasiblePath => {
                statistics.measure_prune();
            }
            ActionResult::Finish => {
                statistics.measure_finish();
            }
        }
    }

    // if resulting_states.len() == 0 {
    //     dbg!(&program[&current_pc.unwrap()]);
    // }

    // Finished
    return R::StateSplit(resulting_states);
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
fn finish_state_in_path(mut leaf: Rc<RefCell<N>>, path: Vec<ProgramCounter>,) -> bool {
    loop {
        dbg!(&path);
        let parent = if let Some(parent) = leaf.borrow().parent().upgrade() {
            parent
        } else {
            // We have reached the root node that has no parent, set it to be an empty leaf and exit.
            // let mut leaf = leaf.borrow_mut();
            // let statement = leaf.statement();
            // *leaf = N::Leaf {
            //     parent: Weak::new(),
            //     statement: 0,
            //     states: vec![],
            // };
            return true;
        };
        
        match parent.borrow_mut().deref_mut() {
            N::Node { children, .. } => {
                
                children.retain(|child| !Rc::ptr_eq(child, &leaf));
                
                if children.len() == 0 {
                    leaf = parent.clone();
                } else {
                    return false;
                }
            }
            N::Leaf { .. } => panic!("Expected a Node as parent"),
        };
    }
}
