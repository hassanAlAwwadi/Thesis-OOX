use std::{
    cell::{RefCell},
    collections::HashMap,
    rc::Rc,
};

use rand::Rng;
use slog::{Logger};

use crate::{
    cfg::CFGStatement, exec::Engine, statistics::Statistics,
    symbol_table::SymbolTable,
};

use super::{
    action, ActionResult, IdCounter, State, SymResult,
};

enum BTree {
    Node {
        statement: u64,
        false_: Box<BTree>,
        true_: Box<BTree>,
    },
    Leaf(Vec<State>), // All program counters should be equal in these states
}

impl BTree {
    fn get_states(&mut self) -> Option<Vec<State>> {
        if let BTree::Leaf(states) = self {
            // Take the state, leaving an empty array
            let states = std::mem::take(states);
            Some(states)
        } else {
            None
        }
    }
}

fn random_path<'a>(mut tree: &'a mut BTree, rng: &'a mut impl Rng) -> &'a mut BTree {
    loop {
        match tree {
            BTree::Node { false_, true_, .. } => {
                if rng.gen() {
                    tree = true_;
                } else {
                    tree = false_;
                }
            }
            BTree::Leaf(_) => return tree,
        }
    }
}

pub struct RandomPathEngine<'a> {
    remaining_states: &'a mut Vec<State>,
    path_counter: Rc<RefCell<IdCounter<u64>>>,
    statistics: &'a mut Statistics,
    st: &'a SymbolTable,
}

impl Engine for RandomPathEngine<'_> {
    fn add_remaining_state(&mut self, state: State) {
        self.remaining_states.push(state);
    }   
    
    fn add_remaining_states(&mut self, states: impl Iterator<Item=State>) {
        self.remaining_states.extend(states);
    }

    fn next_path_id(&mut self) -> u64 {
        self.path_counter.borrow_mut().next_id()
    }

    fn statistics(&mut self) -> &mut Statistics {
        self.statistics
    }

    fn symbol_table(&self) -> &SymbolTable {
        self.st
    }
}

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
    let mut rng = rand::thread_rng();

    let mut paths = BTree::Leaf(Vec::new());

    // pointer to the leaf with states chosen by the heuristic
    let chosen_state = random_path(&mut paths, &mut rng);

    let mut states = chosen_state.get_states().unwrap();

    // wait a minute... how can we execute one statement in this model? we execute until we find another branch right? i think yes..
    // lets double check with latest paper of klee
    *chosen_state = BTree::Leaf(states);

    // for state in states {

    // }

    todo!()
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

fn execute_instruction(
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

    let mut resulting_states = HashMap::new();

    loop {
        let mut state = remaining_states.pop().unwrap();

        // dbg!(&remaining_states.len());
        if state.path_length >= k {
            // finishing current branch
            statistics.measure_finish();
            if let Some(next_state) = remaining_states.pop() {
                state = next_state;
            } else {
                // Finished
                // return R::Exit(SymResult::Valid);
                return R::StateSplit(resulting_states);
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
                            .entry(state.pc)
                            .or_default()
                            .push(new_state);
                    }
                    resulting_states.entry(state.pc).or_default().push(state);
                } else {
                    // Function exit of the main function under verification
                    if let CFGStatement::FunctionExit { decl_name, .. } = &program[&state.pc] {
                        // Valid program exit, continue
                        statistics.measure_finish();
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
}
