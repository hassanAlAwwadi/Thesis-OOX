use std::{
    cell::RefCell,
    collections::HashMap,
    ops::{Deref, DerefMut},
    rc::{Rc, Weak},
};

use itertools::Itertools;
use rand::Rng;
use slog::{debug, Logger};

use crate::{cfg::CFGStatement, exec::Engine, statistics::Statistics, symbol_table::SymbolTable};

use super::{action, ActionResult, IdCounter, State, SymResult};

// We also need to consider that there are a lot of branches that end quickly, like due to if (x == null) { throw exception; } guard insertions.
enum BTree {
    Node {
        statement: u64,
        false_: Option<Box<BTree>>, // A branch is optional since it is set to None when finished to cleanup memory.
        true_: Option<Box<BTree>>,
    },
    Leaf(Vec<State>), // All program counters should be equal in these states
}

impl BTree {
    fn statement(&self) -> u64 {
        match self {
            BTree::Node { statement, .. } => *statement,
            BTree::Leaf(states) => states[0].pc,
        }
    }

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
        if let N::Leaf { states, .. } = self {
            // Set the states
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

type ProgramCounter = u64;

enum TreeNode {
    Node(Vec<ProgramCounter>),
    Leaf(Vec<State>),
}

impl TreeNode {
    /// Assume it is a leaf and take out the states.
    fn into_states(&mut self) -> Option<Vec<State>> {
        if let TreeNode::Leaf(states) = self {
            // Take the state, leaving an empty array
            let states = std::mem::take(states);
            Some(states)
        } else {
            None
        }
    }
}

/// A program may encounter the same branch more than once, so we need to distinguish between them
/// We use this Identifier for this.
type BranchId = u64;

struct PathTree {
    /// A mapping from program counter (at branch statements such as if, while and dynamic dispatch) to either
    /// 1. another branch Node
    /// 2. a leaf containing the states currently unexplored for that program point. In that case there is only a single element in the list.
    ///
    nodes: HashMap<ProgramCounter, TreeNode>,
    branch_id_to_pc: HashMap<BranchId, ProgramCounter>,
    // states: HashMap<ProgramCounter, Vec<State>>,
    root: ProgramCounter,
}

fn random_path<'a>(
    mut tree: Rc<RefCell<N>>,
    rng: &'a mut impl Rng,
) -> Option<(Vec<u64>, Rc<RefCell<N>>)> {
    let mut path = Vec::new();
    loop {
        let node = tree.clone();
        match node.borrow().deref() {
            N::Node {
                statement,
                children,
                ..
            } => {
                path.push(*statement);

                let idx = rng.gen_range(0..children.len());
                tree = children[idx].clone();
            }
            N::Leaf { states, statement, .. } => {
                if states.len() == 0 {
                    return None;
                }
                path.push(*statement);
                return Some((path, tree));
            }
        };
    }
}

// fn random_path<'a>(mut tree: &'a mut PathTree, rng: &'a mut impl Rng) -> Vec<ProgramCounter> {
//     let mut path = Vec::new();
//     let mut pc = tree.root;
//     loop {
//         path.push(pc);
//         match &tree.nodes[&pc] {
//             TreeNode::Node(subnodes) => {
//                 let idx = rng.gen_range(0..subnodes.len());
//                 pc = subnodes[idx];
//             },
//             TreeNode::Leaf(states) =>  {
//                 path.push(states[0].pc);
//                 return path;
//             }
//         }
//     }
// }

// fn random_path<'a>(mut tree: &'a mut BTree, rng: &'a mut impl Rng) -> (Vec<u64>, &'a mut BTree) {
//     let mut path = Vec::new();
//     loop {
//         match tree {
//             BTree::Node { false_, true_, statement } => {
//                 path.push(*statement);
//                 match (false_, true_) {
//                     (Some(false_), Some(true_)) => if rng.gen() {
//                         tree = true_;
//                     } else {
//                         tree = false_;
//                     }
//                     (None, Some(true_)) => tree = true_,
//                     (Some(false_), None) => tree = false_,
//                     (None, None) => panic!()
//                 }

//             }
//             BTree::Leaf(_) => return (path, tree),
//         }
//     }
// }

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

    fn add_remaining_states(&mut self, states: impl Iterator<Item = State>) {
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

    // let mut paths = PathTree {root: state.pc, nodes: HashMap::from([(state.pc, TreeNode::Leaf(vec![state]))]) };
    let mut tree = Rc::new(RefCell::new(N::Leaf {
        parent: Weak::new(),
        statement: state.pc,
        states: vec![state],
    }));
    // why am i setting tree as it's own parent?
    // tree.borrow_mut().set_parent(Rc::<_>::downgrade(&tree));

    loop {
        // pointer to the leaf with states chosen by the heuristic

        let (path_pcs, states_node) = if let Some((path_pcs, states_node)) = random_path(tree.clone(), &mut rng) {
            (path_pcs, states_node) 
        } else {
            // We have explored all states.
            debug!(root_logger, "all states explored");
            return SymResult::Valid;
        };
        let current_pc = *path_pcs.last().unwrap();
        let chosen_state = states_node.borrow_mut().into_states().unwrap();

        let mut states = chosen_state;

        let r = execute_instruction(
            states,
            program,
            flows,
            k,
            st,
            root_logger.clone(),
            path_counter.clone(),
            statistics,
        );

        match r {
            R::Step(_) => todo!(),
            R::StateSplit(new_states) => {
                assert!(new_states.len() <= 2);
                for (pc, states) in &new_states {
                    debug!(
                        root_logger,
                        "all pcs should be equal {}, {:?}",
                        pc,
                        states.iter().map(|s| s.pc).collect_vec()
                    );
                    if (!states.iter().all(|s| s.pc == *pc)) {
                        loop {}
                    }
                    assert!(states.iter().all(|s| s.pc == *pc));
                }

                match new_states.len() {
                    0 => {
                        // Branch finished due to "throw"
                        dbg!(current_pc, &program[&current_pc]);
                        // if let Some(parent) = states_node.borrow().parent().upgrade() {
                        //     dbg!(parent.borrow().deref().statement());
                        // } else {
                        //     dbg!("no parent");
                        // }
                        if (finish_state_in_path(states_node.clone(), path_pcs)) {
                            *tree.borrow_mut() = N::Leaf {
                                parent: Weak::new(),
                                statement: 0,
                                states: vec![],
                            };
                        }
                        
                    }
                    1 => {
                        let (pc, states) = new_states.into_iter().next().unwrap();
                        debug!(root_logger, "new state {:?}", pc);

                        // let mut tree = Rc::new(RefCell::new(N::Leaf(Weak::new(), states)));
                        // tree.borrow_mut().set_parent(Rc::<_>::downgrade(&tree));
                        states_node.borrow_mut().set_states(states);

                        // *states_node.borrow_mut() = N::Leaf { parent: Weak::new(), states };
                    }
                    2 => {
                        // Branching, split up states
                        debug!(
                            root_logger,
                            "new states: {:?}",
                            new_states.iter().map(|(pc, _)| pc).collect_vec()
                        );

                        let ((true_pc, true_), (false_pc, false_)) =
                            new_states.into_iter().collect_tuple().unwrap();

                        assert!(true_.len() > 0 && false_.len() > 0);

                        let parent = states_node.borrow().parent();
                        *states_node.borrow_mut() = N::Node {
                            parent,
                            statement: current_pc,
                            children: vec![
                                Rc::new(RefCell::new(N::Leaf {
                                    parent: Rc::downgrade(&states_node),
                                    statement: true_pc,
                                    states: true_,
                                })),
                                Rc::new(RefCell::new(N::Leaf {
                                    parent: Rc::downgrade(&states_node),
                                    statement: false_pc,
                                    states: false_,
                                })),
                            ],
                        }

                        // paths.nodes.insert(k, v)
                        // paths.nodes[current_pc] = TreeNode::Node(())
                        // *chosen_state = BTree::Node {
                        //     statement: current_pc,
                        //     false_: Some(Box::new(BTree::Leaf(false_))),
                        //     true_: Some(Box::new(BTree::Leaf(true_))),
                        // }
                    }
                    x => panic!("got {:?}", x),
                }
            }
            // Think i need to check here if it is valid or not, if valid we should not return but just prune/finish that path in the tree of paths?
            R::Exit(result) => return result,
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
                dbg!("here");
                children.retain(|child| child.borrow().statement() != leaf.borrow().statement());
                dbg!("& here");
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

// // marks a path as finished in the path tree. (only if there are no valid states left for that path)
// // if both none, move up & mark it as none
// fn finish_state_in_path(tree: &mut PathTree, path: Vec<ProgramCounter>) {
//     let mut idx = path.len();
//     loop {
//         idx = idx - 1;
//         let last = path[idx];
//         let parent = path[idx - 1];

//         // Remove the states from the tree.
//         let states = tree.nodes.remove(&last).unwrap().into_states().unwrap();

//         let parent_nodes = tree.nodes.get_mut(&parent).unwrap();

//         if let TreeNode::Node(subnodes) = parent_nodes {
//             // Remove the finished state from the parent node
//             subnodes.retain(|pc| *pc != last);

//             // TODO: We could add an optimization here.. to reduce nesting when there is only 1 branch left.
//             // if subnodes.len() == 1 {
//             //     *parent_nodes = TreeNode::Leaf(subnodes[0]);
//             // }

//             // if the parent node has unfinished states left, continue.
//             // otherwise we are done.
//             if subnodes.len() != 0 {
//                 break;
//             }
//         } else {
//             panic!("Unexpected Leaf");
//         }
//     }
// }

// // marks a path as finished in the path tree.
// // if both none, move up & mark it as none
// fn finish_state_in_path(tree: &mut BTree, path: Vec<u64>) {
//     let mut path_entries = path.into_iter();
//     loop {
//         let branch = path_entries.next().unwrap();
//         let next_branch = path_entries.next().unwrap();
//         match tree {
//             BTree::Node { false_, true_, statement } => {
//                 assert!(branch == *statement);

//                 match (false_, true_) {
//                     (Some(false_), Some(true_)) => if next_branch == false_.statement() {

//                     }

//                     (None, Some(true_)) => tree = true_,
//                     (Some(false_), None) => tree = false_,
//                     (None, None) => panic!()
//                 }

//             }
//             BTree::Leaf(_) => return (path, tree),
//         }
//     }
// }
