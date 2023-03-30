use std::{
    cell::RefCell,
    collections::HashMap,
    ops::{Deref, DerefMut},
    rc::{Rc, Weak},
};

use itertools::Itertools;
use rand::Rng;
use slog::{debug, Logger};

use crate::{cfg::CFGStatement, exec::{Engine, heuristics::N}, statistics::Statistics, symbol_table::SymbolTable};

use super::{action, ActionResult, IdCounter, State, SymResult, execute_instruction_for_all_statements, R, finish_state_in_path, ProgramCounter};

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
) -> (Vec<u64>, Rc<RefCell<N>>) {
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

                dbg!(children.len());

                let idx = rng.gen_range(0..children.len());
                tree = children[idx].clone();
            }
            N::Leaf { states, statement, .. } => {
                path.push(*statement);
                return (path, tree);
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

// pub struct RandomPathEngine<'a> {
//     remaining_states: &'a mut Vec<State>,
//     path_counter: Rc<RefCell<IdCounter<u64>>>,
//     statistics: &'a mut Statistics,
//     st: &'a SymbolTable,
// }

// impl Engine for RandomPathEngine<'_> {
//     fn add_remaining_state(&mut self, state: State) {
//         self.remaining_states.push(state);
//     }

//     fn add_remaining_states(&mut self, states: impl Iterator<Item = State>) {
//         self.remaining_states.extend(states);
//     }

//     fn next_path_id(&mut self) -> u64 {
//         self.path_counter.borrow_mut().next_id()
//     }

//     fn statistics(&mut self) -> &mut Statistics {
//         self.statistics
//     }

//     fn symbol_table(&self) -> &SymbolTable {
//         self.st
//     }
// }

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

    loop {
        // pointer to the leaf with states chosen by the heuristic

        let (path_pcs, states_node) = random_path(tree.clone(), &mut rng);
        let current_pc = *path_pcs.last().unwrap();
        let chosen_state = states_node.borrow_mut().into_states().unwrap();

        let mut states = chosen_state;

        let r = execute_instruction_for_all_statements(
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
                        let is_finished = finish_state_in_path(states_node.clone(), path_pcs);
                        if is_finished {
                            // *tree.borrow_mut() = N::Leaf {
                            //     parent: Weak::new(),
                            //     statement: 0,
                            //     states: vec![],
                            // };

                            // We have explored all states.
                            debug!(root_logger, "all states explored");
                            return SymResult::Valid;
                        }
                        
                    }
                    1 => {
                        let (pc, states) = new_states.into_iter().next().unwrap();
                        debug!(root_logger, "new state {:?}", pc);

                        // let mut tree = Rc::new(RefCell::new(N::Leaf(Weak::new(), states)));
                        // tree.borrow_mut().set_parent(Rc::<_>::downgrade(&tree));
                        assert_all_aliasmaps_are_equivalent(&states);
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


                        // testing whether all aliasmaps are equivalent, can be removed later
                        assert_all_aliasmaps_are_equivalent(&true_);
                        assert_all_aliasmaps_are_equivalent(&false_);

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


fn assert_all_aliasmaps_are_equivalent(states: &Vec<State>) -> bool {
    states.iter().map(|s| &s.alias_map).all_equal()
}