use std::{
    cell::RefCell,
    collections::HashMap,
    ops::Deref,
    rc::{Rc, Weak},
};

use itertools::Itertools;
use slog::{debug, Logger};

use crate::{
    cfg::{CFGStatement, MethodIdentifier},
    exec::{IdCounter, SymResult},
    statistics::Statistics,
    symbol_table::SymbolTable,
};

use super::{execute_instruction_for_all_states, finish_state_in_path, ProgramCounter, State};

pub(super) trait ExecutionTreeBasedHeuristic {
    fn choice(
        &mut self,
        root: Rc<RefCell<ExecutionTree>>,
        program: &HashMap<u64, CFGStatement>,
        flows: &HashMap<u64, Vec<u64>>,
        st: &SymbolTable,
        entry_method: &MethodIdentifier,
        coverage: &mut HashMap<ProgramCounter, usize>,
    ) -> Rc<RefCell<ExecutionTree>>;

    /// Writes the program to a file 'visualize', with some information for each statement provided by the decorator.
    fn visualize<'a>(
        &self,
        program: &HashMap<ProgramCounter, CFGStatement>,
        flows: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
        st: &SymbolTable,
    ) {
        let s = crate::prettyprint::cfg_pretty::pretty_print_compilation_unit(
            &|pc| Some(pc.to_string()),
            program,
            &flows,
            st,
        );
        std::fs::write("visualize", &s).unwrap();
        // std::thread::sleep(std::time::Duration::from_millis(300));
    }
}

/// A tree datastructure where a node represents a statement where the program forked,
/// with in the leafs the set of states currently being verificated.
///
/// We assume that each state in a leaf is at the same program point. They may differ in stack and/or heap due to for example array initialisation.
#[derive(Debug)]
pub(super) enum ExecutionTree {
    Node {
        parent: Weak<RefCell<ExecutionTree>>,
        statement: u64,
        children: Vec<Rc<RefCell<ExecutionTree>>>,
    },
    Leaf {
        parent: Weak<RefCell<ExecutionTree>>,
        statement: u64,
        states: Vec<State>,
    },
}

impl ExecutionTree {
    pub(super) fn parent(&self) -> Weak<RefCell<ExecutionTree>> {
        match self {
            ExecutionTree::Node { parent, .. } => parent.clone(),
            ExecutionTree::Leaf { parent, .. } => parent.clone(),
        }
    }

    /// Return the current program point that the leaf or node is in.
    pub(super) fn statement(&self) -> u64 {
        match self {
            ExecutionTree::Node { statement, .. } => *statement,
            ExecutionTree::Leaf { statement, .. } => *statement,
        }
    }
    /// Assume it is a leaf and take out the states.
    pub(super) fn into_states(&mut self) -> Option<Vec<State>> {
        if let ExecutionTree::Leaf { states, .. } = self {
            // Take the state, leaving an empty array
            let states = std::mem::take(states);
            Some(states)
        } else {
            None
        }
    }

    pub(super) fn set_states(&mut self, new_states: Vec<State>) {
        if let ExecutionTree::Leaf {
            states, statement, ..
        } = self
        {
            // Set the states
            *statement = new_states[0].pc;
            *states = new_states;
        } else {
            panic!()
        }
    }

    pub(super) fn set_parent(&mut self, new_parent: Weak<RefCell<ExecutionTree>>) {
        match self {
            ExecutionTree::Node { parent, .. } => *parent = new_parent,
            ExecutionTree::Leaf { parent, .. } => *parent = new_parent,
        }
    }

    /// Returns the set of leaf nodes
    pub(super) fn leafs(node: Rc<RefCell<ExecutionTree>>) -> Vec<Rc<RefCell<ExecutionTree>>> {
        match node.borrow().deref() {
            ExecutionTree::Node { children, .. } => {
                children.iter().cloned().map(ExecutionTree::leafs).concat()
            }
            ExecutionTree::Leaf { .. } => vec![node.clone()],
        }
    }
}

/// A symbolic execution approach using an execution tree based heuristic.
pub(super) fn sym_exec_execution_tree(
    state: State,
    program: &HashMap<u64, CFGStatement>,
    flows: &HashMap<u64, Vec<u64>>,
    k: u64,
    st: &SymbolTable,
    root_logger: Logger,
    path_counter: Rc<RefCell<IdCounter<u64>>>,
    statistics: &mut Statistics,
    entry_method: MethodIdentifier,
    mut heuristic: impl ExecutionTreeBasedHeuristic,
    visualize_heuristic: bool,
) -> SymResult {
    // let mut paths = PathTree {root: state.pc, nodes: HashMap::from([(state.pc, TreeNode::Leaf(vec![state]))]) };
    let tree = Rc::new(RefCell::new(ExecutionTree::Leaf {
        parent: Weak::new(),
        statement: state.pc,
        states: vec![state],
    }));

    let mut coverage = HashMap::new();
    loop {
        let states_node = heuristic.choice(
            tree.clone(),
            program,
            flows,
            st,
            &entry_method,
            &mut coverage,
        );
        let current_pc = states_node.borrow().statement();
        *coverage.entry(current_pc).or_insert(0) += 1;
        let chosen_state = states_node.borrow_mut().into_states().unwrap();

        let states = chosen_state;

        if visualize_heuristic {
            heuristic.visualize(program, flows, st);
        }

        let r = execute_instruction_for_all_states(
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
            Ok(new_states) => {
                // assert!(new_states.len() <= 2);
                for (pc, states) in &new_states {
                    // debug!(
                    //     root_logger,
                    //     "all pcs should be equal {}, {:?}",
                    //     pc,
                    //     states.iter().map(|s| s.pc).collect_vec()
                    // );
                    if !states.iter().all(|s| s.pc == *pc) {
                        loop {}
                    }
                    assert!(states.iter().all(|s| s.pc == *pc));
                }

                match new_states.len() {
                    0 => {
                        // Branch finished due to "throw"
                        // dbg!(current_pc, &program[&current_pc]);
                        // if let Some(parent) = states_node.borrow().parent().upgrade() {
                        //     dbg!(parent.borrow().deref().statement());
                        // } else {
                        //     dbg!("no parent");
                        // }
                        let is_finished = finish_state_in_path(states_node.clone());
                        if is_finished {
                            // We have explored all states.
                            debug!(root_logger, "all states explored");
                            return SymResult::Valid;
                        }
                    }
                    1 => {
                        let (_pc, states) = new_states.into_iter().next().unwrap();
                        // debug!(root_logger, "new state {:?}", pc);

                        // let mut tree = Rc::new(RefCell::new(N::Leaf(Weak::new(), states)));
                        // tree.borrow_mut().set_parent(Rc::<_>::downgrade(&tree));

                        states_node.borrow_mut().set_states(states);

                        // *states_node.borrow_mut() = N::Leaf { parent: Weak::new(), states };
                    }
                    _n => {
                        // Branching, split up states
                        // We replace the leaf with a node at the branching statement, its children are the new paths each in a different direction.
                        debug!(
                            root_logger,
                            "new states: {:?}",
                            new_states.iter().map(|(pc, _)| pc).collect_vec()
                        );

                        let states = new_states
                            .into_iter()
                            .map(|(pc, states)| {
                                Rc::new(RefCell::new(ExecutionTree::Leaf {
                                    parent: Rc::downgrade(&states_node),
                                    statement: pc,
                                    states: states,
                                }))
                            })
                            .collect();

                        // assert!(true_.len() > 0 && false_.len() > 0);

                        let parent = states_node.borrow().parent();
                        *states_node.borrow_mut() = ExecutionTree::Node {
                            parent,
                            statement: current_pc,
                            children: states,
                        }
                    }
                }
            }
            Err(info) => return SymResult::Invalid(info),
        }
    }
}
