use std::{
    cell::RefCell,
    ops::Deref,
    rc::{Rc, Weak},
};

use itertools::Itertools;

use super::{Cost, ProgramCounter, State};

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
            ExecutionTree::Node { children, .. } => children.iter().cloned().map(ExecutionTree::leafs).concat(),
            ExecutionTree::Leaf { .. } => vec![node.clone()],
        }
    }
}
