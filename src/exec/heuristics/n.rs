use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    ops::Deref,
    rc::{Rc, Weak},
};

use itertools::Itertools;

use super::{Cost, ProgramCounter, State};

#[derive(Debug)]
pub(super) enum N {
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
    pub(super) fn parent(&self) -> Weak<RefCell<N>> {
        match self {
            N::Node { parent, .. } => parent.clone(),
            N::Leaf { parent, .. } => parent.clone(),
        }
    }

    pub(super) fn statement(&self) -> u64 {
        match self {
            N::Node { statement, .. } => *statement,
            N::Leaf { statement, .. } => *statement,
        }
    }
    /// Assume it is a leaf and take out the states.
    pub(super) fn into_states(&mut self) -> Option<Vec<State>> {
        if let N::Leaf { states, .. } = self {
            // Take the state, leaving an empty array
            let states = std::mem::take(states);
            Some(states)
        } else {
            None
        }
    }

    pub(super) fn set_states(&mut self, new_states: Vec<State>) {
        if let N::Leaf {
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

    pub(super) fn set_parent(&mut self, new_parent: Weak<RefCell<N>>) {
        match self {
            N::Node { parent, .. } => *parent = new_parent,
            N::Leaf { parent, .. } => *parent = new_parent,
        }
    }

    pub(super) fn leafs(node: Rc<RefCell<N>>) -> Vec<Rc<RefCell<N>>> {
        match node.borrow().deref() {
            N::Node { children, .. } => children.iter().cloned().map(N::leafs).concat(),
            N::Leaf { .. } => vec![node.clone()],
        }
    }
}
