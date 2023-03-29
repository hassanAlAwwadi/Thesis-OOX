use std::{collections::{HashMap}, rc::{Rc, Weak}, cell::RefCell};

use itertools::Itertools;
use pathfinding::prelude::{dijkstra_partial, count_paths};
use slog::{Logger, debug};

use crate::{
    cfg::CFGStatement,
    exec::{find_entry_for_static_invocation, State, IdCounter, SymResult},
    symbol_table::SymbolTable,
    syntax::{Declaration, Invocation, Method, Rhs, Statement}, statistics::Statistics,
};

/// edge cost in dijkstra's algorithm
type Cost = u64;
type ProgramCounter = u64;


fn choice(tree: Rc<RefCell<N>>, md2u: HashMap<ProgramCounter, Cost>) {
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

    todo!()
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

enum R {
    /// The new states at one increased path counter, this occurs when there is no branch statement.
    /// Often this will be just one state, but it may happen that states are split due to e.g. array initialisation.
    Step(Vec<State>),
    /// A branch statement (if, while, foo.bar() dynamic dispatch to different functions)
    StateSplit(HashMap<u64, Vec<State>>),
    /// The path is finished, pruned or an invalid assert occured.
    Exit(SymResult),
}

/// Explores all nodes in the tree, if the path is finished, we don't insert it into the result.
/// Returns for each program counter with a reachable path to an unexplored statement the distance to that statement.
fn min_distance_to_uncovered<'a, FS, FN>(start: u64, mut goal: FS, mut successors: FN) -> HashMap<ProgramCounter, Cost>
    where
    FS: FnMut(&ProgramCounter) -> bool,
    FN: FnMut(&ProgramCounter) -> Box<dyn Iterator<Item = (u64, u64)> + 'a>  {

    struct T<'a> {
        pc: u64,
        cost: u64,
        children_left: Box<dyn Iterator<Item = (u64, u64)> + 'a> ,
    }
    // we implicitly assume that start is not a goal,


    let mut pc_to_cost = HashMap::new();
    

    let mut stack = Vec::new();

    stack.push(T {pc:start, cost: u64::MAX, children_left: successors(&start)});

    // dfs
    while let Some(T {pc, cost, mut children_left}) = stack.pop() {

        // Check next successor
        if let Some((successor, _)) = children_left.next() {
            // We will come back later to check other children.
            stack.push(T {pc, cost, children_left});
        
            if goal(&successor) {
                // Insert the cost and we are done 
                pc_to_cost.insert(successor, 0);
            } else {
                // We still have to check its children
                stack.push(T {pc: successor, cost: u64::MAX, children_left: successors(&start)});
            }
        } else {
            let children = successors(&pc);

            // This node has checked all its children
            // Find the minimal cost of its children, if any
            let cost = children.filter_map(|(succ, _)| pc_to_cost.get(&succ)).min();
            if let Some(cost) = cost {
                pc_to_cost.insert(pc, *cost + 1);
            }

        }
    }

    pc_to_cost
}


// /// Computes the minimal distance from the given program counter to any uncovered (= not seen before) statement.
// ///
// /// This is achieved through pathfinding algorithm.
// fn min_distance_to_uncovered(
//     pc: ProgramCounter,
//     coverage: &HashMap<ProgramCounter, bool>,
//     program: &HashMap<ProgramCounter, CFGStatement>,
//     flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
//     st: &SymbolTable,
// ) -> Option<u64> {
//     let successors_fn = successors(program, flow, st);
//     let goal_fn = |pc: &ProgramCounter| coverage[pc] == false;

//     let path = pathfinding::prelude::dijkstra(&pc, successors_fn, goal_fn);
    
//     path.map(|(path, _goal)| path.len() as u64)
// }

// fn with_cost(pc: ProgramCounter) -> (ProgramCounter, Cost) {
//     (pc, 1)
// }

// /// Returns a function that is used by the pathfinding algorithm to find successors for each node.
// /// What the returned function does is given a node, return all the neighbouring nodes with their cost.
// fn successors<'a>(
//     program: &'a HashMap<ProgramCounter, CFGStatement>,
//     flow: &'a HashMap<ProgramCounter, Vec<ProgramCounter>>,
//     st: &'a SymbolTable,
// ) -> impl Fn(&u64) -> Box<dyn Iterator<Item = (u64, u64)> + 'a> {
//     move |pc: &u64| {
//         let statement = &program[pc];
//         match statement {
//             CFGStatement::Statement(Statement::Call { invocation, .. })
//             | CFGStatement::Statement(Statement::Assign {
//                 rhs: Rhs::RhsCall { invocation, .. },
//                 ..
//             }) => {
//                 let resolved_to_pc = |(decl, method): &(Declaration, Rc<Method>)| {
//                     find_entry_for_static_invocation(
//                         &decl.name(),
//                         &method.name,
//                         invocation.argument_types(),
//                         program,
//                         st,
//                     )
//                 };
//                 match invocation {
//                     Invocation::InvokeMethod { resolved, .. } => {
//                         // A regular method can resolve to multiple different methods due to dynamic dispatch, depending on the runtime type of the object.
//                         // We make here the assumption that any object can be represented and thus consider each resolved method.

//                         // We also need to lookup the program counter for each method. (CANT WE DO THIS BEFOREHAND?)
//                         Box::new(
//                             resolved
//                                 .iter()
//                                 .flat_map(HashMap::iter)
//                                 .map(|(_, resolved)| resolved)
//                                 .map(resolved_to_pc)
//                                 .map(with_cost),
//                         )
//                     }
//                     Invocation::InvokeSuperMethod { resolved, .. }
//                     | Invocation::InvokeConstructor { resolved, .. }
//                     | Invocation::InvokeSuperConstructor { resolved, .. } => Box::new(
//                         resolved
//                             .iter()
//                             .map(AsRef::as_ref)
//                             .map(resolved_to_pc)
//                             .map(with_cost),
//                     ),
//                 }
//             }

//             // Otherwise take the flow
//             _ => Box::new(flow[pc].iter().copied().map(with_cost)),
//         }
//     }
// }



#[test]
fn test_partial_dijkstra() {
    use std::collections::HashSet;
    let neighbours: HashMap<u64, Vec<u64>> = HashMap::from([(4, vec![3, 2]), (3, vec![]), (2, vec![1, 5]), (1, vec![6]), (5, vec![124124]), (6, vec![1234])]);
    let goal = HashSet::from([4, 5, 6]);


    /// Explores all nodes in the tree, if the path is finished, we don't insert it into the result.
    /// Returns for each program counter with a reachable path to an unexplored statement the distance to that statement.
    fn doesit<'a, FS, FN>(start: u64, mut goal: FS, mut successors: FN) -> HashMap<ProgramCounter, Cost>
        where
        FS: FnMut(&ProgramCounter) -> bool,
        FN: FnMut(&ProgramCounter) -> &'a Vec<u64> {
        struct T {
            pc: u64,
            cost: u64,
            children_checked: u64,
        }
        // we implicitly assume that start is not a goal,


        let mut pc_to_cost = HashMap::new();

        let mut stack = Vec::new();

        stack.push(T {pc:start, cost: u64::MAX, children_checked: 0});

        // dfs
        while let Some(T {pc, cost, children_checked}) = stack.pop() {
            let successors = successors(&pc);

            if children_checked >= successors.len().try_into().unwrap() {
                // This node has checked all its children
                // Find the minimal cost of its children, if any
                let cost = successors.iter().filter_map(|succ| pc_to_cost.get(succ)).min();
                if let Some(cost) = cost {
                    pc_to_cost.insert(pc, *cost + 1);
                }
            } else {
                // We will come back later to check other children.
                stack.push(T {pc, cost, children_checked: children_checked + 1});

                // Check next successor
                let successor = successors[children_checked as usize];
            
                if goal(&successor) {
                    // Insert the cost and we are done 
                    pc_to_cost.insert(successor, 0);
                } else {
                    // We still have to check its children
                    stack.push(T {pc: successor, cost: u64::MAX, children_checked: 0});
                }
            }
        }

        pc_to_cost
    }


    let result = doesit(4, |pc| goal.contains(pc), |pc| &neighbours[pc]);
    dbg!(result);
}