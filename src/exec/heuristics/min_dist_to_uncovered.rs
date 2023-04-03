use std::{
    cell::RefCell,
    collections::HashMap,
    ops::Deref,
    rc::{Rc, Weak},
};

use itertools::Itertools;
use rand::{
    distributions::{WeightedIndex},
    prelude::Distribution,
    Rng,
};
use slog::{debug, Logger};

use crate::{
    cfg::CFGStatement,
    exec::{
        find_entry_for_static_invocation,
        heuristics::{finish_state_in_path, Cost},
        IdCounter, State, SymResult,
    },
    statistics::Statistics,
    symbol_table::SymbolTable,
    syntax::{Declaration, Invocation, Method, Rhs, Statement},
};

use crate::exec::heuristics::execute_instruction_for_all_statements;

use super::{ProgramCounter, N, R};

/// edge cost in dijkstra's algorithm

/// Make a weighted stochastic choice, where the weight is calculated based on the distance to a newly uncovered branch.
fn choice<'a>(
    mut tree: Rc<RefCell<N>>,
    md2u: &HashMap<ProgramCounter, Cost>,
    rng: &'a mut impl Rng,
) -> Rc<RefCell<N>> {
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
                // I expect here that some elements are not in md2u, they should be assigned 0 in the weights.
                // We should move weighted index to somewhere it is created only once.
                let weights = children
                    .iter()
                    .map(|child| 1.0 / md2u[&child.borrow().statement()] as f32);
                let wi = WeightedIndex::new(weights).unwrap();
                let idx = wi.sample(rng);

                tree = children[idx].clone();
            }
            N::Leaf { statement, .. } => {
                path.push(*statement);
                return tree;
            }
        };
    }
}

/// Explores all nodes in the tree, if the path is finished, we don't insert it into the result.
/// Returns for each program counter with a reachable path to an unexplored statement the distance to that statement.
fn min_distance_to_uncovered<'a, FN>(
    start: u64,
    coverage: &HashMap<ProgramCounter, usize>,
    mut successors: FN,
) -> HashMap<ProgramCounter, Cost>
where
    FN: FnMut(&ProgramCounter) -> Box<dyn Iterator<Item = (u64, u64)> + 'a>,
{
    fn goal(pc: &ProgramCounter, coverage: &HashMap<ProgramCounter, usize>) -> bool {
        coverage.contains_key(pc)
    }


    struct T<'a> {
        pc: u64,
        cost: u64,
        children_left: Box<dyn Iterator<Item = (u64, u64)> + 'a>,
    }
    // we implicitly assume that start is not a goal,

    let mut pc_to_cost = HashMap::new();

    let mut stack = Vec::new();

    stack.push(T {
        pc: start,
        cost: u64::MAX,
        children_left: successors(&start),
    });

    // dfs
    while let Some(T {
        pc,
        cost,
        mut children_left,
    }) = stack.pop()
    {
        // Check next successor
        if let Some((successor, _)) = children_left.next() {
            // We will come back later to check other children.
            stack.push(T {
                pc,
                cost,
                children_left,
            });

            if goal(&successor, coverage) {
                // Insert the cost and we are done
                pc_to_cost.insert(successor, 0);
            } else {
                // We still have to check its children
                stack.push(T {
                    pc: successor,
                    cost: u64::MAX,
                    children_left: successors(&start),
                });
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

fn with_cost(pc: ProgramCounter) -> (ProgramCounter, Cost) {
    (pc, 1)
}

/// Returns a function that is used by the pathfinding algorithm to find successors for each node.
/// What the returned function does is given a node, return all the neighbouring nodes with their cost.
fn successors<'a>(
    program: &'a HashMap<ProgramCounter, CFGStatement>,
    flow: &'a HashMap<ProgramCounter, Vec<ProgramCounter>>,
    st: &'a SymbolTable,
) -> impl Fn(&u64) -> Box<dyn Iterator<Item = (ProgramCounter, Cost)> + 'a> {
    move |pc: &u64| {
        let statement = &program[pc];
        match statement {
            CFGStatement::Statement(Statement::Call { invocation, .. })
            | CFGStatement::Statement(Statement::Assign {
                rhs: Rhs::RhsCall { invocation, .. },
                ..
            }) => {
                let resolved_to_pc = |(decl, method): &(Declaration, Rc<Method>)| {
                    find_entry_for_static_invocation(
                        &decl.name(),
                        &method.name,
                        invocation.argument_types(),
                        program,
                        st,
                    )
                };
                match invocation {
                    Invocation::InvokeMethod { resolved, .. } => {
                        // A regular method can resolve to multiple different methods due to dynamic dispatch, depending on the runtime type of the object.
                        // We make here the assumption that any object can be represented and thus consider each resolved method.

                        // We also need to lookup the program counter for each method. (CANT WE DO THIS BEFOREHAND?)
                        Box::new(
                            resolved
                                .iter()
                                .flat_map(HashMap::iter)
                                .map(|(_, resolved)| resolved)
                                .map(resolved_to_pc)
                                .map(with_cost),
                        )
                    }
                    Invocation::InvokeSuperMethod { resolved, .. }
                    | Invocation::InvokeConstructor { resolved, .. }
                    | Invocation::InvokeSuperConstructor { resolved, .. } => Box::new(
                        resolved
                            .iter()
                            .map(AsRef::as_ref)
                            .map(resolved_to_pc)
                            .map(with_cost),
                    ),
                }
            }

            // Otherwise take the flow
            _ => Box::new(flow[pc].iter().copied().map(with_cost)),
        }
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
    flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
) -> SymResult {
    let mut rng = rand::thread_rng();
    let mut coverage = HashMap::new();
    let mut md2u = min_distance_to_uncovered(state.pc, &coverage, successors(program, flow, st));

    // let mut paths = PathTree {root: state.pc, nodes: HashMap::from([(state.pc, TreeNode::Leaf(vec![state]))]) };
    let mut tree = Rc::new(RefCell::new(N::Leaf {
        parent: Weak::new(),
        statement: state.pc,
        states: vec![state],
    }));

    loop {
        // pointer to the leaf with states chosen by the heuristic

        let states_node = choice(tree.clone(), &md2u, &mut rng);
        let current_pc = states_node.borrow().statement();
        // Update the coverage
        *coverage.entry(current_pc).or_insert(0) += 1;
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
                        let is_finished = finish_state_in_path(states_node.clone(), Vec::new());
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

#[test]
fn test_partial_dijkstra() {
    use std::collections::HashSet;
    let neighbours: HashMap<u64, Vec<u64>> = HashMap::from([
        (4, vec![3, 2]),
        (3, vec![]),
        (2, vec![1, 5]),
        (1, vec![6]),
        (5, vec![124124]),
        (6, vec![1234]),
    ]);
    let goal = HashSet::from([4, 5, 6]);

    /// Explores all nodes in the tree, if the path is finished, we don't insert it into the result.
    /// Returns for each program counter with a reachable path to an unexplored statement the distance to that statement.
    fn doesit<'a, FS, FN>(
        start: u64,
        mut goal: FS,
        mut successors: FN,
    ) -> HashMap<ProgramCounter, Cost>
    where
        FS: FnMut(&ProgramCounter) -> bool,
        FN: FnMut(&ProgramCounter) -> &'a Vec<u64>,
    {
        struct T {
            pc: u64,
            cost: u64,
            children_checked: u64,
        }
        // we implicitly assume that start is not a goal,

        let mut pc_to_cost = HashMap::new();

        let mut stack = Vec::new();

        stack.push(T {
            pc: start,
            cost: u64::MAX,
            children_checked: 0,
        });

        // dfs
        while let Some(T {
            pc,
            cost,
            children_checked,
        }) = stack.pop()
        {
            let successors = successors(&pc);

            if children_checked >= successors.len().try_into().unwrap() {
                // This node has checked all its children
                // Find the minimal cost of its children, if any
                let cost = successors
                    .iter()
                    .filter_map(|succ| pc_to_cost.get(succ))
                    .min();
                if let Some(cost) = cost {
                    pc_to_cost.insert(pc, *cost + 1);
                }
            } else {
                // We will come back later to check other children.
                stack.push(T {
                    pc,
                    cost,
                    children_checked: children_checked + 1,
                });

                // Check next successor
                let successor = successors[children_checked as usize];

                if goal(&successor) {
                    // Insert the cost and we are done
                    pc_to_cost.insert(successor, 0);
                } else {
                    // We still have to check its children
                    stack.push(T {
                        pc: successor,
                        cost: u64::MAX,
                        children_checked: 0,
                    });
                }
            }
        }

        pc_to_cost
    }

    let result = doesit(4, |pc| goal.contains(pc), |pc| &neighbours[pc]);
    dbg!(result);
}
