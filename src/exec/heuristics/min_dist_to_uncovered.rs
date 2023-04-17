use std::{
    cell::{Ref, RefCell},
    collections::{HashMap, HashSet},
    ops::Deref,
    rc::{Rc, Weak},
    time::Duration,
};

use criterion::measurement::Measurement;
use itertools::Itertools;
use rand::{
    distributions::{WeightedError, WeightedIndex},
    prelude::Distribution,
    Rng,
};
use slog::{debug, Logger};

use crate::{
    cfg::{CFGStatement, MethodIdentifier},
    exec::{
        find_entry_for_static_invocation,
        heuristics::{finish_state_in_path, Cost},
        IdCounter, State, SymResult,
    },
    prettyprint::cfg_pretty::pretty_print_compilation_unit,
    statistics::Statistics,
    symbol_table::SymbolTable,
    syntax::{Declaration, Invocation, Method, Rhs, Statement},
    DeclarationMember,
};

use crate::exec::heuristics::execute_instruction_for_all_statements;

use super::{md2u_recursive, n::N, ProgramCounter, R};

/// Make a weighted stochastic choice, where the weight is calculated based on the distance to a newly uncovered branch.
/// Choose between all leafs (states on different program points)
/// If all weights are zero, that means that all statements have been covered and it falls back on random state choice.
fn choice<'a>(
    leafs: &Vec<Rc<RefCell<N>>>,
    md2u: &HashMap<ProgramCounter, md2u_recursive::Distance>,
    rng: &'a mut impl Rng,
) -> Rc<RefCell<N>> {
    // Find for each leaf the md2u, construct a WeightedIndex and sample one leaf.
    if md2u.len() == 0 {
        let idx = rng.gen_range(0..leafs.len());
        return leafs[idx].clone();
    }
    let weights = leafs.iter().map(|n| n.borrow().statement()).map(|pc| {
        let distance = md2u.get(&pc);
        // if distance.is_none() {
        //     dbg!(&md2u);
        // }
        let distance = distance.unwrap();
        match distance.distance_type {
            md2u_recursive::DistanceType::ToFirstUncovered => 1.0 / distance.value as f64,
            md2u_recursive::DistanceType::ToEndOfMethod => 0.0,
        }
    });
    match WeightedIndex::new(weights) {
        Ok(wi) => {
            let idx = wi.sample(rng);
            return leafs[idx].clone();
        }
        Err(WeightedError::AllWeightsZero) => {
            let idx = rng.gen_range(0..leafs.len());
            return leafs[idx].clone();
        }
        Err(err) => panic!("{}", err),
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
    entry_method: MethodIdentifier,
) -> SymResult {
    // dbg!(flows);
    // dbg!(program);

    let mut rng = rand::thread_rng();
    let mut coverage = HashMap::new();
    let mut md2u_cache = md2u_recursive::Cache::new();

    let (_distance, mut md2u) = md2u_recursive::min_distance_to_uncovered_method(
        entry_method.clone(),
        &coverage,
        program,
        flows,
        st,
        &mut md2u_cache,
    );

    let s = crate::prettyprint::cfg_pretty::pretty_print_cfg_method(
        entry_method.clone(),
        &|pc| Some(format!("pc: {}, cost: {}", pc, md2u[&pc].value)),
        &program,
        &flows,
        &st,
    );
    println!("{}", s);

    let root_pc = state.pc;

    // let mut paths = PathTree {root: state.pc, nodes: HashMap::from([(state.pc, TreeNode::Leaf(vec![state]))]) };
    let tree = Rc::new(RefCell::new(N::Leaf {
        parent: Weak::new(),
        statement: state.pc,
        states: vec![state],
    }));

    loop {
        let leafs = N::leafs(tree.clone());
        // pointer to the leaf with states chosen by the heuristic
        // md2u = min_distance_to_uncovered(root_pc, &coverage, successors(program, flows, st));
        let new_md2u = md2u_recursive::min_distance_to_uncovered_method(
            entry_method.clone(),
            &coverage,
            program,
            flows,
            st,
            &mut md2u_cache,
        )
        .1;
        md2u.extend(new_md2u);
        // dbg!(&md2u);

        let states_node = choice(&leafs, &md2u, &mut rng);

        let current_pc = states_node.borrow().statement();

        // let decorator = &|pc| Some(format!("pc: {}, cost: {:?} {}", pc, md2u.get(&pc).and_then(|d| if let md2u_recursive::DistanceType::ToFirstUncovered = d.distance_type { Some(d.value) } else { None}),
        // if pc == current_pc { " <<<<" } else { "" }));

        // let s = pretty_print_compilation_unit(decorator, program, &flows, st);
        // std::fs::write("visualize", &s).unwrap();
        // std::thread::sleep(std::time::Duration::from_millis(300));

        // Update the coverage
        *coverage.entry(current_pc).or_insert(0) += 1;
        let chosen_state = states_node.borrow_mut().into_states().unwrap();

        let states = chosen_state;

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
                // assert!(new_states.len() <= 2);
                for (pc, states) in &new_states {
                    debug!(
                        root_logger,
                        "all pcs should be equal {}, {:?}",
                        pc,
                        states.iter().map(|s| s.pc).collect_vec()
                    );
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
                        let is_finished = finish_state_in_path(states_node.clone(), Vec::new());
                        if is_finished {
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
                    n => {
                        // Branching, split up states
                        // We replace the leaf with a node at the branching statement, its children are the new paths each in a different direction.
                        debug!(
                            root_logger,
                            "new states: {:?}",
                            new_states.iter().map(|(pc, _)| pc).collect_vec()
                        );

                        // let ((true_pc, true_), (false_pc, false_)) =
                        //     new_states.into_iter().collect_tuple().unwrap();

                        let states = new_states
                            .into_iter()
                            .map(|(pc, states)| {
                                Rc::new(RefCell::new(N::Leaf {
                                    parent: Rc::downgrade(&states_node),
                                    statement: pc,
                                    states: states,
                                }))
                            })
                            .collect();

                        // assert!(true_.len() > 0 && false_.len() > 0);

                        let parent = states_node.borrow().parent();
                        *states_node.borrow_mut() = N::Node {
                            parent,
                            statement: current_pc,
                            children: states,
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

#[cfg(test)]
mod tests {
    use crate::Options;

    use super::*;

    #[test]
    fn min() {
        let path = "./examples/psv/min.oox";
        let k = 150;
        let options = Options::default_with_k_and_heuristic(k, crate::Heuristic::MinDist2Uncovered);

        assert_eq!(
            crate::verify(&path, "Foo", "min", options).unwrap(),
            SymResult::Valid
        );
    }
}
