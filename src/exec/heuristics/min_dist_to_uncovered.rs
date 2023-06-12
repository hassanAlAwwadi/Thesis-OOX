use std::{cell::RefCell, collections::HashMap, rc::Rc};

use rand::{
    distributions::{WeightedError, WeightedIndex},
    prelude::Distribution,
    rngs::ThreadRng,
    Rng,
};
use slog::Logger;

use crate::{
    cfg::{CFGStatement, MethodIdentifier},
    exec::{IdCounter, State, SymResult},
    statistics::Statistics,
    symbol_table::SymbolTable, Options,
};

use super::{
    execution_tree::{sym_exec_execution_tree, ExecutionTree, ExecutionTreeBasedHeuristic},
    utils::md2u_recursive::{self, Distance},
    ProgramCounter,
};

/// Make a weighted stochastic choice, where the weight is calculated based on the distance to a newly uncovered branch.
/// Choose between all leafs (states on different program points)
/// If all weights are zero, that means that all statements have been covered and it falls back on random state choice.
fn choice<'a>(
    leafs: &Vec<Rc<RefCell<ExecutionTree>>>,
    md2u: &HashMap<ProgramCounter, md2u_recursive::Distance>,
    rng: &'a mut impl Rng,
) -> Rc<RefCell<ExecutionTree>> {
    // Find for each leaf the md2u, construct a WeightedIndex and sample one leaf.
    if md2u.len() == 0 {
        let idx = rng.gen_range(0..leafs.len());
        return leafs[idx].clone();
    }
    let weights = leafs.iter().map(|n| n.borrow().statement()).map(|pc| {
        let distance = md2u.get(&pc);
        if distance.is_none() {
            dbg!(pc, &md2u);
        }
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

pub(super) struct MinDist2Uncovered {
    rng: ThreadRng,
    md2u_cache: md2u_recursive::Cache,
    md2u: HashMap<u64, Distance>,
}

impl MinDist2Uncovered {
    pub(super) fn new() -> MinDist2Uncovered {
        MinDist2Uncovered {
            rng: rand::thread_rng(),
            md2u_cache: md2u_recursive::Cache::new(),
            md2u: HashMap::new(),
        }
    }
}

impl ExecutionTreeBasedHeuristic for MinDist2Uncovered {
    fn choice(
        &mut self,
        root: Rc<RefCell<ExecutionTree>>,
        program: &HashMap<u64, CFGStatement>,
        flows: &HashMap<u64, Vec<u64>>,
        st: &SymbolTable,
        entry_method: &MethodIdentifier,
        coverage: &mut HashMap<ProgramCounter, usize>,
    ) -> Rc<RefCell<ExecutionTree>> {
        let leafs = ExecutionTree::leafs(root.clone());

        let new_md2u = md2u_recursive::min_distance_to_uncovered_method(
            entry_method,
            &coverage,
            program,
            flows,
            st,
            &mut self.md2u_cache,
        )
        .1;
        self.md2u.extend(new_md2u);

        let states_node = choice(&leafs, &self.md2u, &mut self.rng);

        states_node
    }
}

/// The main function for the symbolic execution
pub(crate) fn sym_exec(
    state: State,
    program: &HashMap<u64, CFGStatement>,
    flows: &HashMap<u64, Vec<u64>>,
    st: &SymbolTable,
    root_logger: Logger,
    path_counter: Rc<RefCell<IdCounter<u64>>>,
    statistics: &mut Statistics,
    entry_method: MethodIdentifier,
    options: &Options,
) -> SymResult {
    sym_exec_execution_tree(
        state,
        program,
        flows,
        st,
        root_logger,
        path_counter,
        statistics,
        entry_method,
        MinDist2Uncovered::new(),
        options,
    )
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
            crate::verify(&[path], "Foo", "min", options).unwrap(),
            SymResult::Valid
        );
    }
}
