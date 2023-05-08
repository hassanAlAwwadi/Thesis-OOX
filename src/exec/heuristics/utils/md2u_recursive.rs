//! This module contains an algorithm to compute the minimal distance to an uncovered statement, for every statement in a given method.
//! It also contains caching utility for when a method is fully explored.
//!
//! The approach we take is method-scoped, so a statement in a method has a distance either to the first uncovered statement in this method.
//! Otherwise it has the shortest distance to the end of the method.

use std::collections::{HashMap, HashSet};

use itertools::Itertools;

use crate::{
    cfg::{CFGStatement, MethodIdentifier, self},
    exec::find_entry_for_static_invocation,
    symbol_table::SymbolTable,
    Invocation, Rhs, Statement,
};

use super::super::{Cost, ProgramCounter};

/// A cache storing for a method the distance, will not contain distances for unexplored methods.
/// A method always has the same cost, with a distinction made between a cost achieved by finding an uncovered statement,
/// and otherwise a cost of calling the function in terms of the number of statements visited.
pub(crate) type Cache<'a> = HashMap<MethodIdentifier<'a>, CumulativeCost>;

/// Type of distance of a statement, can be either partially complete (to as far as it can see), which would be the exit of the method.
/// Or it can be the distance to the first uncovered statement, if any found.
#[derive(Debug, Hash, Eq, PartialEq, Clone, PartialOrd, Ord, Copy)]
pub enum DistanceType {
    ToFirstUncovered,
    ToEndOfMethod,
}

#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Clone, Copy)]
pub struct Distance {
    pub distance_type: DistanceType,
    /// Should be at least 1
    pub value: u64,
}

impl Distance {
    fn plus(mut self, cost: Cost) -> Distance {
        self.value += cost;
        self
    }
}

/// Calling a method will explore a certain number of statements before returning
/// If an uncovered statement is encountered, it will have an exact cost
/// Otherwise it returns the minimal cost of the method call in terms of the number of statements explored.
///
/// Since a method may contain method calls to itself and while loops, there are Cycle and UnexploredMethodCall variants.
/// There are used during the computation but are resolved to Cost(Distance) at the end.
#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum CumulativeCost {
    Cost(Distance),
    /// Cycles back to program point (while loop)
    Cycle(ProgramCounter),
    Plus(Box<CumulativeCost>, Box<CumulativeCost>),
    /// In case of recursion, we can not resolve it immediately and need to keep track of it.
    UnexploredMethodCall(String),
    /// Used to store cost when it cannot yet be determined which one is closer
    Minimal(Box<CumulativeCost>, Box<CumulativeCost>),
}

impl CumulativeCost {
    fn try_into_cost(self) -> Option<Distance> {
        if let CumulativeCost::Cost(d) = self {
            Some(d)
        } else {
            None
        }
    }

    fn increased_by_one(self) -> CumulativeCost {
        self.plus(1)
    }

    fn plus(self, cost: Cost) -> CumulativeCost {
        match self {
            Self::Cost(d) => Self::Cost(d.plus(cost)),
            Self::Plus(c1, c2) => Self::Plus(c1, Box::new(c2.plus(cost))),
            Self::UnexploredMethodCall(_) | Self::Cycle(_) => Self::Plus(
                Box::new(self),
                Box::new(Self::Cost(Distance {
                    value: cost,
                    distance_type: DistanceType::ToEndOfMethod,
                })),
            ),
            Self::Minimal(c1, c2) => {
                Self::Minimal(Box::new(c1.plus(cost)), Box::new(c2.plus(cost)))
            }
        }
    }
    /// Returns the type of distance of the cost expression
    /// If a Cycle or UnexploredMethodCall, we assume to the distance to be ToEndOfMethod
    ///
    /// In other words, ToFirstUncovered is returned if any of the variants in the Cost Expression are ToFirstUncovered.
    fn distance_type(&self) -> DistanceType {
        match self {
            Self::Cost(d) => d.distance_type,
            Self::Plus(a, b) | Self::Minimal(a, b) => {
                std::cmp::min(a.distance_type(), b.distance_type())
            }
            Self::Cycle(_) | Self::UnexploredMethodCall(_) => DistanceType::ToEndOfMethod,
        }
    }
}

/// Computes the minimal distance to uncovered methods for all program counters in this method
/// Recursively computes the minimal distance for any method calls referenced, in a depth-first-search way.
/// Returns:
///  - the distance of this method to the closest uncovered statement, or the end of the method.
///  - a mapping for every program counter explored to its distance
///  - a cache for methods explored may be reused.
pub(crate) fn min_distance_to_uncovered_method<'a>(
    method: MethodIdentifier<'a>,
    coverage: &HashMap<ProgramCounter, usize>,
    program: &'a HashMap<ProgramCounter, CFGStatement>,
    flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
    st: &SymbolTable,
    cache: &mut Cache<'a>,
) -> (Distance, HashMap<ProgramCounter, Distance>) {
    // We reset visited when the search is started from scratch
    let mut visited = HashSet::new();
    let (distance, pc_to_distance) = min_distance_to_uncovered_method_with_visited(
        method.clone(),
        coverage,
        program,
        flow,
        st,
        &mut visited,
        cache,
    );

    (distance, pc_to_distance)
}

fn min_distance_to_uncovered_method_with_visited<'a>(
    method: MethodIdentifier<'a>,
    coverage: &HashMap<ProgramCounter, usize>,
    program: &'a HashMap<ProgramCounter, CFGStatement>,
    flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
    st: &SymbolTable,
    visited: &mut HashSet<ProgramCounter>,
    cache: &mut Cache<'a>,
) -> (Distance, HashMap<ProgramCounter, Distance>) {
    let (cost, pc_to_cost) = min_distance_to_uncovered_method_helper(
        method.clone(),
        coverage,
        program,
        flow,
        st,
        visited,
        cache,
    );

    // dbg!(&cost, &method);
    let distance = if let CumulativeCost::Cost(distance) = cost {
        distance
    } else {
        panic!("expected solved distance");
    };

    // at this point all cost should be concrete distances.
    let pc_to_distance = pc_to_cost
        .into_iter()
        .map(|(key, value)| {
            let distance = if let CumulativeCost::Cost(distance) = value {
                distance
            } else {
                panic!("expected solved distance");
            };
            (key, distance)
        })
        .collect();

    // Clean up cache of incomplete methods
    let to_remove = cache
        .iter()
        .filter_map(|(k, v)| {
            if let CumulativeCost::Cost(d) = v {
                if d.distance_type == DistanceType::ToFirstUncovered {
                    Some(k.clone())
                } else {
                    None
                }
            } else {
                Some(k.clone())
            }
        })
        .collect_vec();

    cache.retain(|k, _v| !to_remove.contains(&k));

    (distance, pc_to_distance)
}

/// Computes the minimal distance to uncovered methods for all program counters in this method
/// Recursively computes the minimal distance for any method calls referenced.
fn min_distance_to_uncovered_method_helper<'a>(
    method: MethodIdentifier<'a>,
    coverage: &HashMap<ProgramCounter, usize>,
    program: &'a HashMap<ProgramCounter, CFGStatement>,
    flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
    st: &SymbolTable,
    visited: &mut HashSet<ProgramCounter>,
    cache: &mut Cache<'a>,
) -> (CumulativeCost, HashMap<ProgramCounter, CumulativeCost>) {
    let pc = find_entry_for_static_invocation(
        method.decl_name,
        method.method_name,
        method.arg_list.iter().cloned(),
        program,
        st,
    );
    let mut pc_to_cost = HashMap::new();

    let method_body_cost = min_distance_to_statement(
        pc,
        &method,
        coverage,
        program,
        flow,
        st,
        &mut pc_to_cost,
        cache,
        visited,
    );

    // dbg!(&method.method_name, &method_body_cost);
    let method_body_cost = match method_body_cost {
        CumulativeCost::Cost(d) => {
            cleanup_pc_to_cost(&method.method_name, &mut pc_to_cost, d);
            method_body_cost
        }
        _ => {
            // if the only unexplored method call is the current function
            // We can reduce it to the minimal cost to end of method.
            if is_reducable(&method_body_cost, &method) {
                // dbg!(&method_body_cost);
                let min_body_cost = reduce(&method_body_cost).unwrap();

                // This can be unwrapped since the only methods calls at this point are the method itself, and we replace that cost with concrete distance.
                let d = replace_method_call_in_costs(
                    &method.method_name,
                    method_body_cost,
                    min_body_cost,
                );

                // dbg!(&d);
                let d = reduce(&d).unwrap();

                cleanup_pc_to_cost(&method.method_name, &mut pc_to_cost, min_body_cost);
                CumulativeCost::Cost(d)
            } else {
                method_body_cost
            }
        }
    };

    cache.insert(method, method_body_cost.clone());

    (method_body_cost, pc_to_cost)
}

/// Computes the minimal distance to uncovered methods for all program counters in this method
/// Recursively computes the minimal distance for any method calls referenced.
fn min_distance_to_statement<'a>(
    pc: ProgramCounter,
    method: &MethodIdentifier<'a>,
    coverage: &HashMap<ProgramCounter, usize>,
    program: &'a HashMap<ProgramCounter, CFGStatement>,
    flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
    st: &SymbolTable,
    pc_to_cost: &mut HashMap<ProgramCounter, CumulativeCost>,
    cache: &mut Cache<'a>,
    visited: &mut HashSet<ProgramCounter>,
) -> CumulativeCost {
    visited.insert(pc);
    let mut stack = vec![pc];

    loop {
        let last = stack.len() == 1;

        // First ensure all other statements following this statement have been done.
        let successors_done = {
            let pc = *stack.last().unwrap();
            if pc_to_cost.contains_key(&pc) {
                continue;
            }
            visited.insert(pc);
            let mut all_there = true;
            if let Some(next_pcs) = flow.get(&pc) {
                for next_pc in next_pcs {
                    if !pc_to_cost.contains_key(&next_pc) {
                        if let CFGStatement::While(_, _) = &program[&next_pc] {
                            if visited.contains(next_pc) {
                                continue;
                            }
                        }
                        all_there = false;
                        stack.push(*next_pc);
                    }
                }
            }
            all_there
        };

        if !successors_done {
            // First we'll do the successors.
            continue;
        }

        let pc = stack.pop().unwrap();

        let remaining_cost = if let Some(next_pcs) = &flow.get(&pc) {
            match &next_pcs[..] {
                [] => unreachable!(),

                multiple => {
                    let mut remaining_costs = multiple.iter().map(|next_pc| {
                        if let CFGStatement::While(_, _) = &program[&next_pc] {
                            if visited.contains(next_pc) && cfg::utils::while_body_pcs(*next_pc, flow, program).contains(&pc) {
                                // Cycle detected (while loop or recursive function)
                                return (next_pc, CumulativeCost::Cycle(*next_pc));
                            }
                        }

                        (next_pc, pc_to_cost[next_pc].clone())
                    });

                    let next_cost = if let CFGStatement::While(_, _) = &program[&pc] {
                        // While loop is a special case due to cycles
                        let ((_body_pc, body_cost), (_exit_pc, exit_cost)) =
                            remaining_costs.next_tuple().unwrap();

                        minimize_while(exit_cost, body_cost)
                    } else {
                        remaining_costs
                            .map(|(_pc, cost)| cost)
                            .reduce(minimize)
                            .expect("multiple pcs")
                    };
                    next_cost
                }
            }
        } else {
            CumulativeCost::Cost(Distance {
                distance_type: DistanceType::ToEndOfMethod,
                value: 0,
            })
        };

        // Find the cost of the current statement
        let cost_of_this_statement =
            statement_cost(pc, coverage, program, flow, st, pc_to_cost, cache, visited);

        match cost_of_this_statement.clone() {
            CumulativeCost::Cost(Distance {
                value,
                distance_type,
            }) => {
                let cost = if distance_type == DistanceType::ToEndOfMethod {
                    // We have to add the cost of the remainder of the current method.
                    let cost = remaining_cost.plus(value);

                    // if this is a while statement, check all cycles and fix them
                    if let CFGStatement::While(_, _) = &program[&pc] {
                        fix_cycles(pc, cost.clone(), pc_to_cost);
                    }
                    cost
                } else {
                    // We can short-circuit back since an uncovered statement was encountered.
                    cost_of_this_statement
                };
                pc_to_cost.insert(pc, cost.clone());
            }
            CumulativeCost::Plus(_, _) => {
                let cost =
                    CumulativeCost::Plus(Box::new(cost_of_this_statement), Box::new(remaining_cost));

                pc_to_cost.insert(pc, cost.clone());
            }
            CumulativeCost::UnexploredMethodCall(_) => {
                let cost =
                    CumulativeCost::Plus(Box::new(cost_of_this_statement), Box::new(remaining_cost));
                pc_to_cost.insert(pc, cost.clone());
            }
            CumulativeCost::Cycle(_pc) => unreachable!(),

            CumulativeCost::Minimal(_, _) => {
                let cost =
                    CumulativeCost::Plus(Box::new(cost_of_this_statement), Box::new(remaining_cost));
                pc_to_cost.insert(pc, cost.clone());
            }
        }

        if last {
            return pc_to_cost[&pc].clone();
        }
    }
}

/// Returns the cost of exploring the statement
/// Can be either strictly in case of a found uncovered statement, or at least cost otherwise.
fn statement_cost<'a>(
    pc: ProgramCounter,
    coverage: &HashMap<ProgramCounter, usize>,
    program: &'a HashMap<ProgramCounter, CFGStatement>,
    flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
    st: &SymbolTable,
    pc_to_cost: &mut HashMap<ProgramCounter, CumulativeCost>,
    cache: &mut Cache<'a>,
    visited: &mut HashSet<ProgramCounter>,
) -> CumulativeCost {
    let statement = &program[&pc];

    if !coverage.contains_key(&pc) {
        // Uncovered statement, has strict 1 cost
        CumulativeCost::Cost(Distance {
            distance_type: DistanceType::ToFirstUncovered,
            value: 1,
        })
    } else if let Some(invocation) = statement.is_method_invocation() {
        // Case for a statement with an invocation.
        // An invocation has more cost than a regular statement, the resulting cost is returned.
        // If an unseen before method invocation is encountered, it will explore that first, and will add the results to the cache.
        let methods_called = invocation.methods_called();

        // Of all possible resolved methods, find the minimal cost to uncovered, or minimal cost to traverse.
        let min_method_cost = methods_called
            .into_iter()
            .map(|method| {
                // Check cache or compute cost for method

                let cost = if let Some(cost) = cache.get(&method) {
                    cost.clone()
                } else {
                    // if method is already covered, but not in cache it means we are processing it currently.
                    let next_pc = find_entry_for_static_invocation(
                        method.decl_name,
                        method.method_name,
                        method.arg_list.iter().cloned(),
                        program,
                        st,
                    );

                    if visited.contains(&next_pc) {
                        // dbg!("oh oh recursion", next_pc);
                        CumulativeCost::UnexploredMethodCall(method.method_name.to_string())
                    } else {
                        let (cost, method_pc_to_cost) = min_distance_to_uncovered_method_helper(
                            method, coverage, program, flow, st, visited, cache,
                        );

                        pc_to_cost.extend(method_pc_to_cost);
                        cost
                    }
                };
                cost.increased_by_one()
            })
            .reduce(minimize)
            .expect("at least one resolved method");

        min_method_cost
    } else {
        // A normal statement has at least cost 1, to be added to remainder
        CumulativeCost::Cost(Distance {
            distance_type: DistanceType::ToEndOfMethod,
            value: 1,
        })
    }
}

fn cleanup_pc_to_cost<'a>(
    method_name: &str,
    pc_to_cost: &'a mut HashMap<ProgramCounter, CumulativeCost>,
    resulting_cost: Distance,
) {
    let mut temp = HashMap::new();
    std::mem::swap(pc_to_cost, &mut temp);

    *pc_to_cost = temp
        .into_iter()
        .map(|(key, value)| {
            let cost = replace_method_call_in_costs(method_name, value.clone(), resulting_cost);
            // for some pc it might not be possible to reduce to a distance cost yet, due to unexplored method
            if let Some(distance) = reduce(&cost) {
                (key, CumulativeCost::Cost(distance))
            } else {
                (key, cost)
            }
        })
        .collect();
}

/// When a cost of a method consists of only costs or cycles we can reduce it to a distance
/// If it contains unexplored method calls we can only reduce it if that method call is this method itself.
fn is_reducable(c: &CumulativeCost, current_method: &MethodIdentifier) -> bool {
    match c {
        CumulativeCost::Cost(_) => true,
        CumulativeCost::Cycle(_) => true,
        CumulativeCost::Plus(c1, c2) => {
            is_reducable(c1, current_method) && is_reducable(c2, current_method)
        }
        CumulativeCost::UnexploredMethodCall(m) => current_method.method_name == m,
        CumulativeCost::Minimal(c1, c2) => {
            is_reducable(c1, current_method) && is_reducable(c2, current_method)
        }
    }
}

/// Returns the minimal route without method calls
/// Makes the assumption that all methods are infinitely large
fn reduce(c: &CumulativeCost) -> Option<Distance> {
    match c {
        CumulativeCost::Cost(d) => Some(*d),
        CumulativeCost::Plus(c1, c2) => {
            let d1 = reduce(&c1);
            let d2 = reduce(&c2);
            match (d1, d2) {
                (Some(d1), Some(d2)) => Some(Distance {
                    distance_type: std::cmp::min(d1.distance_type, d2.distance_type),
                    value: d1.value + d2.value,
                }),
                _ => None,
            }
        }
        CumulativeCost::UnexploredMethodCall(_) => None,
        CumulativeCost::Minimal(c1, c2) => {
            let d1 = reduce(&c1);
            let d2 = reduce(&c2);
            match (d1, d2) {
                (Some(d1), Some(d2)) => Some(std::cmp::min(d1, d2)),
                (Some(d1), None) => Some(d1),
                (None, Some(d2)) => Some(d2),
                _ => None,
            }
        }
        CumulativeCost::Cycle(_) => None,
        _ => unreachable!("{:?}", c),
    }
}

fn replace_method_call_in_costs<'a>(
    method_name: &str,
    cost: CumulativeCost,
    resulting_cost: Distance,
) -> CumulativeCost {
    match cost {
        CumulativeCost::Plus(ref c1, ref c2) => {
            let c1 = replace_method_call_in_costs(method_name, *c1.clone(), resulting_cost);
            let c2 = replace_method_call_in_costs(method_name, *c2.clone(), resulting_cost);
            match (c1, c2) {
                (CumulativeCost::Cost(d1), CumulativeCost::Cost(d2)) => {
                    CumulativeCost::Cost(Distance {
                        distance_type: std::cmp::min(d1.distance_type, d2.distance_type),
                        value: d1.value + d2.value,
                    })
                }
                _ => cost,
            }
        }
        CumulativeCost::UnexploredMethodCall(method) if method_name == &method => {
            CumulativeCost::Cost(resulting_cost)
        }
        CumulativeCost::Minimal(c1, c2) => {
            let c1 = replace_method_call_in_costs(method_name, *c1, resulting_cost);
            let c2 = replace_method_call_in_costs(method_name, *c2, resulting_cost);
            match (c1, c2) {
                (CumulativeCost::Cost(d1), CumulativeCost::Cost(d2)) => {
                    CumulativeCost::Cost(std::cmp::min(d1, d2))
                }
                (c1, c2) => CumulativeCost::Minimal(Box::new(c1), Box::new(c2)), // (c1, c2) => todo!("{:?} {:?}", c1, c2),
            }
        }
        cost => cost,
    }
}

fn fix_cycles(
    pc: ProgramCounter,
    resulting_cost: CumulativeCost,
    pc_to_cost: &mut HashMap<ProgramCounter, CumulativeCost>,
) {
    // dbg!(pc, &resulting_cost, &pc_to_cost);
    for (_k, cost) in pc_to_cost.iter_mut() {
        let mut temp = CumulativeCost::Cost(Distance {
            distance_type: DistanceType::ToEndOfMethod,
            value: 0,
        });
        std::mem::swap(cost, &mut temp);
        *cost = replace_cycles(pc, temp, &resulting_cost);
    }
    // dbg!(&pc_to_cost);

    fn replace_cycles(
        pc: ProgramCounter,
        cost: CumulativeCost,
        resulting_cost: &CumulativeCost,
    ) -> CumulativeCost {
        match cost {
            CumulativeCost::Cycle(cycle_pc) if pc == cycle_pc => resulting_cost.clone(),
            CumulativeCost::Plus(c1, c2) => CumulativeCost::Plus(
                Box::new(replace_cycles(pc, *c1, resulting_cost)),
                Box::new(replace_cycles(pc, *c2, resulting_cost)),
            ),
            CumulativeCost::Minimal(c1, c2) => CumulativeCost::Minimal(
                Box::new(replace_cycles(pc, *c1, resulting_cost)),
                Box::new(replace_cycles(pc, *c2, resulting_cost)),
            ),
            cost => cost,
        }
    }
}

/// Special case for minimizing while, if the body does not contain an uncovered statement,
/// the body cost will always be greater.
fn minimize_while(exit_cost: CumulativeCost, body_cost: CumulativeCost) -> CumulativeCost {
    // if body_cost is to uncovered
    if body_cost.distance_type() == DistanceType::ToFirstUncovered {
        minimize(body_cost, exit_cost)
    } else {
        // The body cost will always be more due to the cycle.
        exit_cost
    }
}

fn minimize(a: CumulativeCost, b: CumulativeCost) -> CumulativeCost {
    match (&a, &b) {
        (CumulativeCost::Cost(a), CumulativeCost::Cost(b)) => {
            CumulativeCost::Cost(std::cmp::min(a, b).clone())
        }
        (CumulativeCost::Cycle(_), CumulativeCost::Cycle(_)) => panic!(),
        (CumulativeCost::Cycle(_), _) => b.clone(),
        (_, CumulativeCost::Cycle(_)) => a.clone(),
        (_, _) => CumulativeCost::Minimal(Box::new(a), Box::new(b)),
    }
}

#[cfg(test)]
mod tests {

    use crate::{
        cfg::labelled_statements, parse_program,
        prettyprint::cfg_pretty::pretty_print_compilation_unit, typing::type_compilation_unit,
        utils, RuntimeType,
    };

    use super::*;

    fn decorator(
        pc_to_cost: &HashMap<ProgramCounter, Distance>,
    ) -> impl Fn(u64) -> Option<String> + '_ {
        |pc| {
            Some(format!(
                "pc: {}, cost: {}",
                pc,
                pc_to_cost
                    .get(&pc)
                    .map(
                        |d| if let DistanceType::ToFirstUncovered = d.distance_type {
                            format!("[{}]", d.value)
                        } else {
                            format!("{}", d.value)
                        }
                    )
                    .unwrap_or(String::new())
            ))
        }
    }

    fn setup(
        path: &str,
    ) -> (
        HashMap<ProgramCounter, usize>,
        HashMap<ProgramCounter, CFGStatement>,
        HashMap<ProgramCounter, Vec<u64>>,
        SymbolTable,
    ) {
        let file_content = std::fs::read_to_string(path).unwrap();

        let mut coverage = HashMap::new();
        let c = parse_program(&file_content, true).unwrap();

        let symbol_table = SymbolTable::from_ast(&c).unwrap();
        let c = type_compilation_unit(c, &symbol_table).unwrap();

        let (result, flw) = labelled_statements(c);

        let program: HashMap<u64, CFGStatement> = result.into_iter().collect();

        // Simulate that the method has been explored.
        coverage.extend(program.keys().map(|k| (*k, 1usize)));

        // dbg!(&program);

        let flows: HashMap<u64, Vec<u64>> = utils::group_by(flw.into_iter());

        (coverage, program, flows, symbol_table)
    }

    #[test]
    fn md2u_single_while1() {
        let path = "./examples/reachability/while.oox";
        let (coverage, program, flows, symbol_table) = setup(path);

        let s =
            pretty_print_compilation_unit(&|pc| format!("{}", pc).into(), &program, &flows, &symbol_table);
        println!("{}", s);


        let mut cache = Cache::new();
        let (cost, pc_to_cost) = min_distance_to_uncovered_method(
            MethodIdentifier {
                method_name: "main",
                decl_name: "Main",
                arg_list: vec![RuntimeType::IntRuntimeType; 1],
            },
            &coverage,
            &program,
            &flows,
            &symbol_table,
            &mut cache,
        );

        #[rustfmt::skip]
        let expected_result = HashMap::from([
            (0, Distance { distance_type: DistanceType::ToEndOfMethod, value: 7 }),
            (2, Distance { distance_type: DistanceType::ToEndOfMethod, value: 6 }),
            (5, Distance { distance_type: DistanceType::ToEndOfMethod, value: 5 }),
            (8, Distance { distance_type: DistanceType::ToEndOfMethod, value: 4 }),
            (10, Distance { distance_type: DistanceType::ToEndOfMethod, value: 6 }),
            (12, Distance { distance_type: DistanceType::ToEndOfMethod, value: 5 }),
            (15, Distance { distance_type: DistanceType::ToEndOfMethod, value: 3 }),
            (17, Distance { distance_type: DistanceType::ToEndOfMethod, value: 2 }),
            (18, Distance { distance_type: DistanceType::ToEndOfMethod, value: 1 }),
        ]);

        assert_eq!(pc_to_cost, expected_result);


        let s = pretty_print_compilation_unit(&decorator(&pc_to_cost), &program, &flows, &symbol_table);
        println!("{}", s);
        // dbg!(cost, pc_to_cost, cache);
    }

    #[test]
    fn md2u_single_while_with_uncovered_statement() {
        let path = "./examples/reachability/while.oox";
        let (mut coverage, program, flows, symbol_table) = setup(path);

        // Except for 12 (i := i + 1)
        coverage.remove(&12);

        let mut cache = Cache::new();
        let (cost, pc_to_cost) = min_distance_to_uncovered_method(
            MethodIdentifier {
                method_name: "main",
                decl_name: "Main",
                arg_list: vec![RuntimeType::IntRuntimeType; 1],
            },
            &coverage,
            &program,
            &flows,
            &symbol_table,
            &mut cache,
        );

        // dbg!(&program, &flows);

        #[rustfmt::skip]
        let expected_result = HashMap::from([
            (0, Distance { distance_type: DistanceType::ToFirstUncovered, value: 6 }),
            (2, Distance { distance_type: DistanceType::ToFirstUncovered, value: 5 }),
            (5, Distance { distance_type: DistanceType::ToFirstUncovered, value: 4 }),
            (8, Distance { distance_type: DistanceType::ToFirstUncovered, value: 3 }),
            (10, Distance { distance_type: DistanceType::ToFirstUncovered, value: 2 }),
            (12, Distance { distance_type: DistanceType::ToFirstUncovered, value: 1 }),
            (15, Distance { distance_type: DistanceType::ToEndOfMethod, value: 3 }),
            (17, Distance { distance_type: DistanceType::ToEndOfMethod, value: 2 }),
            (18, Distance { distance_type: DistanceType::ToEndOfMethod, value: 1 }),
        ]);

        assert_eq!(pc_to_cost, expected_result);

        // dbg!(cost, pc_to_cost, cache);
    }

    #[test]
    fn md2u_recursive_normal() {
        let path = "./examples/reachability/recursive.oox";
        let (coverage, program, flows, symbol_table) = setup(path);
        let method = MethodIdentifier {
            method_name: "main",
            decl_name: "Main",
            arg_list: vec![RuntimeType::IntRuntimeType; 1],
        };
        let mut cache = Cache::new();
        let (cost, pc_to_cost) = min_distance_to_uncovered_method(
            method.clone(),
            &coverage,
            &program,
            &flows,
            &symbol_table,
            &mut cache,
        );

        #[rustfmt::skip]
        let expected_result = HashMap::from([
            (0,  Distance { distance_type: DistanceType::ToEndOfMethod, value: 11 }),
            (2,  Distance { distance_type: DistanceType::ToEndOfMethod, value: 10 }),
            (5,  Distance { distance_type: DistanceType::ToEndOfMethod, value: 9 }),
            (8,  Distance { distance_type: DistanceType::ToEndOfMethod, value: 8 }),
            (10, Distance { distance_type: DistanceType::ToEndOfMethod, value: 2 }),
            (11, Distance { distance_type: DistanceType::ToEndOfMethod, value: 1 }),
            (12, Distance { distance_type: DistanceType::ToEndOfMethod, value: 5 }),
            (13, Distance { distance_type: DistanceType::ToEndOfMethod, value: 4 }),
            (15, Distance { distance_type: DistanceType::ToEndOfMethod, value: 10 }),
            (18, Distance { distance_type: DistanceType::ToEndOfMethod, value: 9 }),
            (21, Distance { distance_type: DistanceType::ToEndOfMethod, value: 8 }),
            (23, Distance { distance_type: DistanceType::ToEndOfMethod, value: 2 }),
            (25, Distance { distance_type: DistanceType::ToEndOfMethod, value: 3 }),
            (27, Distance { distance_type: DistanceType::ToEndOfMethod, value: 2 }),
            (28, Distance { distance_type: DistanceType::ToEndOfMethod, value: 1 }),
        ]);

        assert_eq!(pc_to_cost, expected_result);

        // dbg!(cost, pc_to_cost, cache);
    }

    #[test]
    fn md2u_recursive_with_uncovered_statements() {
        let path = "./examples/reachability/recursive.oox";
        let (mut coverage, program, flows, symbol_table) = setup(path);

        // int whatboutme;
        // int otherwise;
        // are both set to uncovered:
        coverage.remove(&23);
        coverage.remove(&27);

        let mut cache = Cache::new();
        let entry_method = MethodIdentifier {
            method_name: "main",
            decl_name: "Main",
            arg_list: vec![RuntimeType::IntRuntimeType; 1],
        };

        let (cost, pc_to_cost) = min_distance_to_uncovered_method(
            entry_method.clone(),
            &coverage,
            &program,
            &flows,
            &symbol_table,
            &mut cache,
        );
        // dbg!(&program);

        #[rustfmt::skip]
        let expected_result = HashMap::from([
            (0,  Distance { distance_type: DistanceType::ToFirstUncovered, value: 8 }),
            (2,  Distance { distance_type: DistanceType::ToFirstUncovered, value: 7 }),
            (5,  Distance { distance_type: DistanceType::ToFirstUncovered, value: 6 }),
            (8,  Distance { distance_type: DistanceType::ToFirstUncovered, value: 5 }),
            (10, Distance { distance_type: DistanceType::ToEndOfMethod, value: 2 }),
            (11, Distance { distance_type: DistanceType::ToEndOfMethod, value: 1 }),
            (12, Distance { distance_type: DistanceType::ToFirstUncovered, value: 4 }),
            (13, Distance { distance_type: DistanceType::ToFirstUncovered, value: 3 }),
            (15, Distance { distance_type: DistanceType::ToFirstUncovered, value: 8 }),
            (18, Distance { distance_type: DistanceType::ToFirstUncovered, value: 7 }),
            (21, Distance { distance_type: DistanceType::ToFirstUncovered, value: 6 }),
            (23, Distance { distance_type: DistanceType::ToFirstUncovered, value: 1 }),
            (25, Distance { distance_type: DistanceType::ToFirstUncovered, value: 2 }),
            (27, Distance { distance_type: DistanceType::ToFirstUncovered, value: 1 }),
            (28, Distance { distance_type: DistanceType::ToEndOfMethod, value: 1 }),
        ]);

        for k in pc_to_cost.keys() {
            assert_eq!(pc_to_cost[k], expected_result[k], "at pc {}", *k);
        }
        assert_eq!(pc_to_cost, expected_result);

        // Pretty print to confirm
        // let s = pretty_print_compilation_unit(&decorator(&pc_to_cost), &program, &flows, &symbol_table);
        // println!("{}", s);

        // dbg!(cost, pc_to_cost, cache);
    }

    #[test]
    fn md2u_recursive3() {
        let path = "./examples/reachability/recursive2.oox";
        let (mut coverage, program, flows, symbol_table) = setup(path);

        let mut cache = Cache::new();
        let entry_method = MethodIdentifier {
            method_name: "main",
            decl_name: "Main",
            arg_list: vec![RuntimeType::IntRuntimeType; 1],
        };

        let (cost, pc_to_cost) = min_distance_to_uncovered_method(
            entry_method.clone(),
            &coverage,
            &program,
            &flows,
            &symbol_table,
            &mut cache,
        );

        #[rustfmt::skip]
        let expected_result = HashMap::from([
            (0, Distance { distance_type: DistanceType::ToEndOfMethod, value: 19 }),
            (2, Distance { distance_type: DistanceType::ToEndOfMethod, value: 18 }),
            (5, Distance { distance_type: DistanceType::ToEndOfMethod, value: 17 }),
            (8, Distance { distance_type: DistanceType::ToEndOfMethod, value: 16 }),
            (10, Distance { distance_type: DistanceType::ToEndOfMethod, value: 2 }),
            (11, Distance { distance_type: DistanceType::ToEndOfMethod, value: 1 }),
            (12, Distance { distance_type: DistanceType::ToEndOfMethod, value: 13 }),
            (13, Distance { distance_type: DistanceType::ToEndOfMethod, value: 12 }),
            (15, Distance { distance_type: DistanceType::ToEndOfMethod, value: 13 }),
            (18, Distance { distance_type: DistanceType::ToEndOfMethod, value: 12 }),
            (21, Distance { distance_type: DistanceType::ToEndOfMethod, value: 11 }),
            (23, Distance { distance_type: DistanceType::ToEndOfMethod, value: 2 }),
            (25, Distance { distance_type: DistanceType::ToEndOfMethod, value: 11 }),
            (28, Distance { distance_type: DistanceType::ToEndOfMethod, value: 10 }),
            (31, Distance { distance_type: DistanceType::ToEndOfMethod, value: 9 }),
            (34, Distance { distance_type: DistanceType::ToEndOfMethod, value: 8 }),
            (37, Distance { distance_type: DistanceType::ToEndOfMethod, value: 7 }),
            (40, Distance { distance_type: DistanceType::ToEndOfMethod, value: 6 }),
            (43, Distance { distance_type: DistanceType::ToEndOfMethod, value: 5 }),
            (46, Distance { distance_type: DistanceType::ToEndOfMethod, value: 4 }),
            (49, Distance { distance_type: DistanceType::ToEndOfMethod, value: 3 }),
            (51, Distance { distance_type: DistanceType::ToEndOfMethod, value: 2 }),
            (52, Distance { distance_type: DistanceType::ToEndOfMethod, value: 1 }),
            (53, Distance { distance_type: DistanceType::ToEndOfMethod, value: 8 }),
            (54, Distance { distance_type: DistanceType::ToEndOfMethod, value: 7 }),
            (56, Distance { distance_type: DistanceType::ToEndOfMethod, value: 16 }),
            (58, Distance { distance_type: DistanceType::ToEndOfMethod, value: 15 }),
            (60, Distance { distance_type: DistanceType::ToEndOfMethod, value: 6 }),
            (63, Distance { distance_type: DistanceType::ToEndOfMethod, value: 5 }),
            (66, Distance { distance_type: DistanceType::ToEndOfMethod, value: 4 }),
            (69, Distance { distance_type: DistanceType::ToEndOfMethod, value: 3 }),
            (71, Distance { distance_type: DistanceType::ToEndOfMethod, value: 2 }),
            (72, Distance { distance_type: DistanceType::ToEndOfMethod, value: 1 }),
        ]);

        for k in pc_to_cost.keys() {
            assert_eq!(pc_to_cost[k], expected_result[k], "at pc {}", *k);
        }
        assert_eq!(pc_to_cost, expected_result);

        // let s = pretty_print_compilation_unit(&decorator(&pc_to_cost), &program, &flows, &symbol_table);
        // println!("{}", s);

        // dbg!(cost, pc_to_cost, cache);
    }

    #[test]
    fn md2u_nested_while() {
        let path = "./examples/reachability/nested_while.oox";
        let (coverage, program, flows, symbol_table) = setup(path);

        let mut cache = Cache::new();
        let (cost, pc_to_cost) = min_distance_to_uncovered_method(
            MethodIdentifier {
                method_name: "main",
                decl_name: "Main",
                arg_list: vec![RuntimeType::IntRuntimeType; 1],
            },
            &coverage,
            &program,
            &flows,
            &symbol_table,
            &mut cache,
        );

        // dbg!(cost, &pc_to_cost, cache);

        #[rustfmt::skip]
        let expected_result = HashMap::from([
            (0,  Distance { distance_type: DistanceType::ToEndOfMethod, value: 7 }),
            (2,  Distance { distance_type: DistanceType::ToEndOfMethod, value: 6 }),
            (5,  Distance { distance_type: DistanceType::ToEndOfMethod, value: 5 }),
            (8,  Distance { distance_type: DistanceType::ToEndOfMethod, value: 4 }),
            (10, Distance { distance_type: DistanceType::ToEndOfMethod, value: 10 }),
            (13, Distance { distance_type: DistanceType::ToEndOfMethod, value: 9 }),
            (16, Distance { distance_type: DistanceType::ToEndOfMethod, value: 8 }),
            (19, Distance { distance_type: DistanceType::ToEndOfMethod, value: 7 }),
            (22, Distance { distance_type: DistanceType::ToEndOfMethod, value: 6 }),
            (24, Distance { distance_type: DistanceType::ToEndOfMethod, value: 8 }),
            (26, Distance { distance_type: DistanceType::ToEndOfMethod, value: 7 }),
            (28, Distance { distance_type: DistanceType::ToEndOfMethod, value: 5 }),
            (31, Distance { distance_type: DistanceType::ToEndOfMethod, value: 3 }),
            (33, Distance { distance_type: DistanceType::ToEndOfMethod, value: 2 }),
            (34, Distance { distance_type: DistanceType::ToEndOfMethod, value: 1 }),
        ]);

        // let s = pretty_print_compilation_unit(&decorator(&pc_to_cost), &program, &flows, &symbol_table);
        // println!("{}", s);

        assert_eq!(pc_to_cost, expected_result);
    }

    #[test]
    fn md2u_recursive4() {
        let path = "./examples/reachability/recursive4.oox";
        let (mut coverage, program, flows, symbol_table) = setup(path);

        // set to uncovered:
        coverage.remove(&73);

        let s = pretty_print_compilation_unit(
            &|pc: u64| Some(format!("pc: {}", pc)),
            &program,
            &flows,
            &symbol_table,
        );
        println!("{}", s);

        let mut cache = Cache::new();
        let entry_method = MethodIdentifier {
            method_name: "main",
            decl_name: "Node",
            arg_list: vec![
                RuntimeType::ReferenceRuntimeType {
                    type_: "Node".into(),
                },
                RuntimeType::IntRuntimeType,
            ],
        };

        let (cost, pc_to_cost) = min_distance_to_uncovered_method(
            entry_method.clone(),
            &coverage,
            &program,
            &flows,
            &symbol_table,
            &mut cache,
        );

        let s =
            pretty_print_compilation_unit(&decorator(&pc_to_cost), &program, &flows, &symbol_table);
        println!("{}", s);

        dbg!(&cache);
    }

    #[test]
    fn md2u_recursive_while() {
        let path = "./examples/reachability/recursive_while.oox";
        let (mut coverage, program, flows, symbol_table) = setup(path);

        coverage.remove(&23);

        let s = pretty_print_compilation_unit(
            &|pc: u64| Some(format!("pc: {}", pc)),
            &program,
            &flows,
            &symbol_table,
        );
        println!("{}", s);

        let mut cache = Cache::new();
        let entry_method = MethodIdentifier {
            method_name: "main",
            decl_name: "Main",
            arg_list: vec![RuntimeType::IntRuntimeType],
        };

        let (cost, pc_to_cost) = min_distance_to_uncovered_method(
            entry_method.clone(),
            &coverage,
            &program,
            &flows,
            &symbol_table,
            &mut cache,
        );

        let s =
            pretty_print_compilation_unit(&decorator(&pc_to_cost), &program, &flows, &symbol_table);
        println!("{}", s);

        dbg!(&cache);
    }
}
