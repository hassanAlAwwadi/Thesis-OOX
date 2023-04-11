use std::collections::{HashMap, HashSet};

use crate::{
    cfg::{CFGStatement, MethodIdentifier},
    exec::find_entry_for_static_invocation,
    symbol_table::SymbolTable,
    Invocation, Rhs, RuntimeType, Statement,
};

use super::{Cost, ProgramCounter};

/// A method always has the same cost, with a distinction made between a cost achieved by finding an uncovered statement,
/// and otherwise a cost of calling the function in terms of the number of statements visited.
type Cache<'a> = HashMap<MethodIdentifier<'a>, Distance>;

/// Type of distance of a statement, can be either partially complete (to as far as it can see), which would be the exit of the method.
/// Or it can be the distance to the first uncovered statement, if any found.
#[derive(Debug, Hash, Eq, PartialEq, Clone, PartialOrd, Ord, Copy)]
enum DistanceType {
    ToFirstUncovered,
    ToEndOfMethod,
}

#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Clone, Copy)]
struct Distance {
    distance_type: DistanceType,
    value: u64,
}

impl Distance {
    fn plus(mut self, cost: Cost) -> Distance {
        self.value += cost;
        self
    }
}

/// calling a method will explore a certain number of statements before returning
/// If an uncovered statement is encountered, it will have an exact cost
/// Otherwise it returns the minimal cost of the method call in terms of the number of statements explored.
#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Clone)]
enum CumulativeCost {
    Cost(Distance),
    // Cycles back to program point, with additional cost.
    Cycle(ProgramCounter, Cost),
    Added(Box<CumulativeCost>, Box<CumulativeCost>),
    // In case of recursion, we can not resolve it immediately and need to keep track of it.
    UnexploredMethodCall(String),
}

// Either<CostToUncoveredStatement, MinimalMethodCost>

impl CumulativeCost {
    fn increased_by_one(self) -> CumulativeCost {
        self.plus(1)
    }

    fn plus(self, cost: Cost) -> CumulativeCost {
        match self {
            Self::Cost(d) => Self::Cost(d.plus(cost)),
            Self::Cycle(pc, c) => Self::Cycle(pc, c + cost),
            Self::Added(c1, c2) => Self::Added(c1, Box::new(c2.plus(cost))),
            Self::UnexploredMethodCall(_) => Self::Added(
                Box::new(self),
                Box::new(Self::Cost(Distance {
                    value: cost,
                    distance_type: DistanceType::ToEndOfMethod,
                })),
            ),
        }
    }
}

/// Computes the minimal distance to uncovered methods for all program counters in this method
/// Recursively computes the minimal distance for any method calls referenced.
fn min_distance_to_uncovered_method<'a>(
    method: MethodIdentifier<'a>,
    coverage: &HashMap<ProgramCounter, usize>,
    program: &'a HashMap<ProgramCounter, CFGStatement>,
    flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
    st: &SymbolTable,
    visited: &mut HashSet<ProgramCounter>,
) -> (Distance, HashMap<ProgramCounter, Distance>, Cache<'a>) {
    let (cost, pc_to_cost, cache) =
        min_distance_to_uncovered_method_helper(method, coverage, program, flow, st, visited);

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

    (distance, pc_to_distance, cache)
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
) -> (
    CumulativeCost,
    HashMap<ProgramCounter, CumulativeCost>,
    Cache<'a>,
) {
    let pc = find_entry_for_static_invocation(
        method.decl_name,
        method.method_name,
        method.arg_list.iter().cloned(),
        program,
        st,
    );
    let mut pc_to_cost = HashMap::new();
    let mut cache = Cache::new();

    let method_body_cost = min_distance_to_statement(
        pc,
        &method,
        coverage,
        program,
        flow,
        st,
        &mut pc_to_cost,
        &mut cache,
        visited,
    );

    let d = match method_body_cost {
        CumulativeCost::Cost(d) => d,
        _ => panic!(),
    };
    dbg!(&pc_to_cost);

    cleanup_pc_to_cost(&method.method_name, &mut pc_to_cost, d);

    cache.insert(method, d);

    (method_body_cost, pc_to_cost, cache)
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
    let statement = &program[&pc];
    dbg!(statement);
    visited.insert(pc);

    if pc_to_cost.contains_key(&pc) {
        return pc_to_cost[&pc].clone();
    }

    if let CFGStatement::FunctionExit { .. } = statement {
        // We have reached the end of the method
        let distance = if !coverage.contains_key(&pc) {
            // Uncovered statement, has strict 1 cost
            Distance {
                value: 1,
                distance_type: DistanceType::ToFirstUncovered,
            }
        } else {
            Distance {
                value: 1,
                distance_type: DistanceType::ToEndOfMethod,
            }
        };
        pc_to_cost.insert(pc, CumulativeCost::Cost(distance));
        return CumulativeCost::Cost(distance);
    }

    let next_pcs = &flow[&pc];
    let remaining_cost = match &next_pcs[..] {
        [] => unreachable!(),
        multiple => {
            // next cost is the minimum cost of following methods.
            let next_cost = multiple
                .iter()
                .map(|next_pc| {
                    if let CFGStatement::While(_, _) = &program[&next_pc] {
                        if visited.contains(next_pc) {
                            return CumulativeCost::Cycle(*next_pc, 0);
                        }
                    }
                    // Cycle detected (while loop or recursive function)

                    min_distance_to_statement(
                        *next_pc, &method, coverage, program, flow, st, pc_to_cost, cache, visited,
                    )
                })
                .min()
                .expect("multiple pcs");
            next_cost
        }
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
                if let CFGStatement::While(_, _) = &statement {
                    fix_cycles(pc, cost.clone(), pc_to_cost);
                }
                cost
            } else {
                // We can short-circuit back since an uncovered statement was encountered.
                cost_of_this_statement
            };
            pc_to_cost.insert(pc, cost.clone());
            return cost;
        }
        CumulativeCost::Cycle(_pc, _pluscost) => unimplemented!(),
        CumulativeCost::Added(_, _) => {
            let cost =
                CumulativeCost::Added(Box::new(cost_of_this_statement), Box::new(remaining_cost));

            pc_to_cost.insert(pc, cost.clone());
            return cost;
        }
        CumulativeCost::UnexploredMethodCall(_) => {
            let cost =
                CumulativeCost::Added(Box::new(cost_of_this_statement), Box::new(remaining_cost));
            pc_to_cost.insert(pc, cost.clone());
            return cost;
        }
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
            (
                key,
                replace_method_call_in_costs(method_name, value, resulting_cost),
            )
        })
        .collect();
}

fn replace_method_call_in_costs<'a>(
    method_name: &str,
    cost: CumulativeCost,
    resulting_cost: Distance,
) -> CumulativeCost {
    match cost {
        CumulativeCost::Added(c1, c2) => {
            let c1 = replace_method_call_in_costs(method_name, *c1, resulting_cost);
            let c2 = replace_method_call_in_costs(method_name, *c2, resulting_cost);
            match (c1, c2) {
                (CumulativeCost::Cost(d1), CumulativeCost::Cost(d2)) => {
                    CumulativeCost::Cost(Distance {
                        distance_type: std::cmp::min(d1.distance_type, d2.distance_type),
                        value: d1.value + d2.value,
                    })
                }
                (c1, c2) => todo!("{:?} {:?}", c1, c2),
            }
        }
        CumulativeCost::UnexploredMethodCall(method) if method_name == &method => {
            CumulativeCost::Cost(resulting_cost)
        }
        CumulativeCost::Cycle(_, _) => todo!(),
        cost => cost,
    }
}

fn fix_cycles(
    pc: ProgramCounter,
    resulting_cost: CumulativeCost,
    pc_to_cost: &mut HashMap<ProgramCounter, CumulativeCost>,
) {
    let mut to_repair = Vec::new();

    for (k, v) in pc_to_cost.iter() {
        if let CumulativeCost::Cycle(cycle_pc, cost) = v {
            if pc == *cycle_pc {
                to_repair.push((*k, *cost));
            }
        }
    }

    for (k, cost) in to_repair {
        pc_to_cost.insert(k, resulting_cost.clone().plus(cost));
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
    } else if let Some(invocation) = is_method_invocation(statement) {
        // Case for a statement with an invocation.
        // An invocation has more cost than a regular statement, the resulting cost is returned.
        // If an unseen before method invocation is encountered, it will explore that first, and will add the results to the cache.
        let methods_called = methods_called(invocation);

        // Of all possible resolved methods, find the minimal cost to uncovered, or minimal cost to traverse.
        let min_method_cost = methods_called
            .into_iter()
            .map(|method| {
                // Check cache or compute cost for method

                let cost = if let Some(cost) = cache.get(&method) {
                    CumulativeCost::Cost(cost.clone())
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
                        dbg!("oh oh recursion", next_pc);
                        CumulativeCost::UnexploredMethodCall(method.method_name.to_string())
                    } else {
                        let (cost, method_pc_to_cost, method_cache) =
                            min_distance_to_uncovered_method_helper(
                                method, coverage, program, flow, st, visited,
                            );

                        pc_to_cost.extend(method_pc_to_cost);
                        cache.extend(method_cache);
                        cost
                    }
                };
                cost.increased_by_one()
            })
            .min()
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

fn is_method_invocation(statement: &CFGStatement) -> Option<&Invocation> {
    match statement {
        CFGStatement::Statement(Statement::Call { invocation, .. })
        | CFGStatement::Statement(Statement::Assign {
            rhs: Rhs::RhsCall { invocation, .. },
            ..
        }) => Some(invocation),
        _ => None,
    }
}

/// Returns a list of methods that could be called at runtime depending on the runtimetype, by this invocation.
fn methods_called(invocation: &Invocation) -> Vec<MethodIdentifier> {
    match invocation {
        Invocation::InvokeMethod { resolved, .. } => {
            // A regular method can resolve to multiple different methods due to dynamic dispatch, depending on the runtime type of the object.
            // We make here the assumption that any object can be represented and thus consider each resolved method.

            // We also need to lookup the program counter for each method. (CANT WE DO THIS BEFOREHAND?)

            let methods = resolved.as_ref().unwrap();

            methods
                .values()
                .map(|(decl, method)| MethodIdentifier {
                    method_name: &method.name,
                    decl_name: decl.name(),
                    arg_list: method.param_types().collect(),
                })
                .collect()
        }
        Invocation::InvokeSuperMethod { resolved, .. }
        | Invocation::InvokeConstructor { resolved, .. }
        | Invocation::InvokeSuperConstructor { resolved, .. } => {
            // The case where we have a single method that we resolve to.
            let (decl, method) = resolved.as_ref().unwrap().as_ref();

            vec![MethodIdentifier {
                method_name: &method.name,
                decl_name: decl.name(),
                arg_list: method.param_types().collect(),
            }]
        }
    }
}

#[cfg(test)]
mod tests {
    use pretty::BoxAllocator;

    use crate::{
        cfg::labelled_statements, parse_program, prettyprint::cfg_pretty::pretty_print_cfg_method,
        typing::type_compilation_unit, utils,
    };

    use super::*;

    fn setup(
        path: &str,
    ) -> (
        HashMap<ProgramCounter, usize>,
        HashMap<ProgramCounter, CFGStatement>,
        HashMap<ProgramCounter, Vec<u64>>,
        SymbolTable,
        HashSet<u64>,
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

        let visited = HashSet::new();
        (coverage, program, flows, symbol_table, visited)
    }

    #[test]
    fn md2u_single_while() {
        let path = "./examples/reachability/while.oox";
        let (coverage, program, flows, symbol_table, mut visited) = setup(path);

        let (cost, pc_to_cost, cache) = min_distance_to_uncovered_method(
            MethodIdentifier {
                method_name: "main",
                decl_name: "Main",
                arg_list: vec![RuntimeType::IntRuntimeType; 1],
            },
            &coverage,
            &program,
            &flows,
            &symbol_table,
            &mut visited,
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

        dbg!(cost, pc_to_cost, cache);
    }

    #[test]
    fn md2u_single_while_with_uncovered_statement() {
        let path = "./examples/reachability/while.oox";
        let (mut coverage, program, flows, symbol_table, mut visited) = setup(path);

        // Except for 12 (i := i + 1)
        coverage.remove(&12);

        let (cost, pc_to_cost, cache) = min_distance_to_uncovered_method(
            MethodIdentifier {
                method_name: "main",
                decl_name: "Main",
                arg_list: vec![RuntimeType::IntRuntimeType; 1],
            },
            &coverage,
            &program,
            &flows,
            &symbol_table,
            &mut visited,
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

        dbg!(cost, pc_to_cost, cache);
    }

    #[test]
    fn md2u_recursive_normal() {
        let path = "./examples/reachability/recursive.oox";
        let (coverage, program, flows, symbol_table, mut visited) = setup(path);
        let method = MethodIdentifier {
            method_name: "main",
            decl_name: "Main",
            arg_list: vec![RuntimeType::IntRuntimeType; 1],
        };
        let (cost, pc_to_cost, cache) = min_distance_to_uncovered_method(
            method.clone(),
            &coverage,
            &program,
            &flows,
            &symbol_table,
            &mut visited,
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
        

        let pc = find_entry_for_static_invocation(
            method.decl_name,
            "f_recursive",
            vec![RuntimeType::IntRuntimeType; 2].into_iter(),
            &program,
            &symbol_table,
        );

        assert_eq!(pc_to_cost, expected_result);

        // dbg!(cost, pc_to_cost, cache);
    }

    #[test]
    fn md2u_recursive_with_uncovered_statements() {
        let path = "./examples/reachability/recursive.oox";
        let (mut coverage, program, flows, symbol_table, mut visited) = setup(path);

        // int whatboutme;
        // int otherwise;
        // are both set to uncovered:
        coverage.remove(&23);
        coverage.remove(&27);

        let entry_method = MethodIdentifier {
            method_name: "main",
            decl_name: "Main",
            arg_list: vec![RuntimeType::IntRuntimeType; 1],
        };

        let f_recursive = MethodIdentifier {
            method_name: "f_recursive",
            decl_name: "Main",
            arg_list: vec![RuntimeType::IntRuntimeType; 2],
        };

        let (cost, pc_to_cost, cache) = min_distance_to_uncovered_method(
            entry_method.clone(),
            &coverage,
            &program,
            &flows,
            &symbol_table,
            &mut visited,
        );

        let s = pretty_print_cfg_method(
            entry_method,
            &|pc| Some(format!("{}", pc)),
            &program,
            &flows,
            &symbol_table,
        );

        println!("{}", s);

        let s = pretty_print_cfg_method(
            f_recursive,
            &|pc| Some(format!("{}", pc)),
            &program,
            &flows,
            &symbol_table,
        );

        println!("{}", s);

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

        dbg!(cost, pc_to_cost, cache);
    }

    #[test]
    fn md2u_nested_while() {
        let path = "./examples/reachability/nested_while.oox";
        let (coverage, program, flows, symbol_table, mut visited) = setup(path);

        let (cost, pc_to_cost, cache) = min_distance_to_uncovered_method(
            MethodIdentifier {
                method_name: "main",
                decl_name: "Main",
                arg_list: vec![RuntimeType::IntRuntimeType; 1],
            },
            &coverage,
            &program,
            &flows,
            &symbol_table,
            &mut visited,
        );

        dbg!(cost, &pc_to_cost, cache);

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
        

        assert_eq!(pc_to_cost, expected_result);
    }
}
