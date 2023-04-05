use std::{collections::{HashMap, HashSet}, thread::current};

use crate::{
    cfg::CFGStatement, exec::find_entry_for_static_invocation, symbol_table::SymbolTable,
    Invocation, Rhs, RuntimeType, Statement,
};

use super::{Cost, ProgramCounter};

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
struct MethodIdentifier<'a> {
    method_name: &'a str,
    decl_name: &'a str,
    arg_list: Vec<RuntimeType>,
}

/// A method always has the same cost, with a distinction made between a cost achieved by finding an uncovered statement,
/// and otherwise a cost of calling the function in terms of the number of statements visited.
type Cache<'a> = HashMap<MethodIdentifier<'a>, CumulativeCost>;

/// calling a method will explore a certain number of statements before returning
/// If an uncovered statement is encountered, it will have an exact cost
/// Otherwise it returns the minimal cost of the method call in terms of the number of statements explored.
#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Copy, Clone)]
enum CumulativeCost {
    // Cost to uncovered statement
    Strict(Cost),
    // Minimal cost for calling this method.
    AtLeast(Cost),
    // Cycles back to program point, with additional cost.
    Cycle(ProgramCounter, Cost)
}

// Either<CostToUncoveredStatement, MinimalMethodCost>

impl CumulativeCost {
    fn increased_by_one(self) -> CumulativeCost {
        self.plus(1)
    }

    fn plus(self, cost: Cost) -> CumulativeCost {
        match self {
            Self::Strict(c) => Self::Strict(c + cost),
            Self::AtLeast(c) => Self::AtLeast(c + cost),
            Self::Cycle(pc, c) => Self::Cycle(pc, c + cost)
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
    st: &'a SymbolTable,
    visited: &mut HashSet<ProgramCounter>
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

    let method_body_cost = min_distance_to_statement(pc, &method, coverage, program, flow, st, &mut pc_to_cost, &mut cache, visited);

    cache.insert(method, method_body_cost);

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
    st: &'a SymbolTable,
    pc_to_cost: &mut HashMap<ProgramCounter, CumulativeCost>,
    cache: &mut Cache<'a>,
    visited: &mut HashSet<ProgramCounter>,
) -> CumulativeCost {
    let statement = &program[&pc];
    dbg!(statement);
    visited.insert(pc);

    if pc_to_cost.contains_key(&pc) {
        return pc_to_cost[&pc];
    }

    if let CFGStatement::FunctionExit { .. } = statement {
        // We have reached the end of the method
        let cost = if !coverage.contains_key(&pc) {
            // Uncovered statement, has strict 1 cost
            CumulativeCost::Strict(1)
        } else {
            CumulativeCost::AtLeast(1)
        };
        pc_to_cost.insert(pc, cost);
        return cost;
    }

    // Find the cost of the current statement
    let cost_of_this_statement = statement_cost(pc, method, coverage, program, flow, st, pc_to_cost, cache, visited);

    match cost_of_this_statement {
        CumulativeCost::Strict(_) => {
            // We can short-circuit back since an uncovered statement was encountered.
            pc_to_cost.insert(pc, cost_of_this_statement);
            return cost_of_this_statement;
        }
        CumulativeCost::AtLeast(cost) => {
            // Otherwise we have to check the remainder of the current method.

            let next_pcs = &flow[&pc];

            let cost = match &next_pcs[..] {
                [] => unreachable!(),
                multiple => {
                    // next cost is the minimum cost of following methods.
                    let next_cost = multiple
                        .iter()
                        .map(|next_pc| {
                            if visited.contains(next_pc) {
                                // Cycle detected (while loop or recursive function)
                                // We set this to be infinitely large
                                CumulativeCost::Cycle(*next_pc, 0)
                            } else {
                                min_distance_to_statement(
                                    *next_pc, &method, coverage, program, flow, st, pc_to_cost, cache, visited
                                )
                            }
                        })
                        .min()
                        .expect("multiple pcs");

                    next_cost.plus(cost)
                }
            };


            // if this is a while statement, check all cycles and fix them
            if let CFGStatement::While(_, _) = &statement {
                fix_cycles(pc, cost, pc_to_cost);
            }

            pc_to_cost.insert(pc, cost);
            return cost;
        }
        CumulativeCost::Cycle(_, _) => return cost_of_this_statement
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
    };

    for (k, cost) in to_repair {
        pc_to_cost.insert(k, resulting_cost.plus(cost));
    }
}


/// Returns the cost of exploring the statement
/// Can be either strictly in case of a found uncovered statement, or at least cost otherwise.
fn statement_cost<'a>(
    pc: ProgramCounter,
    current_method: &MethodIdentifier<'a>,
    coverage: &HashMap<ProgramCounter, usize>,
    program: &'a HashMap<ProgramCounter, CFGStatement>,
    flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
    st: &'a SymbolTable,
    pc_to_cost: &mut HashMap<ProgramCounter, CumulativeCost>,
    cache: &mut Cache<'a>,
    visited: &mut HashSet<ProgramCounter>
) -> CumulativeCost {
    let statement = &program[&pc];

    if !coverage.contains_key(&pc) {
        // Uncovered statement, has strict 1 cost
        CumulativeCost::Strict(1)
    } else if let Some(invocation) = is_method_invocation(statement) {
        // Case for a statement with an invocation.
        // An invocation has more cost than a regular statement, the resulting cost is returned.
        // If an unseen before method invocation is encountered, it will explore that first, and will add the results to the cache.
        let methods_called = methods_called(invocation);

        // Of all possible resolved methods, find the minimal cost to uncovered, or minimal cost to traverse.
        let min_method_cost = methods_called
            .into_iter()
            .map(|method|{
                // Check cache or compute cost for method
                // if method == current_method {
                //     // Recursiveness detected, have to quit.
                // }

                let cost = if let Some(cost) = cache.get(&method) {
                    *cost
                } else {
                    let (cost, method_pc_to_cost, method_cache) =
                        min_distance_to_uncovered_method(method, coverage, program, flow, st, visited);

                        // would actually like to catch it here already hmm
                    pc_to_cost.extend(method_pc_to_cost);
                    cache.extend(method_cache);
                    cost
                };
                cost
            })
            .min()
            .expect("at least one resolved method");

        min_method_cost.increased_by_one()
    } else {
        // A normal statement has at least cost 1, to be added to remainder
        CumulativeCost::AtLeast(1)
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
    use crate::{parse_program, typing::type_compilation_unit, cfg::labelled_statements, utils};

    use super::*;

    #[test]
    fn md2u_single_while() {
        
        let path = "./examples/psv/test.oox";
        let file_content = std::fs::read_to_string(path).unwrap();

        let mut coverage = HashMap::new();
        let c = parse_program(&file_content, true).unwrap();

        let symbol_table = SymbolTable::from_ast(&c).unwrap();
        let c = type_compilation_unit(c, &symbol_table).unwrap();

        let (result, flw) = labelled_statements(c);

        let program: HashMap<u64, CFGStatement> = result.into_iter().collect();

        // Simulate that the method has been explored.
        coverage.extend(program.keys().map(|k| (*k, 1usize)));
        // Except for 12 (i := i + 1)
        // coverage.remove(&12);

        // dbg!(&program);

        let flows: HashMap<u64, Vec<u64>> = utils::group_by(flw.into_iter());

        let mut visited = HashSet::new();

        let (cost, pc_to_cost, cache) = min_distance_to_uncovered_method(MethodIdentifier { method_name: "main", decl_name: "Main", arg_list: vec![RuntimeType::IntRuntimeType; 1] }, &coverage, &program, &flows, &symbol_table, &mut visited);

        dbg!(cost, pc_to_cost, cache);
    }


    #[test]
    fn md2u_recursive() {
        
        let path = "./examples/psv/test.oox";
        let file_content = std::fs::read_to_string(path).unwrap();

        let mut coverage = HashMap::new();
        let c = parse_program(&file_content, false).unwrap();

        let symbol_table = SymbolTable::from_ast(&c).unwrap();
        let c = type_compilation_unit(c, &symbol_table).unwrap();

        let (result, flw) = labelled_statements(c);

        let program: HashMap<u64, CFGStatement> = result.into_iter().collect();

        // Simulate that the method has been explored.
        coverage.extend(program.keys().map(|k| (*k, 1usize)));
        // Except for 12 (i := i + 1)
        // coverage.remove(&12);

        dbg!(&program);

        let flows: HashMap<u64, Vec<u64>> = utils::group_by(flw.into_iter());

        let mut visited = HashSet::new();

        let (cost, pc_to_cost, cache) = min_distance_to_uncovered_method(MethodIdentifier { method_name: "main2", decl_name: "Main", arg_list: vec![RuntimeType::IntRuntimeType; 1] }, &coverage, &program, &flows, &symbol_table, &mut visited);

        dbg!(cost, pc_to_cost, cache);
    }

    #[test]
    fn md2u_nested_while() {
        
        let path = "./examples/psv/test.oox";
        let file_content = std::fs::read_to_string(path).unwrap();

        let mut coverage = HashMap::new();
        let c = parse_program(&file_content, true).unwrap();

        let symbol_table = SymbolTable::from_ast(&c).unwrap();
        let c = type_compilation_unit(c, &symbol_table).unwrap();

        let (result, flw) = labelled_statements(c);

        let program: HashMap<u64, CFGStatement> = result.into_iter().collect();

        // Simulate that the method has been explored.
        coverage.extend(program.keys().map(|k| (*k, 1usize)));
        // Except for 12 (i := i + 1)
        // coverage.remove(&12);

        dbg!(&program);

        let flows: HashMap<u64, Vec<u64>> = utils::group_by(flw.into_iter());

        let mut visited = HashSet::new();

        let (cost, pc_to_cost, cache) = min_distance_to_uncovered_method(MethodIdentifier { method_name: "main3", decl_name: "Main", arg_list: vec![RuntimeType::IntRuntimeType; 1] }, &coverage, &program, &flows, &symbol_table, &mut visited);

        dbg!(cost, pc_to_cost, cache);
    }
}