use core::panic;
use std::{
    array,
    cell::RefCell,
    collections::{HashMap, HashSet},
    ops::{AddAssign, Deref},
    rc::Rc,
    string,
    sync::Mutex,
};

use itertools::{Either, Itertools};
use num::One;
use ordered_float::NotNan;
use slog::{debug, info, log, o, Drain, Level, Logger, Value};
use slog::{Key, Record, Result, Serializer};
use sloggers::{
    terminal::{Destination, TerminalLoggerBuilder},
    types::Severity,
    Build,
};
use z3::SatResult;

mod invocation;

use crate::{
    cfg::{labelled_statements, CFGStatement},
    concretization::{concretizations, find_symbolic_refs},
    dsl::{equal, ite, negate, or, toIntExpr},
    eval::{self, evaluate, evaluateAsInt},
    exception_handler::{ExceptionHandlerEntry, ExceptionHandlerStack},
    exec::invocation::{non_static_resolved_method_invocation, single_method_invocation},
    lexer::tokens,
    parser::{insert_exceptional_clauses, parse},
    stack::{lookup_in_stack, write_to_stack, StackFrame},
    symbolic_table::SymbolicTable,
    syntax::{
        BinOp, CompilationUnit, Declaration, DeclarationMember, Expression, Identifier, Invocation,
        Lhs, Lit, NonVoidType, Parameter, Reference, Rhs, RuntimeType, Statement, UnOp,
    },
    typeable::{runtime_to_nonvoidtype, Typeable},
    utils, z3_checker,
};

const NULL: Expression = Expression::Lit {
    lit: Lit::NullLit,
    type_: RuntimeType::ANYRuntimeType,
};

fn retval() -> String {
    "retval".to_string()
}

pub type Heap = HashMap<Reference, HeapValue>;

pub fn get_element(index: usize, ref_: Reference, heap: &Heap) -> Rc<Expression> {
    if let HeapValue::ArrayValue { elements, .. } = &heap[&ref_] {
        return elements[index].clone();
    }
    panic!("Expected an array");
}

#[derive(Clone, Debug)]
pub enum HeapValue {
    ObjectValue {
        fields: HashMap<Identifier, Rc<Expression>>,
        type_: RuntimeType,
    },
    ArrayValue {
        elements: Vec<Rc<Expression>>,
        type_: RuntimeType,
    },
}

impl HeapValue {
    fn empty_object() -> HeapValue {
        HeapValue::ObjectValue {
            fields: HashMap::new(),
            type_: RuntimeType::ANYRuntimeType,
        }
    }
}

type PathConstraints = HashSet<Expression>;

// refactor to Vec<Reference>? neins, since it can also be ITE and stuff, can it though?
// nope it can't, refactor this!
pub type AliasMap = HashMap<String, AliasEntry>;

#[derive(Debug, Clone)]
pub struct AliasEntry {
    pub aliases: Vec<Rc<Expression>>,
    uniform_type: bool, // whether all aliases have the same type, or subclasses appear.
}

impl AliasEntry {
    // pub fn aliases(&self) -> impl Iterator<Item=&Rc<Expression>> + Clone {
    //     self.aliases.iter()
    // }

    pub fn new(aliases: Vec<Rc<Expression>>) -> AliasEntry {
        let uniform_type = aliases
            .iter()
            .map(AsRef::as_ref)
            .filter(|e| **e != Expression::NULL)
            .map(Typeable::type_of)
            .all_equal();

        AliasEntry {
            aliases,
            uniform_type: uniform_type,
        }
    }

    pub fn aliases(&self) -> &Vec<Rc<Expression>> {
        &self.aliases
    }

    /// Returns Some type if all alias types are equal, otherwise return None.
    fn uniform_type(&self) -> Option<RuntimeType> {
        if self.uniform_type {
            self.aliases
                .iter()
                .map(AsRef::as_ref)
                .filter(|e| **e != Expression::NULL)
                .next()
                .map(Typeable::type_of)
        } else {
            None
        }
    }

    fn remove_null(&mut self, var: &str) {
        self.aliases.retain(|x| match x.as_ref() {
            Expression::Lit {
                lit: Lit::NullLit, ..
            } => false,
            _ => true,
        });
    }
}

enum Output {
    Valid,
    Invalid,
    Unknown,
}

/// A type to provide fresh id values (numerical).
/// Useful for generating new ids (addresses) for heap values
/// or generating new path ids when paths split.
#[derive(Debug, Clone)]
pub struct IdCounter<T> {
    last_value: T,
}

impl<T> IdCounter<T>
where
    T: AddAssign + One + Clone,
{
    fn new(initial: T) -> IdCounter<T> {
        IdCounter {
            last_value: initial,
        }
    }

    fn next_id(&mut self) -> T {
        self.last_value += T::one();
        self.last_value.clone()
    }
}

// perhaps separate program from this structure, such that we can have multiple references to it.
#[derive(Clone)]
pub struct State {
    pc: u64,
    pub stack: Vec<StackFrame>,
    pub heap: Heap,
    precondition: Expression,

    constraints: PathConstraints,
    pub alias_map: AliasMap,
    pub ref_counter: IdCounter<i64>,
    exception_handler: ExceptionHandlerStack,

    // logger and other (non-functional) metrics
    logger: Logger,
    path_length: u64,
    path_id: u64,
}

impl State {
    fn next_reference_id(&mut self) -> Reference {
        self.ref_counter.next_id()
    }

    /// Create a copy from this state, 'state splitting'
    /// path_id is for the new state to reflect that this is a new path.
    fn new_state(&self, path_counter: &mut IdCounter<u64>) -> State {
        let mut new_state = self.clone();
        new_state.path_id = path_counter.next_id();
        new_state
    }

    /// allocates structure on heap, returning a reference to the value.
    fn allocate_on_heap(&mut self, structure: HeapValue) -> Rc<Expression> {
        let ref_fresh = self.next_reference_id();
        let type_ = structure.type_of();

        self.heap.insert(ref_fresh, structure);
        return Rc::new(Expression::Ref {
            ref_: ref_fresh,
            type_,
        });
    }
}

#[derive(Debug, PartialEq, Eq)]
enum SymResult {
    Valid,
    Invalid,
}

/// The main function for the symbolic execution, any path splitting due to the control flow graph or array initialization happens here.
fn sym_exec(
    state: &mut State,
    program: &HashMap<u64, CFGStatement>,
    flows: &HashMap<u64, Vec<u64>>,
    k: u64,
    st: &SymbolicTable,
    root_logger: Logger,
    path_counter: Rc<RefCell<IdCounter<u64>>>,
) -> SymResult {
    if k == 0 {
        // finishing current branch
        //dbg!("FINITO");
        return SymResult::Valid;
    }
    let next = action(state, program, k, st);

    // //dbg!(&state.pc);

    match next {
        ActionResult::FunctionCall(next) => {
            // function call or return
            state.pc = next;
            let result = sym_exec(state, program, flows, k - 1, st, root_logger, path_counter);
            if result != SymResult::Valid {
                return result;
            }
        }
        ActionResult::Return(return_pc) => {
            if let Some(neighbours) = flows.get(&return_pc) {
                for neighbour_pc in neighbours {
                    let mut new_state = state.clone();
                    new_state.pc = *neighbour_pc;

                    let result = sym_exec(
                        &mut new_state,
                        program,
                        flows,
                        k - 1,
                        st,
                        root_logger.clone(),
                        path_counter.clone(),
                    );
                    if result != SymResult::Valid {
                        return result;
                    }
                }
            } else {
                panic!("function pc does not exist");
            }
        }
        ActionResult::Continue => {
            if let Some(neighbours) = flows.get(&state.pc) {
                // //dbg!(&neighbours);

                let new_path_ids = std::iter::once(state.path_id)
                    .chain((1..neighbours.len()).map(|_| path_counter.borrow_mut().next_id()));

                for (neighbour_pc, path_id) in neighbours.iter().zip(new_path_ids) {
                    let mut new_state = state.clone();
                    new_state.path_id = path_id;
                    new_state.pc = *neighbour_pc;
                    new_state.path_length += 1;

                    let result = sym_exec(
                        &mut new_state,
                        program,
                        flows,
                        k - 1,
                        st,
                        root_logger.clone(),
                        path_counter.clone(),
                    );
                    if result != SymResult::Valid {
                        return result;
                    }
                }
            } else {
                // Function exit of the main function under verification
                if let CFGStatement::FunctionExit { .. } = &program[&state.pc] {
                    return SymResult::Valid;
                } else {
                    return SymResult::Invalid;
                }
            }
        }
        ActionResult::InvalidAssertion => {
            return SymResult::Invalid;
        }
        ActionResult::InfeasiblePath => {
            // Finish this branch
            return SymResult::Valid;
        }
        ActionResult::Finish => {
            return SymResult::Valid;
        }
        ActionResult::ArrayInitialization(array_name) => {
            const N: u64 = 3;
            let StackFrame { params, .. } = state.stack.last_mut().unwrap();

            let array_type = params[&array_name].type_of();

            let inner_type = match array_type.clone() {
                RuntimeType::ArrayRuntimeType { inner_type } => inner_type,
                _ => panic!(
                    "Expected array type, found {:?}",
                    params[&array_name].type_of()
                ),
            };

            let new_path_ids = std::iter::once(state.path_id)
                .chain((1..N).map(|_| path_counter.borrow_mut().next_id()));

            for (array_size, path_id) in (0..N).zip(new_path_ids) {
                let mut new_state = state.clone();
                new_state.path_id = path_id;

                let r = new_state.next_reference_id();
                let StackFrame { params, .. } = new_state.stack.last_mut().unwrap();
                params.insert(
                    array_name.clone(),
                    Rc::new(Expression::Ref {
                        ref_: r,
                        type_: RuntimeType::ARRAYRuntimeType,
                    }),
                );

                let array_elements = (0..array_size)
                    .map(|i| {
                        create_symbolic_var(format!("{}{}", array_name, i), *inner_type.clone())
                            .into()
                    })
                    .collect();

                new_state.heap.insert(
                    r,
                    HeapValue::ArrayValue {
                        elements: array_elements,
                        type_: array_type.clone(),
                    }
                    .into(),
                );

                dbg!(
                    "after array initialization",
                    &new_state.heap,
                    &new_state.alias_map
                );

                // note k does not decrease, we stay at the same statement containing array access
                let result = sym_exec(
                    &mut new_state,
                    program,
                    flows,
                    k,
                    st,
                    root_logger.clone(),
                    path_counter.clone(),
                );
                if result != SymResult::Valid {
                    return result;
                }
            }

            // And a branch for the case where the array is NULL
            let StackFrame { params, .. } = state.stack.last_mut().unwrap();
            params.insert(array_name.clone(), Expression::NULL.into());

            let result = sym_exec(state, program, flows, k, st, root_logger, path_counter);
            if result != SymResult::Valid {
                return result;
            }
        }
        ActionResult::StateSplit((guard, true_lhs, false_lhs, lhs_name)) => {
            // split up the paths into two, one where guard == true and one where guard == false.
            let mut true_state = state.clone();
            let feasible_path = exec_assume(&mut true_state, guard.clone(), st);
            if feasible_path {
                write_to_stack(lhs_name.clone(), true_lhs, &mut true_state.stack);
                let result = sym_exec(
                    &mut true_state,
                    program,
                    flows,
                    k,
                    st,
                    root_logger.clone(),
                    path_counter.clone(),
                );
                if result != SymResult::Valid {
                    return result;
                }
            }

            let false_state = state;
            false_state.path_id = path_counter.borrow_mut().next_id();
            let feasible_path = exec_assume(false_state, guard, st);
            if feasible_path {
                write_to_stack(lhs_name, false_lhs, &mut false_state.stack);
                let result = sym_exec(
                    false_state,
                    program,
                    flows,
                    k,
                    st,
                    root_logger.clone(),
                    path_counter.clone(),
                );
                if result != SymResult::Valid {
                    return result;
                }
            }
        }
        ActionResult::StateSplitObjectTypes {
            symbolic_object_ref,
            resulting_alias,
        } => {
            let alias = &state.alias_map[&symbolic_object_ref];
            // group on (class_name, method_name)
            // let alias = utils::group_by(alias.aliases.iter().map(|e| (e.type_of(), e.clone())));

            assert!(resulting_alias.len() > 1);

            debug!(state.logger, "Splitting up current path into {:?} paths due to polymorphic method invocation", resulting_alias.len();
                "object" => #?symbolic_object_ref,
                "resulting_split" => #?resulting_alias
            );

            let new_path_ids = std::iter::once(state.path_id)
                .chain((1..resulting_alias.len()).map(|_| path_counter.borrow_mut().next_id()));
            let new_states =
                resulting_alias
                    .into_iter()
                    .zip(new_path_ids)
                    .map(|((_, objects), path_id)| {
                        let mut state = state.clone();
                        state
                            .alias_map
                            .insert(symbolic_object_ref.clone(), AliasEntry::new(objects));
                        state.path_id = path_id;
                        state
                    });

            for mut state in new_states {
                let result = sym_exec(
                    &mut state,
                    program,
                    flows,
                    k,
                    st,
                    root_logger.clone(),
                    path_counter.clone(),
                );
                if result != SymResult::Valid {
                    return result;
                }
            }
        }
    };
    SymResult::Valid
}

enum ActionResult {
    Continue,
    Return(u64),
    FunctionCall(u64),
    InvalidAssertion,
    InfeasiblePath,
    Finish,
    ArrayInitialization(Identifier),
    StateSplit((Rc<Expression>, Rc<Expression>, Rc<Expression>, Identifier)), // ?
    StateSplitObjectTypes {
        symbolic_object_ref: Identifier, // alias map entry
        resulting_alias: HashMap<(Identifier, Identifier), Vec<Rc<Expression>>>, // (class_name, method) -> resulting objects.
    },
}

fn action(
    state: &mut State,
    program: &HashMap<u64, CFGStatement>,
    k: u64,
    st: &SymbolicTable,
) -> ActionResult {
    let pc = state.pc;
    let action = &program[&pc];

    debug!(state.logger, "Action";
     "action" => #?action,
     "stack" => ?state.stack.last().map(|s| &s.params),
     "heap" => ?state.heap,
     "alias_map" => ?state.alias_map);
    // dbg!(
    //     &action,
    //     state.stack.last().map(|s| &s.params),
    //     &state.heap,
    //     &state.alias_map
    // );

    match action {
        CFGStatement::Statement(Statement::Declare { type_, var }) => {
            let StackFrame { pc, t, params, .. } = state.stack.last_mut().unwrap();
            params.insert(var.clone(), Rc::new(type_.default()));

            ActionResult::Continue
        }
        CFGStatement::Statement(Statement::Assign { lhs, rhs }) => {
            // If lhs or rhs contains an uninitialized array, we must initialize it
            // When we initialize an array, we split up the state into multiple states each with an increasingly longer instance of the array.
            // In other words, we must split this path into multiple paths.
            // This will be done in sym_exec. We return an ActionResult::ArrayInitialization with the current program counter.

            if let Lhs::LhsElem { var, .. } = lhs {
                // if var is an uninitialized array (symbolic reference)
                if let Expression::SymbolicRef { .. } =
                    state.stack.last().unwrap().params[var].as_ref()
                {
                    return ActionResult::ArrayInitialization(var.clone());
                }
            }
            // RhsElem 'a[i]' and RhsCall 'x.foo()' have a special case,
            // others are handled in evaluateRhs
            match rhs {
                Rhs::RhsElem {
                    // if rhs contains an uninitialized array
                    var: Expression::Var { var, .. },
                    ..
                } => {
                    if let Expression::SymbolicRef { .. } =
                        state.stack.last().unwrap().params[var].as_ref()
                    {
                        return ActionResult::ArrayInitialization(var.clone());
                    }
                }
                Rhs::RhsCall { invocation, type_ } => {
                    // if rhs contains an invocation.
                    return exec_invocation(state, invocation, &program, pc, Some(lhs.clone()), st);
                }
                _ => (),
            }

            let value = evaluateRhs(state, rhs, st);
            let e = evaluate(state, value, st);

            let state_split = execute_assign(state, lhs, e, st);

            if let Some(state_split) = state_split {
                return ActionResult::StateSplit(state_split);
            }

            ActionResult::Continue
        }
        CFGStatement::Statement(Statement::Assert { assertion }) => {
            let expression = prepare_assert_expression(state, Rc::new(assertion.clone()), st);

            let is_valid = eval_assertion(state, expression, st);
            if !is_valid {
                return ActionResult::InvalidAssertion;
            }
            ActionResult::Continue
        }
        CFGStatement::Statement(Statement::Assume { assumption }) => {
            let is_feasible_path = exec_assume(state, Rc::new(assumption.clone()), st);
            if !is_feasible_path {
                return ActionResult::InfeasiblePath;
            }
            ActionResult::Continue
        }
        CFGStatement::Statement(Statement::Return { expression }) => {
            if let Some(expression) = expression {
                let expression = evaluate(state, Rc::new(expression.clone()), st);
                let StackFrame { pc, t, params, .. } = state.stack.last_mut().unwrap();
                params.insert("retval".to_string(), expression);
            }
            ActionResult::Continue
        }
        CFGStatement::FunctionEntry { .. } => {
            // only check preconditions when it's the first method called??
            // we assume that the previous stackframe is of this method
            let StackFrame { current_member, .. } = state.stack.last().unwrap();
            if let Some(requires) = current_member.requires() {
                // if this is the program entry, assume that require is true, otherwise assert it.
                if (state.path_length == 0) {
                    // if any parameters currently are symbolic arrays, initialise them

                    let mut symbolic_array_parameters = state
                        .stack
                        .last()
                        .unwrap()
                        .params
                        .iter()
                        .filter(|(id, exp)| {
                            if let Expression::SymbolicRef {
                                var,
                                type_: RuntimeType::ArrayRuntimeType { inner_type },
                            } = exp.as_ref()
                            {
                                true
                            } else {
                                false
                            }
                        });

                    if let Some((array_name, _)) = symbolic_array_parameters.next() {
                        return ActionResult::ArrayInitialization(array_name.clone());
                    }

                    let expression = evaluate(state, requires, st);

                    if *expression == false_lit() {
                        println!("Constraint is infeasible");
                        return ActionResult::InfeasiblePath;
                    } else if *expression != true_lit() {
                        state.constraints.insert(expression.deref().clone());
                    }
                } else {
                    let requires = prepare_assert_expression(state, requires, st);
                    let is_valid = eval_assertion(state, requires.clone(), st);
                    if !is_valid {
                        return ActionResult::InvalidAssertion;
                    }
                    state.constraints.insert(requires.deref().clone());
                }
            }

            ActionResult::Continue
        }
        CFGStatement::FunctionExit {
            decl_name,
            method_name,
        } => {
            state.exception_handler.decrement_handler();

            let StackFrame {
                current_member,
                params,
                ..
            } = state.stack.last().unwrap();
            if let Some(post_condition) = current_member.post_condition().clone() {
                let expression = prepare_assert_expression(state, post_condition, st);
                let is_valid = eval_assertion(state, expression, st);
                if !is_valid {
                    // postcondition invalid
                    return ActionResult::InvalidAssertion;
                }
            }
            if state.stack.len() == 1 {
                ActionResult::Continue
                // we are pbobably done now
            } else {
                //dbg!(&state.stack);

                let StackFrame {
                    pc,
                    t,
                    params,
                    current_member,
                } = state.stack.pop().unwrap();
                let return_type = current_member.type_of();
                if return_type != RuntimeType::VoidRuntimeType {
                    if let Some(lhs) = t {
                        let rv = params.get(&retval()).unwrap();
                        let return_value = evaluate(state, rv.clone(), st);

                        // perhaps also write retval to current stack?
                        // will need to do this due to this case: `return o.func();`

                        execute_assign(state, &lhs, return_value, st);
                    }
                }

                ActionResult::Return(pc)
            }
        }
        CFGStatement::Statement(Statement::Call { invocation }) => {
            exec_invocation(state, invocation, &program, pc, None, st)
        }
        CFGStatement::Statement(Statement::Throw { message }) => exec_throw(state, st),
        CFGStatement::TryCatch(_, _, catch_entry_pc, _) => {
            state
                .exception_handler
                .insert_handler(ExceptionHandlerEntry::new(*catch_entry_pc));
            ActionResult::Continue
        }
        CFGStatement::TryEntry(_) => ActionResult::Continue,
        CFGStatement::TryExit => {
            // state.exception_handler.remove_last_handler();
            ActionResult::Continue
        }
        CFGStatement::CatchEntry(_) => ActionResult::Continue,
        _ => ActionResult::Continue,
    }
}

fn exec_throw(state: &mut State, st: &SymbolicTable) -> ActionResult {
    if let Some(ExceptionHandlerEntry {
        catch_pc,
        mut current_depth,
    }) = state.exception_handler.pop_last()
    {
        while current_depth > 0 {
            let stack_frame = state
                .stack
                .pop()
                .unwrap_or_else(|| panic!("Unexpected empty stack"));

            if let Some(exceptional) = stack_frame.current_member.exceptional() {
                let assertion = prepare_assert_expression(state, exceptional, st);
                //dbg!(&assertion);
                let is_valid = eval_assertion(state, assertion, st);
                if !is_valid {
                    return ActionResult::InvalidAssertion;
                }
            }
            current_depth -= 1;
        }

        ActionResult::Return(catch_pc)
    } else {
        while let Some(stack_frame) = state.stack.last() {
            if let Some(exceptional) = stack_frame.current_member.exceptional() {
                let assertion = prepare_assert_expression(state, exceptional, st);
                //dbg!(&assertion);
                let is_valid = eval_assertion(state, assertion, st);
                if !is_valid {
                    return ActionResult::InvalidAssertion;
                }
            }
            state.stack.pop();
        }

        ActionResult::Finish
    }
}

fn lhs_contains_symbolic_array(state: &State, lhs: &Lhs) -> Option<String> {
    if let Lhs::LhsElem { var, .. } = lhs {
        // if var is an uninitialized array (symbolic reference)
        if let Expression::SymbolicRef { .. } = state.stack.last().unwrap().params[var].as_ref() {
            return Some(var.clone());
        }
    }
    None
}

fn rhs_contains_symbolic_array(state: &State, lhs: &Lhs) -> Option<String> {
    if let Lhs::LhsElem { var, .. } = lhs {
        // if var is an uninitialized array (symbolic reference)
        if let Expression::SymbolicRef { .. } = state.stack.last().unwrap().params[var].as_ref() {
            return Some(var.clone());
        }
    }
    None
}

fn eval_assertion(state: &mut State, expression: Rc<Expression>, st: &SymbolicTable) -> bool {
    // dbg!("invoke Z3 with:", &expression);
    // dbg!(&alias_map);

    if *expression == true_lit() {
        false
    } else if *expression == false_lit() {
        true
    } else {
        let symbolic_refs = find_symbolic_refs(&expression);
        if symbolic_refs.len() == 0 {
            let result = z3_checker::verify(&expression);
            if let SatResult::Unsat = result {
            } else {
                return false;
            }
        } else {
            // dbg!(&symbolic_refs);
            let expressions = concretizations(expression.clone(), &symbolic_refs, &state.alias_map);
            // dbg!(&expressions);

            for expression in expressions {
                let expression = evaluate(state, expression, st);
                if *expression == true_lit() {
                    return false;
                } else if *expression == false_lit() {
                    // valid, keep going
                    // dbg!("locally solved!");
                } else {
                    // panic!("should not do that right now");
                    let result = z3_checker::verify(&expression);
                    if let SatResult::Unsat = result {
                    } else {
                        // panic!("invalid");
                        return false;
                    }
                }
            }
        }
        return true;
    }
}

fn exec_invocation(
    state: &mut State,
    invocation: &Invocation,
    program: &HashMap<u64, CFGStatement>,
    return_point: u64,
    lhs: Option<Lhs>,
    st: &SymbolicTable,
) -> ActionResult {
    // dbg!(invocation);

    debug!(state.logger, "Invocation"; "invocation" => %invocation);

    state.exception_handler.increment_handler();

    match invocation {
        Invocation::InvokeMethod {
            resolved,
            lhs: invocation_lhs,
            arguments,
            ..
        } => {
            let potential_methods = resolved.as_ref().unwrap();

            if potential_methods.len() == 1 {
                debug!(state.logger, "only one potential method, resolved");
                // potentially a static method.
                let (_, potential_method) = &potential_methods.iter().next().unwrap();
                // A static method, or a method that is not overriden anywhere (non-polymorphic)
                let next_entry = invocation::single_method_invocation(
                    state,
                    invocation,
                    potential_method,
                    return_point,
                    lhs,
                    program,
                    st,
                );
                return ActionResult::FunctionCall(next_entry);
            } else {
                dbg!(invocation_lhs);

                return invocation::multiple_method_invocation(
                    state,
                    invocation_lhs,
                    invocation,
                    potential_methods,
                    return_point,
                    lhs,
                    program,
                    st,
                );
            }
        }
        // (Invocation::InvokeMethod { resolved: Some((DeclarationMember::Method {
        //     is_static: false,
        //     return_type,
        //     name,
        //     params,
        //     specification,
        //     body,
        // })), .. }) => {
        //     // evaluate arguments
        //     let arguments = invocation
        //         .arguments()
        //         .into_iter()
        //         .map(|arg| evaluate(state, Rc::new(arg.clone()), st))
        //         .collect::<Vec<_>>();

        //     let invocation_lhs = if let Invocation::InvokeMethod { lhs, .. } = invocation {
        //         lhs
        //     } else {
        //         panic!("expected invokemethod");
        //     };
        //     dbg!(invocation_lhs);
        //     let object = lookup_in_stack(invocation_lhs, &state.stack).unwrap();
        //     // object can be either a concrete reference to a heap object, or a symbolic object
        //     // the latter means that we have to split states here, one path for every alias object types,
        //     // if there is only one possible then we can also continue with that path
        //     let type_ = match object.as_ref() {
        //         Expression::Ref { ref_, type_ } => type_,
        //         Expression::SymbolicRef { var, type_ } => todo!(),
        //         _ => unreachable!(),
        //     };

        //     let this = (type_.clone(), invocation_lhs.to_owned());

        //     exec_method(
        //         state,
        //         return_point,
        //         member.clone(),
        //         lhs,
        //         &arguments,
        //         &params,
        //         st,
        //         this,
        //     );
        //     // TODO: add lookup for overrides, in case of an object with superclasses
        //     let next_entry =
        //         find_entry_for_static_invocation(class_name, invocation.identifier(), program);

        //     ActionResult::FunctionCall(next_entry)
        // }
        Invocation::InvokeConstructor {
            resolved,
            class_name,
            ..
        } => {
            let (declaration, member): &(Declaration, Rc<DeclarationMember>) = resolved
                .as_ref()
                .map(AsRef::as_ref)
                .unwrap_or_else(|| panic!("Unresolved constructor for class {}", class_name));
            let class_name = declaration.name();
            if let DeclarationMember::Constructor {
                name,
                params,
                specification,
                body,
            } = member.as_ref()
            {
                // evaluate arguments
                let arguments = invocation
                    .arguments()
                    .into_iter()
                    .map(|arg| evaluate(state, Rc::new(arg.clone()), st))
                    .collect::<Vec<_>>();

                // Zis is problems with interfaces
                let this_param = Parameter {
                    type_: NonVoidType::ReferenceType {
                        identifier: class_name.to_string(),
                    },
                    name: "this".to_owned(),
                };
                exec_constructor(
                    state,
                    return_point,
                    member.clone(),
                    lhs,
                    &arguments,
                    params,
                    class_name,
                    st,
                    this_param,
                );

                let next_entry = find_entry_for_static_invocation(&class_name, &name, program);
                ActionResult::FunctionCall(next_entry)
            } else {
                panic!()
            }
        }
        Invocation::InvokeSuperConstructor { resolved, .. } => {
            let (declaration, member) = resolved.as_ref().map(AsRef::as_ref).unwrap();
            let class_name = declaration.name();
            if let DeclarationMember::Constructor {
                name,
                params,
                specification,
                body,
            } = member.as_ref()
            {
                // evaluate arguments
                let arguments = invocation
                    .arguments()
                    .into_iter()
                    .map(|arg| evaluate(state, Rc::new(arg.clone()), st))
                    .collect::<Vec<_>>();

                // zis is trouble with interfaces
                let this_param = Parameter {
                    type_: NonVoidType::ReferenceType {
                        identifier: class_name.to_string(),
                    },
                    name: "this".to_owned(),
                };
                exec_super_constructor(
                    state,
                    return_point,
                    member.clone(),
                    lhs,
                    &arguments,
                    params,
                    st,
                    this_param,
                );
                let next_entry = find_entry_for_static_invocation(&class_name, &name, program);
                ActionResult::FunctionCall(next_entry)
            } else {
                panic!()
            }
        }
        Invocation::InvokeSuperMethod { resolved, .. } => {
            let potential_method = resolved.as_ref().unwrap();

            let next_entry = invocation::single_method_invocation(
                state,
                invocation,
                potential_method,
                return_point,
                lhs,
                program,
                st,
            );
            return ActionResult::FunctionCall(next_entry);
        }
        // (_, DeclarationMember::Field { type_, name }) => todo!(),
        _ => panic!("Incorrect pair of Invocation and DeclarationMember"),
    }
}

fn find_entry_for_static_invocation(
    class_name: &str,
    method_name: &str,
    program: &HashMap<u64, CFGStatement>,
) -> u64 {
    // dbg!(invocation);
    let (entry, _) = program
        .iter()
        .find(|(k, v)| {
            if let CFGStatement::FunctionEntry {
                decl_name: other_decl_name,
                method_name: other_method_name,
            } = *v
            {
                other_decl_name == class_name && other_method_name == method_name
            } else {
                false
            }
        })
        .unwrap();

    *entry
}

fn exec_method(
    state: &mut State,
    return_point: u64,
    member: Rc<DeclarationMember>,
    lhs: Option<Lhs>,
    arguments: &[Rc<Expression>],
    parameters: &[Parameter],
    st: &SymbolicTable,
    this: (RuntimeType, Identifier),
) {
    let this_param = Parameter {
        type_: runtime_to_nonvoidtype(this.0.clone()).expect("concrete, nonvoid type"),
        name: "this".to_owned(),
    };
    let this_expr = Expression::Var {
        var: this.1.clone(),
        type_: this.0,
    };
    let parameters = std::iter::once(&this_param).chain(parameters.iter());
    let arguments = std::iter::once(Rc::new(this_expr)).chain(arguments.iter().cloned());

    push_stack_frame(
        state,
        return_point,
        member,
        lhs,
        parameters.zip(arguments),
        st,
    )
}

fn exec_static_method(
    state: &mut State,
    return_point: u64,
    member: Rc<DeclarationMember>,
    lhs: Option<Lhs>,
    arguments: &[Rc<Expression>],
    parameters: &[Parameter],
    st: &SymbolicTable,
) {
    push_stack_frame(
        state,
        return_point,
        member,
        lhs,
        parameters.iter().zip(arguments.iter().cloned()),
        st,
    )
}

fn exec_constructor(
    state: &mut State,
    return_point: u64,
    member: Rc<DeclarationMember>,
    lhs: Option<Lhs>,
    arguments: &[Rc<Expression>],
    parameters: &[Parameter],
    class_name: &str,
    st: &SymbolicTable,
    this_param: Parameter,
) {
    let parameters = std::iter::once(&this_param).chain(parameters.iter());

    let fields = st
        .get_all_fields(class_name)
        .iter()
        .map(|(s, t)| (s.to_string(), t.default().into()))
        .collect();
    let structure = HeapValue::ObjectValue {
        fields,
        type_: member.type_of(),
    };

    let object_ref = state.allocate_on_heap(structure);
    let arguments = std::iter::once(object_ref).chain(arguments.iter().cloned());

    push_stack_frame(
        state,
        return_point,
        member,
        lhs,
        parameters.zip(arguments),
        st,
    )
}

fn exec_super_constructor(
    state: &mut State,
    return_point: u64,
    member: Rc<DeclarationMember>,
    lhs: Option<Lhs>,
    arguments: &[Rc<Expression>],
    parameters: &[Parameter],
    st: &SymbolicTable,
    this_param: Parameter,
) {
    let parameters = std::iter::once(&this_param).chain(parameters.iter());

    // instead of allocating a new object, add the new fields to the existing 'this' object.
    let object_ref = lookup_in_stack("this", &state.stack)
        .expect("super() is called in a constructor with a 'this' object on the stack");
    let arguments = std::iter::once(object_ref).chain(arguments.iter().cloned());

    push_stack_frame(
        state,
        return_point,
        member,
        lhs,
        parameters.zip(arguments),
        st,
    )
}

fn push_stack_frame<'a, P>(
    state: &mut State,
    return_point: u64,
    member: Rc<DeclarationMember>,
    lhs: Option<Lhs>,
    params: P,
    st: &SymbolicTable,
) where
    P: Iterator<Item = (&'a Parameter, Rc<Expression>)>,
{
    let params = params
        .map(|(p, e)| (p.name.clone(), evaluate(state, e, st)))
        .collect();
    let stack_frame = StackFrame {
        pc: return_point,
        t: lhs,
        params,
        current_member: member,
    };
    state.stack.push(stack_frame);
}

fn prepare_assert_expression(
    state: &mut State,
    assertion: Rc<Expression>,
    st: &SymbolicTable,
) -> Rc<Expression> {
    let expression = if state.constraints.len() >= 1 {
        let assumptions = state
            .constraints
            .iter()
            .cloned()
            .reduce(|x, y| Expression::BinOp {
                bin_op: BinOp::And,
                lhs: Rc::new(x),
                rhs: Rc::new(y),
                type_: RuntimeType::BoolRuntimeType,
            })
            .unwrap();

        negate(Rc::new(Expression::BinOp {
            bin_op: BinOp::Implies,
            lhs: Rc::new(assumptions),
            rhs: assertion,
            type_: RuntimeType::BoolRuntimeType,
        }))
    } else {
        negate(assertion)
    };
    // let expression = constraints.iter().fold(
    //     Expression::UnOp {
    //         un_op: UnOp::Negative,
    //         value: Box::new(assertion.clone()),
    //         type_: RuntimeType::BoolRuntimeType,
    //     },
    //     |x, b| Expression::BinOp {
    //         bin_op: BinOp::And,
    //         lhs: Box::new(x),
    //         rhs: Box::new(b.clone()),
    //         type_: RuntimeType::BoolRuntimeType,
    //     },
    // );
    debug!(state.logger, "Expression to evaluate: {:?}", expression);
    let z = evaluate(state, Rc::new(expression), st);
    debug!(state.logger, "Evaluated expression: {:?}", z);
    z
}

fn read_field_concrete_ref(heap: &mut Heap, ref_: i64, field: &Identifier) -> Rc<Expression> {
    match heap.get_mut(&ref_).unwrap() {
        HeapValue::ObjectValue { fields, type_ } => fields[field].clone(),
        _ => panic!("Expected object, found array heapvalue"),
    }
}

fn read_field_symbolic_ref(
    heap: &mut Heap,
    concrete_refs: &[Rc<Expression>],
    sym_ref: Rc<Expression>,
    field: &Identifier,
) -> Rc<Expression> {
    match concrete_refs {
        [] => panic!(),
        [r] => {
            if let Expression::Ref { ref_, .. } = **r {
                read_field_concrete_ref(heap, ref_, field)
            } else {
                panic!()
            }
        }
        // assuming here that concrete refs (perhaps in ITE expression)
        [r, rs @ ..] => {
            if let Expression::Ref { ref_, .. } = **r {
                Rc::new(Expression::Conditional {
                    guard: Rc::new(Expression::BinOp {
                        bin_op: BinOp::Equal,
                        lhs: sym_ref.clone(),
                        rhs: r.clone(),
                        type_: RuntimeType::ANYRuntimeType,
                    }),
                    true_: (read_field_concrete_ref(heap, ref_, &field)),
                    false_: (read_field_symbolic_ref(heap, rs, sym_ref, field)),
                    type_: RuntimeType::ANYRuntimeType,
                })
            } else {
                panic!()
            }
        }
        // null is not possible here, will be caught with exceptional state
        _ => panic!(),
    }
}

fn write_field_concrete_ref(
    heap: &mut Heap,
    ref_: i64,
    field: &Identifier,
    value: Rc<Expression>,
) -> () {
    // let x = ;

    if let HeapValue::ObjectValue { fields, type_ } = heap.get_mut(&ref_).unwrap() {
        fields.insert(field.clone(), value);
    } else {
        panic!("expected object")
    }
}

fn write_field_symbolic_ref(
    heap: &mut Heap,
    concrete_refs: &Vec<Rc<Expression>>,
    field: &Identifier,
    sym_ref: Rc<Expression>,
    value: Rc<Expression>,
) -> () {
    match concrete_refs.as_slice() {
        [] => panic!(),
        [r] => {
            if let Expression::Ref { ref_, .. } = **r {
                write_field_concrete_ref(heap, ref_, field, value);
            } else {
                panic!()
            }
        }
        rs => {
            for r in rs {
                if let Expression::Ref { ref_, type_ } = r.as_ref() {
                    let ite = ite(
                        Rc::new(equal(sym_ref.clone(), r.clone())),
                        value.clone(),
                        read_field_concrete_ref(heap, *ref_, &field),
                    );
                    write_field_concrete_ref(heap, *ref_, field, Rc::new(ite))
                } else {
                    panic!("Should only contain refs, {:?}", r.as_ref());
                }
            }
        }
    }
}

fn null() -> Expression {
    Expression::Lit {
        lit: Lit::NullLit,
        type_: RuntimeType::ANYRuntimeType,
    }
}

/// Initialise a symbolic object reference.
pub fn init_symbolic_reference(
    state: &mut State,
    sym_ref: &Identifier,
    type_ref: &RuntimeType,
    st: &SymbolicTable,
) {
    if !state.alias_map.contains_key(sym_ref) {
        debug!(state.logger, "Lazy initialisation of symbolic reference"; "ref" => #?sym_ref, "type" => #?type_ref);

        // Symbolic objects are first ReferenceRuntimeType {type} (uninitialized)
        // then if they are initialised by a single type they remain that
        // if they become initialised by multiple types their type becomes REFRuntimeType (or a different one)
        // Or aliasmap contains a flag whether all types are the same of the symbolic object or there are multipe types.
        let decl_name = if let RuntimeType::ReferenceRuntimeType { type_ } = type_ref {
            type_
        } else {
            panic!("Cannot initialize any other atm");
        };

        // initialise new objects, one for each possible type (sub)class of class_name
        let new_object_references = st
            .get_all_instance_types(decl_name)
            .iter()
            .map(|class_name| {
                let fields = st
                    .get_all_fields(&class_name)
                    .iter()
                    .map(|(field_name, type_)| {
                        (
                            field_name.clone(),
                            Rc::new(initialize_symbolic_var(
                                &field_name,
                                &type_.type_of(),
                                state.next_reference_id(),
                            )),
                        )
                    })
                    .collect();

                let reference = state.allocate_on_heap(
                    HeapValue::ObjectValue {
                        fields,
                        type_: RuntimeType::ReferenceRuntimeType {
                            type_: class_name.clone(),
                        },
                    }
                    .into(),
                );

                reference
            })
            .collect_vec();

        // Find all other possible concrete references of the same type as sym_ref
        let instance_types = st.get_all_instance_types(decl_name);

        let has_unique_type = instance_types.len() == 1;

        let existing_aliases = state
            .alias_map
            .values()
            .filter_map(|x| {
                if let Some(type_) = x.uniform_type() {
                    if instance_types
                        .contains(type_.as_reference_type().expect("expected reference type"))
                    {
                        Some(Either::Left(x.aliases.iter()))
                    } else {
                        None
                    }
                } else {
                    Some(Either::Right(
                        x.aliases.iter().filter(|x| x.type_of() == *type_ref),
                    ))
                }
            })
            .flat_map(|x| x.into_iter())
            .unique();

        let aliases = existing_aliases
            .cloned()
            .chain(std::iter::once(Expression::NULL.into()))
            .chain(new_object_references.into_iter())
            .collect();

        state.alias_map.insert(
            sym_ref.clone(),
            AliasEntry {
                aliases,
                uniform_type: has_unique_type,
            },
        );
        debug!(state.logger, "Updated aliasentry"; "alias_map" => #?state.alias_map);
    }
}

// can't you have a symbolic array, as in the a in a[i] is symbolic?
fn write_index(heap: &mut Heap, ref_: i64, index: &Expression, value: &Expression) {
    // match index {
    //     Expression::Ref { ref_, type_ } => {
    //         let Expression::Lit { lit , type_ } = (&mut heap[ref_]);
    //     },
    //     Expression::SymbolicRef { var, type_ } => {},

    // }
}

type ConditionalStateSplit = (Rc<Expression>, Rc<Expression>, Rc<Expression>, Identifier);

fn execute_assign(
    state: &mut State,
    lhs: &Lhs,
    e: Rc<Expression>,
    st: &SymbolicTable,
) -> Option<ConditionalStateSplit> {
    match lhs {
        Lhs::LhsVar { var, type_ } => {
            let StackFrame { pc, t, params, .. } = state.stack.last_mut().unwrap();
            params.insert(var.clone(), e);
        }
        Lhs::LhsField {
            var,
            var_type,
            field,
            type_,
        } => {
            let StackFrame { pc, t, params, .. } = state.stack.last_mut().unwrap();
            let o = params
                .get(var)
                .unwrap_or_else(|| panic!("infeasible, object does not exit"))
                .clone();

            match o.as_ref() {
                Expression::Ref { ref_, type_ } => {
                    write_field_concrete_ref(&mut state.heap, *ref_, field, e);
                }
                sym_ref @ Expression::SymbolicRef { var, type_ } => {
                    init_symbolic_reference(state, &var, &type_, st);
                    // should also remove null here? --Assignemnt::45
                    // Yes, we have if (x = null) { throw; } guards that ensure it cannot be null
                    remove_symbolic_null(&mut state.alias_map, var);
                    let concrete_refs = &state.alias_map[var];
                    // dbg!(&var, &concrete_refs);
                    write_field_symbolic_ref(
                        &mut state.heap,
                        &concrete_refs.aliases,
                        field,
                        Rc::new(sym_ref.clone()),
                        e,
                    );
                }
                e @ Expression::Conditional {
                    guard,
                    true_,
                    false_,
                    type_,
                } => {
                    return Some((guard.clone(), true_.clone(), false_.clone(), var.clone()));
                }

                _ => todo!("{:?}", o.as_ref()),
            }
        }
        Lhs::LhsElem { var, index, type_ } => {
            let StackFrame { pc, t, params, .. } = state.stack.last_mut().unwrap();
            let ref_ = params
                .get(var)
                .unwrap_or_else(|| panic!("infeasible, array does not exit"))
                .clone();

            // let int_value = if let Expression::Lit { lit: Lit::IntLit { int_value }, type_ } = index {
            //     *int_value
            // } else {
            //     panic!("Array index is not an integer value");
            // };

            match ref_.as_ref() {
                Expression::Ref { ref_, type_ } => {
                    let index = evaluateAsInt(state, index.clone(), st);

                    match index {
                        Either::Left(index) => write_elem_symbolic_index(state, *ref_, index, e),
                        Either::Right(i) => write_elem_concrete_index(state, *ref_, i, e),
                    }
                    // let size = evaluate(state, Rc::new(Expression::))
                }
                _ => panic!("expected array ref, found expr {:?}", &ref_),
            }
        }
    }
    return None;
}

// fn evaluateRhs(state: &mut State, rhs: &Rhs) -> Expression {
fn evaluateRhs(state: &mut State, rhs: &Rhs, st: &SymbolicTable) -> Rc<Expression> {
    match rhs {
        Rhs::RhsExpression { value, type_ } => {
            match value {
                Expression::Var { var, type_ } => lookup_in_stack(var, &state.stack).unwrap(),
                _ => Rc::new(value.clone()), // might have to expand on this when dealing with complex quantifying expressions and array
            }
        }
        Rhs::RhsField { var, field, type_ } => {
            if let Expression::Var { var, .. } = var {
                let StackFrame { pc, t, params, .. } = state.stack.last_mut().unwrap();
                let object = params.get(var).unwrap().clone();
                exec_rhs_field(state, &object, field, type_, st)
            } else {
                panic!(
                    "Currently only right hand sides of the form <variable>.<field> are allowed."
                )
            }
        }
        Rhs::RhsElem { var, index, type_ } => {
            if let Expression::Var { var, .. } = var {
                let StackFrame { pc, t, params, .. } = state.stack.last_mut().unwrap();
                let array = params.get(var).unwrap().clone();
                exec_rhs_elem(state, array, index.to_owned().into(), st)
            } else {
                panic!("Unexpected uninitialized array");
            }
            //read_elem_concrete_index(state, ref_, index)
            //
        }
        Rhs::RhsCall { invocation, type_ } => {
            unreachable!("unreachable, invocations are handled in function exec_invocation()")
        }

        Rhs::RhsArray {
            array_type,
            sizes,
            type_,
        } => {
            return exec_array_construction(state, array_type, sizes, type_, st);
        }
        _ => unimplemented!(),
    }
}

fn exec_rhs_field(
    state: &mut State,
    object: &Expression,
    field: &Identifier,
    type_: &RuntimeType,
    st: &SymbolicTable,
) -> Rc<Expression> {
    match object {
        Expression::Conditional {
            guard,
            true_,
            false_,
            type_,
        } => {
            // bedoelt hij hier niet exec true_ ipv execField true_ ?
            // nope want hij wil nog steeds het field weten ervan
            let true_ = exec_rhs_field(state, true_, field, type_, st);
            let false_ = exec_rhs_field(state, false_, field, type_, st);

            Rc::new(Expression::Conditional {
                guard: guard.clone(),
                true_: true_,
                false_: false_,
                type_: type_.clone(),
            })
        }
        Expression::Lit {
            lit: Lit::NullLit, ..
        } => panic!("infeasible"),
        Expression::Ref { ref_, type_ } => read_field_concrete_ref(&mut state.heap, *ref_, field),
        sym_ref @ Expression::SymbolicRef { var, type_ } => {
            init_symbolic_reference(state, var, type_, st);
            remove_symbolic_null(&mut state.alias_map, var);
            let concrete_refs = &state.alias_map[var];
            // dbg!(&alias_map);
            // dbg!(&heap);
            read_field_symbolic_ref(
                &mut state.heap,
                &concrete_refs.aliases,
                Rc::new(sym_ref.clone()),
                field,
            )
        }
        _ => todo!("Expected reference here, found: {:?}", object),
    }
}

fn exec_rhs_elem(
    state: &mut State,
    array: Rc<Expression>,
    index: Rc<Expression>,
    st: &SymbolicTable,
) -> Rc<Expression> {
    if let Expression::Ref { ref_, .. } = array.as_ref() {
        let index = evaluateAsInt(state, index, st);
        match index {
            Either::Left(index) => read_elem_symbolic_index(state, *ref_, index),
            Either::Right(index) => read_elem_concrete_index(state, *ref_, index),
        }
    } else {
        panic!("Expected array reference");
    }
}

fn true_lit() -> Expression {
    Expression::Lit {
        lit: Lit::BoolLit { bool_value: true },
        type_: RuntimeType::BoolRuntimeType,
    }
}

fn false_lit() -> Expression {
    Expression::Lit {
        lit: Lit::BoolLit { bool_value: false },
        type_: RuntimeType::BoolRuntimeType,
    }
}

fn remove_symbolic_null(alias_map: &mut AliasMap, var: &str) {
    // dbg!(&alias_map, &var);
    alias_map.get_mut(var).unwrap().remove_null(var)
}

fn create_symbolic_var(name: String, type_: impl Typeable) -> Expression {
    if type_.is_of_type(RuntimeType::REFRuntimeType) {
        Expression::SymbolicRef {
            var: name,
            type_: type_.type_of(),
        }
    } else {
        Expression::SymbolicVar {
            var: name,
            type_: type_.type_of(),
        }
    }
}

/// Create uninitialised variable (that can be initialized lazily)
fn initialize_symbolic_var(name: &str, type_: &RuntimeType, ref_: i64) -> Expression {
    let sym_name = format!("{}{}", name, ref_);
    create_symbolic_var(sym_name, type_.clone())
}

fn read_elem_concrete_index(state: &mut State, ref_: Reference, index: i64) -> Rc<Expression> {
    if let HeapValue::ArrayValue { elements, .. } = state.heap.get(&ref_).unwrap() {
        elements[index as usize].clone()
    } else {
        panic!("Expected Array object");
    }
}

/// Reads an expression from the array at reference ref_ in the heap,
/// with a symbolic index.
///
/// Since it is symbolic it will return a nested if-then-else expression
/// Like this:
/// index == #1 ? e1 : (index == #2 ? e2 : e3)
fn read_elem_symbolic_index(
    state: &mut State,
    ref_: Reference,
    index: Rc<Expression>,
) -> Rc<Expression> {
    if let HeapValue::ArrayValue { elements, .. } = state.heap.get(&ref_).unwrap() {
        let indices = (0..elements.len()).map(|i| toIntExpr(i as i64));

        let mut indexed_elements = elements.iter().zip(indices).rev();

        if let Some((last_element, _)) = indexed_elements.next() {
            let value = indexed_elements
                .fold(last_element.clone(), |acc, (element, concrete_index)| {
                    ite(equal(index.clone(), concrete_index), element.clone(), acc).into()
                })
                .into();
            value
        } else {
            // empty array

            todo!("infeasible? or invalid?") // I assume that the added exceptional clauses should prevent this
        }
    } else {
        panic!("Expected Array object");
    }
}

fn write_elem_concrete_index(
    state: &mut State,
    ref_: Reference,
    index: i64,
    expression: Rc<Expression>,
) {
    if let HeapValue::ArrayValue { elements, .. } = state.heap.get_mut(&ref_).unwrap() {
        if index >= 0 && index < elements.len() as i64 {
            elements[index as usize] = expression;
        } else {
            panic!("infeasible due to added checked array bounds");
        }
    } else {
        panic!("Expected Array object")
    }
}

fn write_elem_symbolic_index(
    state: &mut State,
    ref_: Reference,
    index: Rc<Expression>,
    expression: Rc<Expression>,
) {
    if let HeapValue::ArrayValue { elements, .. } = state.heap.get_mut(&ref_).unwrap() {
        let indices = (0..elements.len()).map(|i| toIntExpr(i as i64));

        let indexed_elements = elements.iter_mut().zip(indices);

        for (value, concrete_index) in indexed_elements {
            *value = ite(
                equal(index.clone(), concrete_index),
                expression.clone(),
                value.clone(),
            )
            .into()
        }
    } else {
        panic!("expected Array object")
    }
}

/// Constructs an array that was created by an OOX statement like this:
// / ```
// / int[] a = new int[10];
// / ```
/// in this example, array_type = int, sizes = { 10 }, type_ = int[].
fn exec_array_construction(
    state: &mut State,
    array_type: &NonVoidType,
    sizes: &Vec<Expression>,
    type_: &RuntimeType,
    st: &SymbolicTable,
) -> Rc<Expression> {
    let ref_id = state.next_reference_id();

    assert!(sizes.len() == 1, "Support for only 1D arrays");
    // int[][] a = new int[10][10];

    let size =
        evaluateAsInt(state, Rc::new(sizes[0].clone()), st).expect_right("no symbolic array sizes");

    let array = (0..size)
        .map(|_| Rc::new(array_type.default()))
        .collect_vec();

    state.heap.insert(
        ref_id,
        HeapValue::ArrayValue {
            elements: array,
            type_: type_.clone(),
        },
    );

    Rc::new(Expression::Ref {
        ref_: ref_id,
        type_: type_.clone(),
    })
}

/// Helper function, does not invoke Z3 but tries to evaluate the assumption locally.
/// Returns whether the assumption was found to be infeasible.
/// Otherwise it inserts the assumption into the constraints.
fn exec_assume(state: &mut State, assumption: Rc<Expression>, st: &SymbolicTable) -> bool {
    let expression = evaluate(state, assumption, st);

    if *expression == false_lit() {
        return false;
    } else if *expression != true_lit() {
        state.constraints.insert(expression.deref().clone());
    }
    true
}

fn verify(file_content: &str, class_name: &str, method_name: &str, k: u64) -> SymResult {
    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    // dbg!(as_ref);
    let c = parse(&tokens);
    let c = c.unwrap();

    // dbg!(&c);

    let initial_function = c
        .find_class_declaration_member(method_name, class_name.into())
        .unwrap();

    let mut i = 0;
    let symbolic_table = SymbolicTable::from_ast(&c);
    let (result, flw) = labelled_statements(c, &mut i);

    let program = result.into_iter().collect();

    // dbg!(&program);

    let flows: HashMap<u64, Vec<u64>> = utils::group_by(flw.into_iter());

    // dbg!(&flows);
    // panic!();

    if let DeclarationMember::Method { params, .. } = initial_function.as_ref() {
        let pc = find_entry_for_static_invocation(class_name, method_name, &program);
        // dbg!(&params);
        let params = params
            .iter()
            .map(|p| {
                (
                    p.name.clone(),
                    Rc::new(create_symbolic_var(p.name.clone(), p.type_.type_of())),
                )
            })
            .collect();
        // dbg!(&params);

        // let root_logger = slog::Logger::root(
        //     Mutex::new(slog_bunyan::default(std::io::stderr()).filter_level(Level::Debug)).fuse(),
        //     o!(),
        // );

        let mut builder = TerminalLoggerBuilder::new();
        builder.level(Severity::Debug);
        builder.destination(Destination::Stdout);
        builder.format(sloggers::types::Format::Full);
        builder.source_location(sloggers::types::SourceLocation::FileAndLine);

        let root_logger = builder.build().unwrap();

        let mut state = State {
            pc,
            stack: vec![StackFrame {
                pc,
                t: None,
                params,
                current_member: initial_function,
            }],
            heap: HashMap::new(),
            precondition: true_lit(),
            constraints: HashSet::new(),
            alias_map: HashMap::new(),
            ref_counter: IdCounter::new(0),
            exception_handler: Default::default(),
            path_length: 0,
            logger: root_logger.new(o!("pathId" => 0)),
            path_id: 0,
        };

        let path_counter = Rc::new(RefCell::new(IdCounter::new(0)));

        return sym_exec(
            &mut state,
            &program,
            &flows,
            k,
            &symbolic_table,
            root_logger,
            path_counter,
        );
    } else {
        panic!()
    }
}

#[test]
fn sym_exec_of_absolute_simplest() {
    let file_content = include_str!("../examples/absolute_simplest.oox");
    assert_eq!(verify(file_content, "Foo", "f", 20), SymResult::Valid);
}

#[test]
fn sym_exec_min() {
    let file_content = include_str!("../examples/psv/min.oox");
    assert_eq!(verify(file_content, "Foo", "min", 20), SymResult::Valid);
}

#[test]
fn sym_exec_method() {
    let file_content = include_str!("../examples/psv/method.oox");
    assert_eq!(verify(file_content, "Main", "min", 20), SymResult::Valid);
}

#[test]
fn sym_exec_fib() {
    let file_content = std::fs::read_to_string("./examples/psv/fib.oox").unwrap();
    assert_eq!(verify(&file_content, "Main", "main", 70), SymResult::Valid);
}

#[test]
fn sym_test_failure() {
    let file_content = std::fs::read_to_string("./examples/psv/test.oox").unwrap();
    assert_eq!(
        verify(&file_content, "Main", "main", 30),
        SymResult::Invalid
    );
}

#[test]
fn sym_exec_div_by_n() {
    let file_content = std::fs::read_to_string("./examples/psv/divByN.oox").unwrap();
    // so this one is invalid at k = 100, in OOX it's invalid at k=105, due to exceptions (more if statements are added)
    assert_eq!(
        verify(&file_content, "Main", "divByN_invalid", 100),
        SymResult::Invalid
    );
}

#[test]
fn sym_exec_nonstatic_function() {
    let file_content = std::fs::read_to_string("./examples/nonstatic_function.oox").unwrap();
    assert_eq!(verify(&file_content, "Main", "f", 20), SymResult::Valid);
}

#[test]
fn sym_exec_this_method() {
    let file_content = std::fs::read_to_string("./examples/this_method.oox").unwrap();
    assert_eq!(verify(&file_content, "Main", "main", 30), SymResult::Valid);
}

#[test]
fn sym_exec_linked_list1() {
    let file_content = std::fs::read_to_string("./examples/intLinkedList.oox").unwrap();
    assert_eq!(verify(&file_content, "Node", "test2", 90), SymResult::Valid);
}

#[test]
fn sym_exec_linked_list1_invalid() {
    let file_content = std::fs::read_to_string("./examples/intLinkedList.oox").unwrap();
    assert_eq!(
        verify(&file_content, "Node", "test2_invalid", 90),
        SymResult::Invalid
    );
}

#[test]
fn sym_exec_linked_list3_invalid() {
    let file_content = std::fs::read_to_string("./examples/intLinkedList.oox").unwrap();
    // at k=80 it fails, after ~170 sec in hs oox, rs oox does this in ~90 sec
    assert_eq!(
        verify(&file_content, "Node", "test3_invalid1", 110),
        SymResult::Invalid
    );
}

#[test]
fn sym_exec_linked_list4() {
    let file_content = std::fs::read_to_string("./examples/intLinkedList.oox").unwrap();
    assert_eq!(verify(&file_content, "Node", "test4", 90), SymResult::Valid);
}

#[test]
fn sym_exec_linked_list4_invalid() {
    let file_content = std::fs::read_to_string("./examples/intLinkedList.oox").unwrap();
    assert_eq!(
        verify(&file_content, "Node", "test4_invalid", 90),
        SymResult::Invalid
    );
}

#[test]
fn sym_exec_linked_list4_if_problem() {
    let file_content = std::fs::read_to_string("./examples/intLinkedList.oox").unwrap();
    assert_eq!(
        verify(&file_content, "Node", "test4_if_problem", 90),
        SymResult::Valid
    );
}

#[test]
fn sym_exec_exceptions1() {
    let file_content = std::fs::read_to_string("./examples/exceptions.oox").unwrap();

    assert_eq!(verify(&file_content, "Main", "test1", 20), SymResult::Valid);
    assert_eq!(
        verify(&file_content, "Main", "test1_invalid", 20),
        SymResult::Invalid
    );
    assert_eq!(verify(&file_content, "Main", "div", 30), SymResult::Valid);
}

#[test]
fn sym_exec_exceptions_m0() {
    let file_content = std::fs::read_to_string("./examples/exceptions.oox").unwrap();

    assert_eq!(verify(&file_content, "Main", "m0", 20), SymResult::Valid);
    assert_eq!(
        verify(&file_content, "Main", "m0_invalid", 20),
        SymResult::Invalid
    );
}

#[test]
fn sym_exec_exceptions_m1() {
    let file_content = std::fs::read_to_string("./examples/exceptions.oox").unwrap();

    assert_eq!(verify(&file_content, "Main", "m1", 20), SymResult::Valid);
    assert_eq!(
        verify(&file_content, "Main", "m1_invalid", 20),
        SymResult::Invalid
    );
}

#[test]
fn sym_exec_exceptions_m2() {
    let file_content = std::fs::read_to_string("./examples/exceptions.oox").unwrap();

    assert_eq!(verify(&file_content, "Main", "m2", 20), SymResult::Valid);
}

#[test]
fn sym_exec_exceptions_m3() {
    let file_content = std::fs::read_to_string("./examples/exceptions.oox").unwrap();

    assert_eq!(verify(&file_content, "Main", "m3", 30), SymResult::Valid);
    assert_eq!(
        verify(&file_content, "Main", "m3_invalid1", 30),
        SymResult::Invalid
    );
    assert_eq!(
        verify(&file_content, "Main", "m3_invalid2", 30),
        SymResult::Invalid
    );
}

#[test]
fn sym_exec_exceptions_null() {
    let file_content = std::fs::read_to_string("./examples/exceptions.oox").unwrap();

    assert_eq!(
        verify(&file_content, "Main", "nullExc1", 30),
        SymResult::Valid
    );
    assert_eq!(
        verify(&file_content, "Main", "nullExc2", 30),
        SymResult::Valid
    );
    // assert_eq!(verify_file(&file_content, "m3_invalid1", 30), SymResult::Invalid);
    // assert_eq!(verify_file(&file_content, "m3_invalid2", 30), SymResult::Invalid);
}

#[test]
fn sym_exec_array1() {
    let file_content = std::fs::read_to_string("./examples/array/array1.oox").unwrap();

    assert_eq!(verify(&file_content, "Main", "foo", 50), SymResult::Valid);
    assert_eq!(
        verify(&file_content, "Main", "foo_invalid", 50),
        SymResult::Invalid
    );
    assert_eq!(verify(&file_content, "Main", "sort", 300), SymResult::Valid);
    assert_eq!(
        verify(&file_content, "Main", "sort_invalid1", 50),
        SymResult::Invalid
    );
    assert_eq!(verify(&file_content, "Main", "max", 50), SymResult::Valid);
    assert_eq!(
        verify(&file_content, "Main", "max_invalid1", 50),
        SymResult::Invalid
    );
    assert_eq!(
        verify(&file_content, "Main", "max_invalid2", 50),
        SymResult::Invalid
    );
    assert_eq!(
        verify(&file_content, "Main", "exists_valid", 50),
        SymResult::Valid
    );
    // assert_eq!(verify_file(&file_content, "exists_invalid1", 50), SymResult::Invalid);
    assert_eq!(
        verify(&file_content, "Main", "exists_invalid2", 50),
        SymResult::Invalid
    );
    assert_eq!(
        verify(&file_content, "Main", "array_creation1", 50),
        SymResult::Valid
    );
    assert_eq!(
        verify(&file_content, "Main", "array_creation2", 50),
        SymResult::Valid
    );
    assert_eq!(
        verify(&file_content, "Main", "array_creation_invalid", 50),
        SymResult::Invalid
    );
}

#[test]
fn sym_exec_array2() {
    let file_content = std::fs::read_to_string("./examples/array/array2.oox").unwrap();

    assert_eq!(verify(&file_content, "Main", "foo1", 50), SymResult::Valid);
    assert_eq!(
        verify(&file_content, "Main", "foo1_invalid", 50),
        SymResult::Invalid
    );
    assert_eq!(
        verify(&file_content, "Main", "foo2_invalid", 50),
        SymResult::Invalid
    );
    assert_eq!(verify(&file_content, "Main", "sort", 100), SymResult::Valid);
}

#[test]
fn sym_exec_inheritance() {
    let file_content = std::fs::read_to_string("./examples/inheritance/inheritance.oox").unwrap();
    let k = 150;

    assert_eq!(verify(&file_content, "Main", "test1", k), SymResult::Valid);
    assert_eq!(
        verify(&file_content, "Main", "test1_invalid", k),
        SymResult::Invalid
    );
    assert_eq!(verify(&file_content, "Main", "test2a", k), SymResult::Valid);

    assert_eq!(verify(&file_content, "Main", "test2b", k), SymResult::Valid);

    assert_eq!(
        verify(&file_content, "Main", "test2b_invalid", k),
        SymResult::Invalid
    );

    assert_eq!(verify(&file_content, "Main", "test3", k), SymResult::Valid);

    assert_eq!(
        verify(&file_content, "Main", "test4_valid", k),
        SymResult::Valid
    );
    assert_eq!(
        verify(&file_content, "Main", "test4_invalid", k),
        SymResult::Invalid
    );
    assert_eq!(verify(&file_content, "Main", "test5", k), SymResult::Valid);

    assert_eq!(verify(&file_content, "Main", "test6", k), SymResult::Valid);
}

#[test]
fn sym_exec_inheritance_specifications() {
    let file_content =
        std::fs::read_to_string("./examples/inheritance/specifications.oox").unwrap();
    let k = 150;
    assert_eq!(
        verify(&file_content, "Main", "test_valid", k),
        SymResult::Valid
    );
    assert_eq!(
        verify(&file_content, "Main", "test_invalid", k),
        SymResult::Invalid
    );
}

#[test]
fn sym_exec_interface() {
    let file_content = std::fs::read_to_string("./examples/inheritance/interface.oox").unwrap();
    let k = 150;

    println!("hello");

    assert_eq!(verify(&file_content, "Main", "main", k), SymResult::Valid);
    assert_eq!(verify(&file_content, "Main", "test1_valid", k), SymResult::Valid);
    assert_eq!(verify(&file_content, "Main", "test1_invalid", k), SymResult::Invalid);
}

#[test]
fn sym_exec_interface2() {
    let file_content = std::fs::read_to_string("./examples/inheritance/interface2.oox").unwrap();
    let k = 150;

    assert_eq!(verify(&file_content, "Foo", "test_valid", k), SymResult::Valid);
    assert_eq!(verify(&file_content, "Foo1", "test_invalid", k), SymResult::Invalid);
    assert_eq!(verify(&file_content, "Foo2", "test_valid", k), SymResult::Valid);
    assert_eq!(verify(&file_content, "Foo3", "test_invalid", k), SymResult::Invalid);
    //assert_eq!(verify(&file_content, "Foo4", "test_valid", k), SymResult::Valid);
}


#[test]
fn sym_exec_polymorphic() {
    let file_content =
        std::fs::read_to_string("./examples/inheritance/sym_exec_polymorphic.oox").unwrap();
    let k = 150;
    assert_eq!(
        verify(&file_content, "Main", "main", k),
        SymResult::Valid
    );
}