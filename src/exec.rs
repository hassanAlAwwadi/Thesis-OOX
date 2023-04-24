use core::panic;
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    ops::{AddAssign, Deref},
    rc::Rc,
    time::Instant,
};

use clap::ValueEnum;
use itertools::{Either, Itertools};
use num::One;
use slog::{debug, error, info, o, Logger};
use sloggers::{
    file::FileLoggerBuilder,
    terminal::{Destination, TerminalLoggerBuilder},
    types::Severity,
    Build,
};
use z3::SatResult;

use std::fmt::Debug;

mod heuristics;
mod invocation;
mod state_split;

use crate::{
    cfg::{labelled_statements, CFGStatement, MethodIdentifier},
    concretization::{concretizations, find_symbolic_refs},
    dsl::{equal, ite, negate, or, to_int_expr},
    eval::{self, evaluate, evaluate_as_int},
    exception_handler::{ExceptionHandlerEntry, ExceptionHandlerStack},
    language, parse_program,
    parser::parse,
    positioned::{SourcePos, WithPosition},
    stack::{StackFrame, Stack},
    statistics::Statistics,
    symbol_table::SymbolTable,
    syntax::{
        BinOp, Declaration, Expression, Identifier, Invocation, Lhs, Lit, Method, NonVoidType,
        Parameter, Reference, Rhs, RuntimeType, Statement,
    },
    typeable::{runtime_to_nonvoidtype, Typeable},
    typing::type_compilation_unit,
    utils, z3_checker, FILE_NAMES,
};

use crate::exec::state_split::exec_array_initialisation;

const NULL: Expression = Expression::Lit {
    lit: Lit::NullLit,
    type_: RuntimeType::ANYRuntimeType,
    info: SourcePos::UnknownPosition,
};

pub fn retval() -> Identifier {
    Identifier::with_unknown_pos("retval".to_string())
}

pub fn this_str() -> Identifier {
    Identifier::with_unknown_pos("this".to_owned())
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
pub type AliasMap = HashMap<Identifier, AliasEntry>;

#[derive(Debug, Clone, PartialEq, Eq)]
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

    fn current_value(&self) -> T {
        self.last_value.clone()
    }
}

#[derive(Clone)]
pub struct State {
    pc: u64,
    pub stack: Stack,
    pub heap: Heap,
    precondition: Expression,

    constraints: PathConstraints,
    pub alias_map: AliasMap,
    pub ref_counter: IdCounter<i64>,
    exception_handler: ExceptionHandlerStack,

    // logger and other (non-functional) metrics
    pub logger: Logger,
    path_length: u64,
    path_id: u64,
}

impl Debug for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("State")
            .field("pc", &self.pc)
            // .field("stack", &self.stack)
            // .field("heap", &self.heap)
            // .field("precondition", &self.precondition)
            // .field("constraints", &self.constraints)
            // .field("alias_map", &self.alias_map)
            // .field("ref_counter", &self.ref_counter)
            // .field("exception_handler", &self.exception_handler)
            // .field("logger", &self.logger)
            // .field("path_length", &self.path_length)
            // .field("path_id", &self.path_id)
            .finish()
    }
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
            info: SourcePos::UnknownPosition,
        });
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum SymResult {
    Valid,
    Invalid(SourcePos),
}

pub trait Engine {
    fn add_remaining_state(&mut self, state: State);

    fn add_remaining_states(&mut self, state: impl Iterator<Item = State>);

    /// Provides a unique path id, can be used when the state is split into a new path
    fn next_path_id(&mut self) -> u64;

    fn statistics(&mut self) -> &mut Statistics;

    fn symbol_table(&self) -> &SymbolTable;
}

pub struct DFSEngine<'a> {
    remaining_states: &'a mut Vec<State>,
    path_counter: Rc<RefCell<IdCounter<u64>>>,
    statistics: &'a mut Statistics,
    st: &'a SymbolTable,
}

impl Engine for DFSEngine<'_> {
    fn add_remaining_state(&mut self, state: State) {
        self.remaining_states.push(state);
    }

    fn add_remaining_states(&mut self, states: impl Iterator<Item = State>) {
        self.remaining_states.extend(states);
    }

    fn next_path_id(&mut self) -> u64 {
        self.path_counter.borrow_mut().next_id()
    }

    fn statistics(&mut self) -> &mut Statistics {
        self.statistics
    }

    fn symbol_table(&self) -> &SymbolTable {
        self.st
    }
}

/// Initialises an array by creating a concrete array of size array_size in the heap, symbolic objects are initialised lazily.
/// The resulting state has a single concrete array (or null) in its alias map.
fn array_initialisation(
    state: &mut State,
    array_name: &Identifier,
    array_size: u64,
    array_type: RuntimeType,
    inner_type: RuntimeType,
    st: &SymbolTable,
) {
    let r = state.next_reference_id();

    state.alias_map.insert(
        array_name.clone(),
        AliasEntry::new(vec![Rc::new(Expression::Ref {
            ref_: r,
            type_: array_type.clone(),
            info: SourcePos::UnknownPosition,
        })]),
    );

    let array_elements = (0..array_size)
        .map(|i| {
            create_symbolic_var(
                format!("{}{}", array_name, i).into(),
                inner_type.clone(),
                st,
            )
            .into()
        })
        .collect();

    state.heap.insert(
        r,
        HeapValue::ArrayValue {
            elements: array_elements,
            type_: array_type.clone(),
        }
        .into(),
    );

    // dbg!("after array initialization", &state.heap, &state.alias_map);
}

enum ActionResult {
    /// Statement executed, continue
    Continue,
    Return(u64),
    FunctionCall(u64),
    InvalidAssertion(SourcePos),
    InfeasiblePath,
    Finish,
}

/// Execute one statement for one state
fn action(
    state: &mut State,
    program: &HashMap<u64, CFGStatement>,
    k: u64,
    en: &mut impl Engine,
) -> ActionResult {
    let pc = state.pc;
    let action = &program[&pc];

    //use language::prettyprint::cfg_pretty;

    debug!(state.logger, "Action {}", action;
     "stack" => ?state.stack.current_stackframe(),
     "heap" => ?state.heap,
     "alias_map" => ?state.alias_map
    );

    // dbg!(
    //     &state.path_id,
    //     &action,
    //     state.stack.last().map(|s| &s.params),
    //     &state.heap,
    //     &state.alias_map,
    //     // &state.pc,
    //     // &state.path_length,
    // );

    match action {
        CFGStatement::Statement(Statement::Declare { type_, var, info }) => {
            state.stack.insert_variable(var.clone(), Rc::new(type_.default()));

            ActionResult::Continue
        }
        CFGStatement::Statement(Statement::Assign { lhs, rhs, info }) => {
            // RhsCall 'x.foo()' has a special case,
            // others are handled in evaluateRhs
            match rhs {
                Rhs::RhsCall {
                    invocation,
                    type_,
                    info,
                } => {
                    // if rhs contains an invocation.
                    return exec_invocation(state, invocation, &program, pc, Some(lhs.clone()), en);
                }
                _ => (),
            }

            let value = evaluate_rhs(state, rhs, en);
            let e = evaluate(state, value, en);

            execute_assign(state, lhs, e, en);

            ActionResult::Continue
        }
        CFGStatement::Statement(Statement::Assert { assertion, .. }) => {
            let expression = prepare_assert_expression(state, Rc::new(assertion.clone()), en);

            let is_valid = eval_assertion(state, expression, en);
            if !is_valid {
                return ActionResult::InvalidAssertion(assertion.get_position());
            }
            ActionResult::Continue
        }
        CFGStatement::Statement(Statement::Assume { assumption, .. }) => {
            let is_feasible_path = exec_assume(state, Rc::new(assumption.clone()), en);
            if !is_feasible_path {
                return ActionResult::InfeasiblePath;
            }
            ActionResult::Continue
        }
        CFGStatement::Statement(Statement::Return { expression, .. }) => {
            if let Some(expression) = expression {
                let expression = evaluate(state, Rc::new(expression.clone()), en);
                state.stack.insert_variable(retval(), expression);
            }
            ActionResult::Continue
        }
        CFGStatement::FunctionEntry { .. } => {
            // only check preconditions when it's the first method called??
            // we assume that the previous stackframe is of this method
            let StackFrame { current_member, .. } = state.stack.current_stackframe().unwrap();
            if let Some(requires) = current_member.requires() {
                // if this is the program entry, assume that require is true, otherwise assert it.
                if (state.path_length == 0) {
                    let expression = evaluate(state, requires, en);

                    if *expression == false_lit() {
                        println!("Constraint is infeasible");
                        return ActionResult::InfeasiblePath;
                    } else if *expression != true_lit() {
                        state.constraints.insert(expression.deref().clone());
                    }
                } else {
                    // Assert that requires is true
                    let assertion = prepare_assert_expression(state, requires.clone(), en);
                    let is_valid = eval_assertion(state, assertion.clone(), en);
                    if !is_valid {
                        return ActionResult::InvalidAssertion(requires.get_position());
                    }
                    state.constraints.insert(requires.deref().clone());
                }
            }

            ActionResult::Continue
        }
        CFGStatement::FunctionExit {
            decl_name,
            method_name,
            argument_types,
        } => {
            state.exception_handler.decrement_handler();

            let StackFrame {
                current_member,
                params,
                ..
            } = state.stack.current_stackframe().unwrap();
            if let Some(post_condition) = current_member.post_condition() {
                let expression = prepare_assert_expression(state, post_condition.clone(), en);
                let is_valid = eval_assertion(state, expression, en);
                if !is_valid {
                    // postcondition invalid
                    return ActionResult::InvalidAssertion(post_condition.get_position());
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
                        let return_value = evaluate(state, rv.clone(), en);

                        // perhaps also write retval to current stack?
                        // will need to do this due to this case: `return o.func();`

                        execute_assign(state, &lhs, return_value, en);
                    }
                }

                ActionResult::Return(pc)
            }
        }
        CFGStatement::Statement(Statement::Call { invocation, info }) => {
            exec_invocation(state, invocation, &program, pc, None, en)
        }
        CFGStatement::Statement(Statement::Throw { message, .. }) => exec_throw(state, en, message),
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

fn exec_throw(state: &mut State, en: &mut impl Engine, message: &str) -> ActionResult {
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
                let assertion = prepare_assert_expression(state, exceptional.clone(), en);
                //dbg!(&assertion);
                let is_valid = eval_assertion(state, assertion.clone(), en);
                if !is_valid {
                    error!(state.logger, "Exceptional error: {:?}", message);
                    return ActionResult::InvalidAssertion(exceptional.get_position());
                }
            }
            current_depth -= 1;
        }

        ActionResult::Return(catch_pc)
    } else {
        while let Some(stack_frame) = state.stack.current_stackframe() {
            if let Some(exceptional) = stack_frame.current_member.exceptional() {
                let assertion = prepare_assert_expression(state, exceptional.clone(), en);
                //dbg!(&assertion);
                let is_valid = eval_assertion(state, assertion.clone(), en);
                if !is_valid {
                    error!(state.logger, "Exceptional error: {:?}", message);
                    return ActionResult::InvalidAssertion(exceptional.get_position());
                }
            }
            state.stack.pop();
        }
        // Throw exception path explored, but is valid so we can prune this path.
        ActionResult::Finish
    }
}

fn eval_assertion(state: &mut State, expression: Rc<Expression>, en: &mut impl Engine) -> bool {
    // dbg!("invoke Z3 with:", &expression);
    // dbg!(&alias_map);
    en.statistics().measure_veficiation();

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
            // This introduces branching in computation for each concretization proposed:
            en.statistics().measure_branches(expressions.len() as u32);
            // dbg!(&expressions);

            for expression in expressions {
                let expression = evaluate(state, expression, en);
                if *expression == true_lit() {
                    // Invalid
                    en.statistics().measure_local_solve();
                    return false;
                } else if *expression == false_lit() {
                    // valid, continue
                    en.statistics().measure_local_solve();
                } else {
                    en.statistics().measure_invoke_z3();
                    let result = z3_checker::verify(&expression);
                    if let SatResult::Unsat = result {
                        // valid, continue
                    } else {
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
    en: &mut impl Engine,
) -> ActionResult {
    // dbg!(invocation);

    debug!(state.logger, "Invocation"; "invocation" => %invocation);

    state.exception_handler.increment_handler();

    let argument_types = invocation
        .arguments()
        .iter()
        .map(AsRef::as_ref)
        .map(Typeable::type_of);

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
                    en,
                );
                return ActionResult::FunctionCall(next_entry);
            } else {
                // dbg!(invocation_lhs);

                return invocation::multiple_method_invocation(
                    state,
                    invocation_lhs,
                    invocation,
                    potential_methods,
                    return_point,
                    lhs,
                    program,
                    en,
                );
            }
        }
        Invocation::InvokeConstructor {
            resolved,
            class_name,
            ..
        } => {
            let (declaration, method): &(Declaration, Rc<Method>) = resolved
                .as_ref()
                .map(AsRef::as_ref)
                .unwrap_or_else(|| panic!("Unresolved constructor for class {}", class_name));
            let class_name = declaration.name();
            // evaluate arguments
            let arguments = invocation
                .arguments()
                .into_iter()
                .map(|arg| evaluate(state, arg.clone(), en))
                .collect::<Vec<_>>();

            let this_param = Parameter::new(
                NonVoidType::ReferenceType {
                    identifier: class_name.clone(),
                    info: SourcePos::UnknownPosition,
                },
                this_str(),
            );
            exec_constructor(
                state,
                return_point,
                method.clone(),
                lhs,
                &arguments,
                class_name,
                en,
                this_param,
            );

            let next_entry = find_entry_for_static_invocation(
                &class_name,
                &method.name,
                argument_types,
                program,
                en.symbol_table(),
            );
            ActionResult::FunctionCall(next_entry)
        }
        Invocation::InvokeSuperConstructor { resolved, .. } => {
            let (declaration, method) = resolved
                .as_ref()
                .map(AsRef::as_ref)
                .expect("super constructor call not resolved");
            let class_name = declaration.name();

            // evaluate arguments
            let arguments = invocation
                .arguments()
                .into_iter()
                .map(|arg| evaluate(state, arg.clone(), en))
                .collect::<Vec<_>>();

            let this_param = Parameter::new(
                NonVoidType::ReferenceType {
                    identifier: class_name.clone(),
                    info: SourcePos::UnknownPosition,
                },
                this_str(),
            );
            exec_super_constructor(
                state,
                return_point,
                method.clone(),
                lhs,
                &arguments,
                &method.params,
                en,
                this_param,
            );
            let next_entry = find_entry_for_static_invocation(
                &class_name,
                &method.name,
                argument_types,
                program,
                en.symbol_table(),
            );
            ActionResult::FunctionCall(next_entry)
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
                en,
            );
            return ActionResult::FunctionCall(next_entry);
        }
        // (_, DeclarationMember::Field { type_, name }) => todo!(),
        _ => panic!("Incorrect pair of Invocation and DeclarationMember"),
    }
}

/// Given a class name and method name, lookup the entry node in the Control Flow Graph
/// Also checks if the argument types are consistent.
/// Panics if the method is not found
pub fn find_entry_for_static_invocation(
    class_name: &str,
    method_name: &str,
    argument_types: impl ExactSizeIterator<Item = RuntimeType> + Clone,
    program: &HashMap<u64, CFGStatement>,
    st: &SymbolTable,
) -> u64 {
    // dbg!(invocation);
    let (entry, _) = program
        .iter()
        .find(|(k, v)| {
            if let CFGStatement::FunctionEntry {
                decl_name: other_decl_name,
                method_name: other_method_name,
                argument_types: other_argument_types,
            } = *v
            {
                let mut argument_types_match = argument_types
                    .clone()
                    .zip(other_argument_types)
                    .map(|(a, b)| a.is_of_type(b, st));
                *other_decl_name == class_name
                    && *other_method_name == method_name
                    && argument_types.len() == other_argument_types.len()
                    && argument_types_match.all_equal()
            } else {
                false
            }
        })
        .unwrap_or_else(|| panic!("Could not find the method {}.{}({:?})", class_name, method_name, argument_types.clone().collect_vec()));

    *entry
}

fn exec_method(
    state: &mut State,
    return_point: u64,
    method: Rc<Method>,
    lhs: Option<Lhs>,
    arguments: &[Rc<Expression>],
    en: &mut impl Engine,
    this: (RuntimeType, Identifier),
) {
    let this_param = Parameter::new(
        runtime_to_nonvoidtype(this.0.clone()).expect("concrete, nonvoid type"),
        this_str(),
    );

    let this_expr = Expression::Var {
        var: this.1.clone(),
        type_: this.0,
        info: method.info,
    };
    let parameters = std::iter::once(&this_param).chain(method.params.iter());
    let arguments = std::iter::once(Rc::new(this_expr)).chain(arguments.iter().cloned());

    push_stack_frame(
        state,
        return_point,
        method.clone(),
        lhs,
        parameters.zip(arguments),
        en,
    )
}

fn exec_static_method(
    state: &mut State,
    return_point: u64,
    member: Rc<Method>,
    lhs: Option<Lhs>,
    arguments: &[Rc<Expression>],
    parameters: &[Parameter],
    en: &mut impl Engine,
) {
    push_stack_frame(
        state,
        return_point,
        member,
        lhs,
        parameters.iter().zip(arguments.iter().cloned()),
        en,
    )
}

fn exec_constructor(
    state: &mut State,
    return_point: u64,
    method: Rc<Method>,
    lhs: Option<Lhs>,
    arguments: &[Rc<Expression>],
    class_name: &Identifier,
    en: &mut impl Engine,
    this_param: Parameter,
) {
    let parameters = std::iter::once(&this_param).chain(method.params.iter());

    let fields = en
        .symbol_table()
        .get_all_fields(class_name)
        .iter()
        .map(|(s, t)| (s.clone(), t.default().into()))
        .collect();
    let structure = HeapValue::ObjectValue {
        fields,
        type_: method.type_of(),
    };

    let object_ref = state.allocate_on_heap(structure);
    let arguments = std::iter::once(object_ref).chain(arguments.iter().cloned());

    push_stack_frame(
        state,
        return_point,
        method.clone(),
        lhs,
        parameters.zip(arguments),
        en,
    )
}

fn exec_super_constructor(
    state: &mut State,
    return_point: u64,
    method: Rc<Method>,
    lhs: Option<Lhs>,
    arguments: &[Rc<Expression>],
    parameters: &[Parameter],
    en: &mut impl Engine,
    this_param: Parameter,
) {
    let parameters = std::iter::once(&this_param).chain(parameters.iter());

    // instead of allocating a new object, add the new fields to the existing 'this' object.
    let object_ref = state.stack.lookup(&this_str())
        .expect("super() is called in a constructor with a 'this' object on the stack");
    let arguments = std::iter::once(object_ref).chain(arguments.iter().cloned());

    push_stack_frame(
        state,
        return_point,
        method,
        lhs,
        parameters.zip(arguments),
        en,
    )
}

fn push_stack_frame<'a, P>(
    state: &mut State,
    return_point: u64,
    method: Rc<Method>,
    lhs: Option<Lhs>,
    params: P,
    en: &mut impl Engine,
) where
    P: Iterator<Item = (&'a Parameter, Rc<Expression>)>,
{
    let params = params
        .map(|(p, e)| (p.name.clone(), evaluate(state, e, en)))
        .collect();
    let stack_frame = StackFrame {
        pc: return_point,
        t: lhs,
        params,
        current_member: method,
    };
    state.stack.push(stack_frame);
}

fn prepare_assert_expression(
    state: &mut State,
    assertion: Rc<Expression>,
    en: &mut impl Engine,
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
                info: SourcePos::UnknownPosition,
            })
            .unwrap();

        negate(Rc::new(Expression::BinOp {
            bin_op: BinOp::Implies,
            lhs: Rc::new(assumptions),
            rhs: assertion,
            type_: RuntimeType::BoolRuntimeType,
            info: SourcePos::UnknownPosition,
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
    let z = evaluate(state, Rc::new(expression), en);
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
                        info: SourcePos::UnknownPosition,
                    }),
                    true_: (read_field_concrete_ref(heap, ref_, &field)),
                    false_: (read_field_symbolic_ref(heap, rs, sym_ref, field)),
                    type_: RuntimeType::ANYRuntimeType,
                    info: SourcePos::UnknownPosition,
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
                if let Expression::Ref { ref_, type_, .. } = r.as_ref() {
                    let ite = ite(
                        equal(sym_ref.clone(), r.clone()),
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
        info: SourcePos::UnknownPosition,
    }
}

/// Initialise a symbolic object reference.
pub fn init_symbolic_reference(
    state: &mut State,
    sym_ref: &Identifier,
    type_ref: &RuntimeType,
    en: &mut impl Engine,
) {
    if !state.alias_map.contains_key(sym_ref) {
        debug!(state.logger, "Lazy initialisation of symbolic reference"; "ref" => #?sym_ref, "type" => #?type_ref);
        match type_ref {
            RuntimeType::ReferenceRuntimeType { type_ } => {
                init_symbolic_object(type_, state, sym_ref, type_ref, en)
            }
            RuntimeType::ArrayRuntimeType { .. } => {
                exec_array_initialisation(state, en, sym_ref.clone(), type_ref.clone())
            }
            _ => panic!("Cannot initialize type {:?}", type_ref),
        };

        debug!(state.logger, "Updated aliasentry"; "alias_map" => #?state.alias_map);
    }
}

fn init_symbolic_object(
    decl_name: &Identifier,
    state: &mut State,
    sym_ref: &Identifier,
    type_ref: &RuntimeType,
    en: &mut impl Engine,
) {
    let st = en.symbol_table();
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
                            st,
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
                let ref_type = match type_ {
                    RuntimeType::ReferenceRuntimeType { type_ } => type_,
                    RuntimeType::ArrayRuntimeType { .. } => return None, // arrays cannot have the same type as objects, skip
                    _ => panic!("expected reference type"),
                };

                if instance_types.contains(&ref_type) {
                    Some(Either::Left(x.aliases.iter()))
                } else {
                    None
                }
            } else {
                Some(Either::Right(
                    x.aliases.iter().filter(|x| if let Some(ref_type) = x.type_of().as_reference_type() {
                        instance_types.contains(ref_type)
                    } else {
                        // null
                        false
                    },
                )))
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
}

fn execute_assign(state: &mut State, lhs: &Lhs, e: Rc<Expression>, en: &mut impl Engine) {
    // let st = en.symbol_table();
    match lhs {
        Lhs::LhsVar { var, .. } => {
            state.stack.insert_variable(var.clone(), e);
        }
        Lhs::LhsField {
            var,
            var_type,
            field,
            type_,
            info,
        } => {
            let o = state.stack.lookup(var).unwrap_or_else(|| panic!("infeasible, object does not exit"));

            match o.as_ref() {
                Expression::Ref { ref_, type_, .. } => {
                    write_field_concrete_ref(&mut state.heap, *ref_, field, e);
                }
                sym_ref @ Expression::SymbolicRef { var, type_, .. } => {
                    init_symbolic_reference(state, &var, &type_, en);
                    // should also remove null here? --Assignemnt::45
                    // Yes, we have if (x = null) { throw; } guards that ensure it cannot be null
                    remove_symbolic_null(&mut state.alias_map, &var);
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
                Expression::Conditional {
                    guard,
                    true_,
                    false_,
                    ..
                } => {
                    state_split::conditional_state_split(
                        state,
                        en,
                        guard.clone(),
                        true_.clone(),
                        false_.clone(),
                        var.clone(),
                    );
                    return execute_assign(state, lhs, e, en);
                }

                _ => todo!("{:?}", o.as_ref()),
            }
        }
        Lhs::LhsElem {
            var,
            index,
            type_,
            info,
        } => {
            let ref_ = state.stack.lookup(var).unwrap_or_else(|| panic!("infeasible, array does not exit"));

            let ref_ = single_alias_elimination(ref_, &state.alias_map);

            match ref_.as_ref() {
                Expression::Ref { ref_, type_, .. } => {
                    let index = evaluate_as_int(state, index.clone(), en);

                    match index {
                        Either::Left(index) => write_elem_symbolic_index(state, *ref_, index, e),
                        Either::Right(i) => write_elem_concrete_index(state, *ref_, i, e),
                    }
                }
                _ => panic!("expected array ref, found expr {:?}", &ref_),
            }
        }
    }
}

// fn evaluateRhs(state: &mut State, rhs: &Rhs) -> Expression {
fn evaluate_rhs(state: &mut State, rhs: &Rhs, en: &mut impl Engine) -> Rc<Expression> {
    match rhs {
        Rhs::RhsExpression { value, .. } => {
            match value {
                Expression::Var { var, .. } => state.stack.lookup(var)
                    .unwrap_or_else(|| {
                        panic!(
                            "Could not find {:?} on the stack {:?}",
                            var,
                            &state.stack.current_variables()
                        )
                    }),
                _ => Rc::new(value.clone()), // might have to expand on this when dealing with complex quantifying expressions and array
            }
        }
        Rhs::RhsField {
            var, field, type_, ..
        } => {
            if let Expression::Var { var, .. } = var {
                let object = state.stack.lookup(var).unwrap();
                exec_rhs_field(state, &object, field, type_, en)
            } else {
                panic!(
                    "Currently only right hand sides of the form <variable>.<field> are allowed."
                )
            }
        }
        // We expect that this symbolic reference has been initialised into multiple states,
        // where in each state the aliasmap is left with one concrete array.
        Rhs::RhsElem {
            var, index, ..
        } => {
            if let Expression::Var { var, .. } = var {
                let array = state.stack.lookup(var).unwrap();
                exec_rhs_elem(state, array, index.to_owned().into(), en)
            } else {
                panic!("Unexpected uninitialized array");
            }
        }
        Rhs::RhsCall {
            invocation, type_, ..
        } => {
            unreachable!("unreachable, invocations are handled in function exec_invocation()")
        }

        Rhs::RhsArray {
            array_type,
            sizes,
            type_,
            ..
        } => {
            return exec_array_construction(state, array_type, sizes, type_, en);
        }
        _ => unimplemented!(),
    }
}

fn exec_rhs_field(
    state: &mut State,
    object: &Expression,
    field: &Identifier,
    type_: &RuntimeType,
    en: &mut impl Engine,
) -> Rc<Expression> {
    match object {
        Expression::Conditional {
            guard,
            true_,
            false_,
            type_,
            info,
        } => {
            let true_ = exec_rhs_field(state, true_, field, type_, en);
            let false_ = exec_rhs_field(state, false_, field, type_, en);

            Rc::new(Expression::Conditional {
                guard: guard.clone(),
                true_: true_,
                false_: false_,
                type_: type_.clone(),
                info: *info,
            })
        }
        Expression::Lit {
            lit: Lit::NullLit, ..
        } => panic!("infeasible"),
        Expression::Ref { ref_, type_, info } => {
            read_field_concrete_ref(&mut state.heap, *ref_, field)
        }
        sym_ref @ Expression::SymbolicRef { var, type_, info } => {
            init_symbolic_reference(state, var, type_, en);
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
    en: &mut impl Engine,
) -> Rc<Expression> {
    let array = single_alias_elimination(array, &state.alias_map);
    match array.as_ref() {
        Expression::Ref { ref_, .. } => {
            let index = evaluate_as_int(state, index, en);
            match index {
                Either::Left(index) => read_elem_symbolic_index(state, *ref_, index),
                Either::Right(index) => read_elem_concrete_index(state, *ref_, index),
            }
        }
        _ => {
            panic!("expected array ref, found expr {:?}", &array)
        }
    }
}

fn true_lit() -> Expression {
    Expression::Lit {
        lit: Lit::BoolLit { bool_value: true },
        type_: RuntimeType::BoolRuntimeType,
        info: SourcePos::UnknownPosition,
    }
}

fn false_lit() -> Expression {
    Expression::Lit {
        lit: Lit::BoolLit { bool_value: false },
        type_: RuntimeType::BoolRuntimeType,
        info: SourcePos::UnknownPosition,
    }
}

fn remove_symbolic_null(alias_map: &mut AliasMap, var: &Identifier) {
    // dbg!(&alias_map, &var);
    alias_map.get_mut(var).unwrap().remove_null(var)
}

fn create_symbolic_var(name: Identifier, type_: impl Typeable, st: &SymbolTable) -> Expression {
    if type_.is_of_type(RuntimeType::REFRuntimeType, st) {
        Expression::SymbolicRef {
            var: name,
            type_: type_.type_of(),
            info: SourcePos::UnknownPosition,
        }
    } else {
        Expression::SymbolicVar {
            var: name,
            type_: type_.type_of(),
            info: SourcePos::UnknownPosition,
        }
    }
}

/// Create uninitialised variable (that can be initialized lazily)
fn initialize_symbolic_var(
    name: &str,
    type_: &RuntimeType,
    ref_: i64,
    st: &SymbolTable,
) -> Expression {
    let sym_name = format!("{}{}", name, ref_);
    create_symbolic_var(sym_name.into(), type_.clone(), st)
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
        let indices = (0..elements.len()).map(|i| to_int_expr(i as i64));

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
        let indices = (0..elements.len()).map(|i| to_int_expr(i as i64));

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
    en: &mut impl Engine,
) -> Rc<Expression> {
    let ref_id = state.next_reference_id();

    assert!(sizes.len() == 1, "Support for only 1D arrays");
    // int[][] a = new int[10][10];

    let size = evaluate_as_int(state, Rc::new(sizes[0].clone()), en)
        .expect_right("no symbolic array sizes");

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
        info: SourcePos::UnknownPosition,
    })
}

/// Helper function, does not invoke Z3 but tries to evaluate the assumption locally.
/// Returns whether the assumption was found to be infeasible.
/// Otherwise it inserts the assumption into the constraints.
fn exec_assume(state: &mut State, assumption: Rc<Expression>, en: &mut impl Engine) -> bool {
    let expression = evaluate(state, assumption, en);

    if *expression == false_lit() {
        return false;
    } else if *expression != true_lit() {
        state.constraints.insert(expression.deref().clone());
    }
    true
}

/// Checks whether there is only one alias for the given symbolic reference, if so return the alias otherwise return the expression.
/// A single alias occurs for example when an array is initialised, split into multiple paths each with a different array size
pub(crate) fn single_alias_elimination(
    expr: Rc<Expression>,
    alias_map: &AliasMap,
) -> Rc<Expression> {
    if let Expression::SymbolicRef { var, .. } = expr.as_ref() {
        let alias = &alias_map[var];
        if alias.aliases.len() == 1 {
            return alias.aliases[0].clone();
        }
    }
    expr
}

pub type Error = String;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Heuristic {
    DepthFirstSearch,
    RandomPath,
    MinDist2Uncovered,
}

#[derive(Copy, Clone)]
pub struct Options {
    pub k: u64,
    pub quiet: bool,
    pub with_exceptional_clauses: bool,
    pub heuristic: Heuristic,
}

impl Options {
    fn default_with_k(k: u64) -> Options {
        Options {
            k,
            quiet: false,
            with_exceptional_clauses: true,
            heuristic: Heuristic::DepthFirstSearch,
        }
    }

    fn default_with_k_and_heuristic(k: u64, heuristic: Heuristic) -> Options {
        Options {
            k,
            quiet: false,
            with_exceptional_clauses: true,
            heuristic: heuristic,
        }
    }
}

pub fn verify(
    path: &str,
    class_name: &str,
    method_name: &str,
    options: Options,
) -> std::result::Result<SymResult, Error> {
    let start = Instant::now();
    if !options.quiet {
        println!("Starting up");
    }

    let file_content = std::fs::read_to_string(path).map_err(|err| err.to_string())?;

    // Set global file names
    *FILE_NAMES.lock().unwrap() = path.to_string();

    let c =
        parse_program(&file_content, options.with_exceptional_clauses).map_err(
            |error| match error {
                language::Error::ParseError(err) => err.to_string(),
                language::Error::LexerError((line, col)) => {
                    format!("Lexer error at {}:{}:{}", path.to_string(), line, col)
                }
            },
        )?;

    // dbg!(&c);
    if !options.quiet {
        println!("Parsing completed");
    }

    let initial_method = c
        .find_class_declaration_member(method_name, class_name.into())
        .ok_or_else(|| {
            format!(
                "Could not find method '{}' in class '{}'",
                method_name, class_name
            )
        })?;

    let symbol_table = SymbolTable::from_ast(&c)?;
    if !options.quiet {
        println!("Symbol table completed");
    }

    let c = type_compilation_unit(c, &symbol_table)?;
    if !options.quiet {
        println!("Typing completed");
    }

    let (result, flw) = labelled_statements(c);

    let program = result.into_iter().collect();

    // dbg!(&program);

    let flows: HashMap<u64, Vec<u64>> = utils::group_by(flw.into_iter());

    // dbg!(&flows);
    // panic!();
    let argument_types = initial_method
        .params
        .iter()
        .map(Typeable::type_of)
        .collect();

    let entry_method = MethodIdentifier {
        decl_name: class_name,
        method_name: method_name,
        arg_list: argument_types,
    };

    let pc = find_entry_for_static_invocation(
        entry_method.decl_name,
        entry_method.method_name,
        entry_method.arg_list.iter().cloned(),
        &program,
        &symbol_table,
    );
    // dbg!(&params);
    let params = initial_method
        .params
        .iter()
        .map(|p| {
            (
                p.name.clone(),
                Rc::new(create_symbolic_var(
                    p.name.clone(),
                    p.type_.type_of(),
                    &symbol_table,
                )),
            )
        })
        .collect();
    // dbg!(&params);

    // let root_logger = slog::Logger::root(
    //     Mutex::new(slog_bunyan::default(std::io::stderr()).filter_level(Level::Debug)).fuse(),
    //     o!(),
    // );
    let mut builder = FileLoggerBuilder::new("logs");
    // let mut builder = TerminalLoggerBuilder::new();
    // builder.destination(Destination::Stdout);
    builder.level(Severity::Debug);
    builder.format(sloggers::types::Format::Full);
    builder.source_location(sloggers::types::SourceLocation::FileAndLine);

    let root_logger = builder.build().unwrap();

    let state = State {
        pc,
        stack: Stack::new(vec![StackFrame {
            pc,
            t: None,
            params,
            current_member: initial_method,
        }]),
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
    let mut statistics = Statistics::default();

    // Choose between heuristic function (with matching parameters)
    let sym_exec = match options.heuristic {
        Heuristic::DepthFirstSearch => heuristics::depth_first_search::sym_exec,
        Heuristic::RandomPath => heuristics::random_path::sym_exec,
        Heuristic::MinDist2Uncovered => heuristics::min_dist_to_uncovered::sym_exec,
    };
    let sym_result = sym_exec(
        state,
        &program,
        &flows,
        options.k,
        &symbol_table,
        root_logger,
        path_counter.clone(),
        &mut statistics,
        entry_method,
    );

    let duration = start.elapsed();

    let result_text = match sym_result {
        SymResult::Valid => "VALID".to_string(),
        SymResult::Invalid(SourcePos::SourcePos { line, col }) => {
            format!("INVALID at {}:{}:{}", path, line, col)
        }
        SymResult::Invalid(SourcePos::UnknownPosition) => "INVALID at unknown position".to_string(),
    };

    if options.quiet && sym_result != SymResult::Valid {
        println!("{}", result_text);
    } else if !options.quiet {
        println!("Statistics");
        println!("  Final result:     {}", result_text);
        println!("  time:             {:?}s", duration.as_secs_f64());
        println!("  #branches:        {}", statistics.number_of_branches);
        println!("  #prunes:          {}", statistics.number_of_prunes);
        println!(
            "  #complete_paths:  {}",
            statistics.number_of_complete_paths
        );
        println!("  #locally_solved:  {}", statistics.number_of_local_solves);
        println!(
            "  #Z3 invocations:  {}",
            statistics.number_of_z3_invocations
        );
        println!(
            "  #paths explored:  {}",
            path_counter.borrow().current_value()
        );
    }

    return Ok(sym_result);
}

#[test]
fn sym_exec_of_absolute_simplest() {
    let path = "./examples/absolute_simplest.oox";
    let options = Options::default_with_k(20);
    assert_eq!(verify(path, "Foo", "f", options).unwrap(), SymResult::Valid);
}

#[test]
fn sym_exec_min() {
    let path = "./examples/psv/min.oox";
    assert_eq!(
        verify(path, "Foo", "min", Options::default_with_k(20)).unwrap(),
        SymResult::Valid
    );
}

#[test]
fn sym_exec_method() {
    let path = "./examples/psv/method.oox";
    assert_eq!(
        verify(path, "Main", "min", Options::default_with_k(20)).unwrap(),
        SymResult::Valid
    );
}

// #[test]
// fn sym_exec_fib() {
//     let file_content = std::fs::read_to_string("./examples/psv/fib.oox").unwrap();
//     assert_eq!(verify(&file_content, "Main", "main", 50), SymResult::Valid);
// }


#[test]
fn sym_exec_div_by_n() {
    let path = "./examples/psv/divByN.oox";
    // so this one is invalid at k = 100, in OOX it's invalid at k=105, due to exceptions (more if statements are added)
    assert_eq!(
        verify(
            &path,
            "Main",
            "divByN_invalid",
            Options::default_with_k(100)
        )
        .unwrap(),
        SymResult::Invalid(SourcePos::new(73, 16))
    );
}

#[test]
fn sym_exec_nonstatic_function() {
    let path = "./examples/nonstatic_function.oox";
    assert_eq!(
        verify(&path, "Main", "f", Options::default_with_k(20)).unwrap(),
        SymResult::Valid
    );
}

#[test]
fn sym_exec_this_method() {
    let path = "./examples/this_method.oox";
    assert_eq!(
        verify(&path, "Main", "main", Options::default_with_k(30)).unwrap(),
        SymResult::Valid
    );
}

#[test]
fn sym_exec_linked_list1() {
    let path = "./examples/intLinkedList.oox";
    assert_eq!(
        verify(&path, "Node", "test2", Options::default_with_k(90)).unwrap(),
        SymResult::Valid
    );
}

#[test]
fn sym_exec_linked_list1_invalid() {
    let path = "./examples/intLinkedList.oox";
    assert_eq!(
        verify(&path, "Node", "test2_invalid", Options::default_with_k(90)).unwrap(),
        SymResult::Invalid(SourcePos::new(109, 16))
    );
}

#[test]
fn sym_exec_linked_list3_invalid() {
    let path = "./examples/intLinkedList.oox";
    // at k=80 it fails, after ~170 sec in hs oox, rs oox does this in ~90 sec
    assert_eq!(
        verify(
            &path,
            "Node",
            "test3_invalid1",
            Options::default_with_k(110)
        )
        .unwrap(),
        SymResult::Invalid(SourcePos::new(141, 18))
    );
}

#[test]
fn sym_exec_linked_list4() {
    let path = "./examples/intLinkedList.oox";
    assert_eq!(
        verify(&path, "Node", "test4", Options::default_with_k(90)).unwrap(),
        SymResult::Valid
    );
}

#[test]
fn sym_exec_linked_list4_invalid() {
    let path = "./examples/intLinkedList.oox";
    assert_eq!(
        verify(&path, "Node", "test4_invalid", Options::default_with_k(90)).unwrap(),
        SymResult::Invalid(SourcePos::new(11, 21))
    );
}

#[test]
fn sym_exec_linked_list4_if_problem() {
    let path = "./examples/intLinkedList.oox";
    assert_eq!(
        verify(
            &path,
            "Node",
            "test4_if_problem",
            Options::default_with_k(90)
        )
        .unwrap(),
        SymResult::Valid
    );
}

#[test]
fn sym_exec_exceptions1() {
    let path = "./examples/exceptions.oox";

    assert_eq!(
        verify(&path, "Main", "test1", Options::default_with_k(20)).unwrap(),
        SymResult::Valid
    );
    assert_eq!(
        verify(&path, "Main", "test1_invalid", Options::default_with_k(20)).unwrap(),
        SymResult::Invalid(SourcePos::new(15, 21))
    );
    assert_eq!(
        verify(&path, "Main", "div", Options::default_with_k(30)).unwrap(),
        SymResult::Valid
    );
}

#[test]
fn sym_exec_exceptions_m0() {
    let path = "./examples/exceptions.oox";

    assert_eq!(
        verify(&path, "Main", "m0", Options::default_with_k(20)).unwrap(),
        SymResult::Valid
    );
    assert_eq!(
        verify(&path, "Main", "m0_invalid", Options::default_with_k(20)).unwrap(),
        SymResult::Invalid(SourcePos::new(49, 17))
    );
}

#[test]
fn sym_exec_exceptions_m1() {
    let path = "./examples/exceptions.oox";

    assert_eq!(
        verify(&path, "Main", "m1", Options::default_with_k(20)).unwrap(),
        SymResult::Valid
    );
    assert_eq!(
        verify(&path, "Main", "m1_invalid", Options::default_with_k(20)).unwrap(),
        SymResult::Invalid(SourcePos::new(68, 17))
    );
}

#[test]
fn sym_exec_exceptions_m2() {
    let path = "./examples/exceptions.oox";

    assert_eq!(
        verify(&path, "Main", "m2", Options::default_with_k(20)).unwrap(),
        SymResult::Valid
    );
}

#[test]
fn sym_exec_exceptions_m3() {
    let path = "./examples/exceptions.oox";

    assert_eq!(
        verify(&path, "Main", "m3", Options::default_with_k(30)).unwrap(),
        SymResult::Valid
    );
    assert_eq!(
        verify(&path, "Main", "m3_invalid1", Options::default_with_k(30)).unwrap(),
        SymResult::Invalid(SourcePos::new(94, 17))
    );
    assert_eq!(
        verify(&path, "Main", "m3_invalid2", Options::default_with_k(30)).unwrap(),
        SymResult::Invalid(SourcePos::new(102, 21))
    );
}

#[test]
fn sym_exec_exceptions_null() {
    let path = "./examples/exceptions.oox";

    assert_eq!(
        verify(&path, "Main", "nullExc1", Options::default_with_k(30)).unwrap(),
        SymResult::Valid
    );
    assert_eq!(
        verify(&path, "Main", "nullExc2", Options::default_with_k(30)).unwrap(),
        SymResult::Valid
    );
    // assert_eq!(verify_file(&file_content, "m3_invalid1", 30), SymResult::Invalid);
    // assert_eq!(verify_file(&file_content, "m3_invalid2", 30), SymResult::Invalid);
}

#[test]
fn sym_exec_array1() {
    let path = "./examples/array/array1.oox";

    assert_eq!(
        verify(&path, "Main", "foo", Options::default_with_k(50)).unwrap(),
        SymResult::Valid
    );
    assert_eq!(
        verify(&path, "Main", "foo_invalid", Options::default_with_k(50)).unwrap(),
        SymResult::Invalid(SourcePos::new(33, 16))
    );
    assert_eq!(
        verify(&path, "Main", "sort", Options::default_with_k(300)).unwrap(),
        SymResult::Valid
    );
    assert_eq!(
        verify(&path, "Main", "sort_invalid1", Options::default_with_k(50)).unwrap(),
        SymResult::Invalid(SourcePos::new(62, 17))
    );
    assert_eq!(
        verify(&path, "Main", "max", Options::default_with_k(50)).unwrap(),
        SymResult::Valid
    );
    assert_eq!(
        verify(&path, "Main", "max_invalid1", Options::default_with_k(50)).unwrap(),
        SymResult::Invalid(SourcePos::new(104, 21))
    );
    assert_eq!(
        verify(&path, "Main", "max_invalid2", Options::default_with_k(50)).unwrap(),
        SymResult::Invalid(SourcePos::new(120, 17))
    );
    assert_eq!(
        verify(&path, "Main", "exists_valid", Options::default_with_k(50)).unwrap(),
        SymResult::Valid
    );
    // assert_eq!(verify_file(&file_content, "exists_invalid1", 50), SymResult::Invalid);
    assert_eq!(
        verify(
            &path,
            "Main",
            "exists_invalid2",
            Options::default_with_k(50)
        )
        .unwrap(),
        SymResult::Invalid(SourcePos::new(160, 17))
    );
    assert_eq!(
        verify(
            &path,
            "Main",
            "array_creation1",
            Options::default_with_k(50)
        )
        .unwrap(),
        SymResult::Valid
    );
    assert_eq!(
        verify(
            &path,
            "Main",
            "array_creation2",
            Options::default_with_k(50)
        )
        .unwrap(),
        SymResult::Valid
    );
    assert_eq!(
        verify(
            &path,
            "Main",
            "array_creation_invalid",
            Options::default_with_k(50)
        )
        .unwrap(),
        SymResult::Invalid(SourcePos::new(193, 17))
    );
}

#[test]
fn sym_exec_array2() {
    let path = "./examples/array/array2.oox";

    assert_eq!(
        verify(&path, "Main", "foo1", Options::default_with_k(50)).unwrap(),
        SymResult::Valid
    );
    assert_eq!(
        verify(&path, "Main", "foo1_invalid", Options::default_with_k(50)).unwrap(),
        SymResult::Invalid(SourcePos::new(37, 15))
    );
    assert_eq!(
        verify(&path, "Main", "foo2_invalid", Options::default_with_k(50)).unwrap(),
        SymResult::Invalid(SourcePos::new(51, 18))
    );
    assert_eq!(
        verify(&path, "Main", "sort", Options::default_with_k(100)).unwrap(),
        SymResult::Valid
    );
}

#[test]
fn sym_exec_inheritance() {
    let path = "./examples/inheritance/inheritance.oox";
    let k = 150;
    let options = Options::default_with_k(k);

    assert_eq!(
        verify(&path, "Main", "test1", options).unwrap(),
        SymResult::Valid
    );
    assert_eq!(
        verify(&path, "Main", "test1_invalid", options).unwrap(),
        SymResult::Invalid(SourcePos::new(25, 16))
    );
    assert_eq!(
        verify(&path, "Main", "test2a", options).unwrap(),
        SymResult::Valid
    );

    assert_eq!(
        verify(&path, "Main", "test2b", options).unwrap(),
        SymResult::Valid
    );

    assert_eq!(
        verify(&path, "Main", "test2b_invalid", options).unwrap(),
        SymResult::Invalid(SourcePos::new(68, 16))
    );

    assert_eq!(
        verify(&path, "Main", "test3", options).unwrap(),
        SymResult::Valid
    );

    assert_eq!(
        verify(&path, "Main", "test4_valid", options).unwrap(),
        SymResult::Valid
    );
    assert_eq!(
        verify(&path, "Main", "test4_invalid", options).unwrap(),
        SymResult::Invalid(SourcePos::new(25, 16))
    );
    assert_eq!(
        verify(&path, "Main", "test5", options).unwrap(),
        SymResult::Valid
    );

    assert_eq!(
        verify(&path, "Main", "test6", options).unwrap(),
        SymResult::Valid
    );
}

#[test]
fn sym_exec_inheritance_specifications() {
    let path = "./examples/inheritance/specifications.oox";
    let k = 150;
    let options = Options::default_with_k(k);
    assert_eq!(
        verify(&path, "Main", "test_valid", options).unwrap(),
        SymResult::Valid
    );
    assert_eq!(
        verify(&path, "Main", "test_invalid", options).unwrap(),
        SymResult::Invalid(SourcePos::new(3, 18))
    );
}

#[test]
fn sym_exec_interface() {
    let path = "./examples/inheritance/interface.oox";
    let k = 150;
    let options = Options::default_with_k(k);

    println!("hello");

    assert_eq!(
        verify(&path, "Main", "main", options).unwrap(),
        SymResult::Valid
    );
    assert_eq!(
        verify(&path, "Main", "test1_valid", options).unwrap(),
        SymResult::Valid
    );
    assert_eq!(
        verify(&path, "Main", "test1_invalid", options).unwrap(),
        SymResult::Invalid(SourcePos::new(35, 12))
    );
}

#[test]
fn sym_exec_interface2() {
    let path = "./examples/inheritance/interface2.oox";
    let k = 150;
    let options = Options::default_with_k(k);

    assert_eq!(
        verify(&path, "Foo", "test_valid", options).unwrap(),
        SymResult::Valid
    );
    assert_eq!(
        verify(&path, "Foo1", "test_invalid", options).unwrap(),
        SymResult::Invalid(SourcePos::new(3, 16))
    );
    assert_eq!(
        verify(&path, "Foo2", "test_valid", options).unwrap(),
        SymResult::Valid
    );
    assert_eq!(
        verify(&path, "Foo3", "test_invalid", options).unwrap(),
        SymResult::Invalid(SourcePos::new(37, 16))
    );
    //assert_eq!(verify(&file_content, "Foo4", "test_valid", k), SymResult::Valid);
}

#[test]
fn sym_exec_polymorphic() {
    let k = 150;
    let options = Options::default_with_k(k);
    assert_eq!(
        verify(
            "./examples/inheritance/sym_exec_polymorphic.oox",
            "Main",
            "main",
            options
        )
        .unwrap(),
        SymResult::Valid
    );
}

#[test]
fn benchmark_col_25() {
    let k = 15000;
    let options = Options::default_with_k(k);
    assert_eq!(
        verify(
            "./benchmark_programs/defects4j/collections_25.oox",
            "Test",
            "test",
            options
        )
        .unwrap(),
        SymResult::Invalid(SourcePos::new(352, 21))
    );
}

#[test]
fn benchmark_col_25_symbolic() {
    let k = 15000;
    let options = Options::default_with_k(k);
    assert_eq!(
        verify(
            "./benchmark_programs/defects4j/collections_25.oox",
            "Test",
            "test_symbolic",
            options
        )
        .unwrap(),
        SymResult::Invalid(SourcePos::new(395, 21))
    );
}

#[test]
fn benchmark_col_25_test3() {
    let k = 15000;
    let options = Options::default_with_k(k);
    assert_eq!(
        verify(
            "./benchmark_programs/defects4j/collections_25.oox",
            "Test",
            "test3",
            options
        )
        .unwrap(),
        SymResult::Valid
    );
}

#[test]
fn any_linked_list() {
    let k = 40;
    let options = Options::default_with_k(k);
    assert_eq!(
        verify(
            "./benchmark_programs/experiment1/1Node.oox",
            "Main",
            "test2",
            options
        )
        .unwrap(),
        SymResult::Valid
    );
}

#[test]
fn supertest() {
    let k = 50;
    let options = Options::default_with_k(k);
    assert_eq!(
        verify("./examples/supertest.oox", "Main", "test", options).unwrap(),
        SymResult::Valid
    )
}

#[test]
fn multiple_constructors() {
    let k = 50;
    let options = Options::default_with_k(k);
    assert_eq!(
        verify(
            "./examples/multiple_constructors.oox",
            "Foo",
            "test",
            options
        )
        .unwrap(),
        SymResult::Valid
    )
}

#[test]
fn arrays3() {
    let k = 50;
    let options = Options::default_with_k(k);
    assert_eq!(
        verify("./examples/array/array3.oox", "Main", "test", options).unwrap(),
        SymResult::Valid
    )
}
