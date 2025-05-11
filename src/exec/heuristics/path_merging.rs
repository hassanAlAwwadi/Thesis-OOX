use std::{cell::RefCell, collections::HashMap, rc::Rc};

use itertools::{izip, Either};
use slog::Logger;

use crate::{
    cfg::CFGStatement, exec::{constants, IdCounter, SymResult}, merge::{DynamicPointer, MergeEngine, MergeState, SetEngine, TreeEngine}, positioned::WithPosition, statistics::Statistics, symbol_table::SymbolTable, typeable::Typeable, Expression, Identifier, Invocation, Lhs, Options, Rhs, RuntimeType, Statement, TypeExpr
};

use super::State;

pub(crate) fn sym_exec(
    init: State,
    program: &HashMap<u64, CFGStatement>,
    flows: &HashMap<u64, Vec<u64>>,
    st: &SymbolTable,
    root_logger: Logger,
    path_counter: Rc<RefCell<IdCounter<u64>>>,
    statistics: &mut Statistics,
    _entry_method: crate::cfg::MethodIdentifier,
    options: &Options,
    abstraction: bool,
) -> SymResult {
    let mut symbols = vec![];
    for (id, expr) in init.stack.current_stackframe().unwrap().params.iter() {
        if let Expression::SymbolicVar {
            var,
            type_,
            info: _,
        } = expr.as_ref()
        {
            symbols.push((id.clone(), var.clone(), type_.clone()));
        } else {
            panic!("starting out with non symbolic values!?");
        }
    }

    if abstraction {
        let mut engine = SetEngine::new();
        let state = engine.make_new_state(init.pc, Rc::new(Expression::TRUE), symbols);
        return run(
            engine,
            state,
            program,
            flows,
            st,
            root_logger,
            path_counter,
            statistics,
            _entry_method,
            options,
        );
    } else {
        let mut engine = TreeEngine::new();
        let state = engine.make_new_state(init.pc, Rc::new(Expression::TRUE), symbols);
        return run(
            engine,
            state,
            program,
            flows,
            st,
            root_logger,
            path_counter,
            statistics,
            _entry_method,
            options,
        );

    };
}

enum Status {
    Waiting(),
    Active(),
}

struct MergeInfo {
    merge_at: u64,
    dcf_size: usize,
}

type FTable = HashMap<(Identifier, Identifier, Vec<RuntimeType>), (u64, Vec<Identifier>, Rc<Expression>)>;
fn run<T>(
    mut engine: T,
    init_state: T::State,
    program: &HashMap<u64, CFGStatement>,
    flows: &HashMap<u64, Vec<u64>>,
    st: &SymbolTable,
    _root_logger: Logger,
    _path_counter: Rc<RefCell<IdCounter<u64>>>,
    _statistics: &mut Statistics,
    _entry_method: crate::cfg::MethodIdentifier,
    options: &Options,
) -> SymResult
where
    T: MergeEngine,
    T::EValue: Clone,
{
    let mut function_entry_map: FTable = HashMap::new();

    for (entry, stmt) in program {
        if let CFGStatement::FunctionEntry {
            decl_name,
            method_name,
            argument_types,
        } = stmt
        {
            let method_name = method_name.clone();
            let class = st.get_class(decl_name).unwrap();

            let mut arg_namess = vec![];
            let mut reqs = vec![];
            for imp in class.members.clone() {
                if let Some(method) = imp.method() {
                    if method.name.eq(&method_name) {
                        let arg_names = method.params.iter().map(|par| par.name.clone()).collect();
                        let req = if let Some((l,r)) = method.requires().clone(){
                            if let Some(t) = r{
                                let t = match t{
                                    TypeExpr::InstanceOf { var, rhs, info } 
                                        => Rc::new(Expression::TypeExpr {
                                            texpr: TypeExpr::InstanceOf {
                                                var: var.clone(),
                                                rhs: rhs.clone(),
                                                info: info.clone(),
                                            },
                                        }),
                                    TypeExpr::NotInstanceOf { var, rhs, info } 
                                        => Rc::new(Expression::TypeExpr {
                                            texpr: TypeExpr::NotInstanceOf {
                                                var: var.clone(),
                                                rhs: rhs.clone(),
                                                info: info.clone(),
                                            },
                                        }),
                                };
                                Expression::and(l.clone(), t)
                            }
                            else{
                                l.clone()
                            }
                        }
                        else{
                            Rc::new(Expression::TRUE)
                        };
                        arg_namess.push(arg_names);
                        reqs.push(req);
                    }
                }
            }

            let key = (decl_name.clone(), method_name, argument_types.clone());
            for (arg_names, req) in izip!(arg_namess, reqs) {
                let entry = (entry.clone(), arg_names, req);
                function_entry_map.insert(key.clone(), entry);
            }
        }
    }
    // states that are actively progressing
    // together with a reference to their parent and sibling
    let mut paths: Vec<(T::State, Status)> = vec![];
    let mut m_at_s_at: Vec<MergeInfo> = vec![];
    paths.push((init_state, Status::Active()));

    while let Some((mut current, current_status)) = paths.pop() {
        if current.path_length() > options.k {

            if let Some(merge_info) = m_at_s_at.pop() {
                //merge info present, so our sibling must be one
                //behind us and our parent two behind us
                let (sibling, _) = paths.pop().unwrap();
                let (mut parent, _) = paths.pop().unwrap();

                parent.merge_part(sibling);

                if let Some(p_merge_info) = m_at_s_at.pop() {
                    // we've already moved beyond the merge point of the parent...
                    if p_merge_info.dcf_size > merge_info.dcf_size {
                        // uncle needs to be reawakened if it was already asleep,
                        // because its sleep point has been moved further back
                        let (uncle, _) = paths.pop().unwrap();
                        paths.push((uncle, Status::Active()));

                        // the direct parent on the other hand can go directly
                        // to sleep, because its new waiting spot is where its already
                        // at.
                        paths.push((parent, Status::Waiting()));

                        m_at_s_at.push(merge_info)
                    }
                    // we've not yet moved beyond the parent's merge point
                    // parent still needs to sleep though, since its waiting on its children
                    else {
                        paths.push((parent, Status::Waiting()));
                        m_at_s_at.push(p_merge_info);
                    }
                }
                continue;
            } else {
                return SymResult::Valid;
            }
        }

        let stmt_id = current.get_pointer();

        current.incr_path();

        // we have reached our join point
        if let Some(MergeInfo { merge_at, dcf_size }) = m_at_s_at.pop() {
            if stmt_id == merge_at && current.get_dynamic_cf_size() == dcf_size {
                let (sibling, sib_status) = paths.pop().unwrap();
                if let Status::Active() = sib_status {
                    // our sibling still needs to do stuff, so we let push it to the top of the stack
                    paths.push((current, Status::Waiting()));
                    paths.push((sibling, current_status));

                    // other sibling will need this info too :relieved:
                    m_at_s_at.push(MergeInfo { merge_at, dcf_size });
                } else if let Status::Waiting() = sib_status {
                    //our sibling has been waiting, so we can merge :relieved:
                    let (mut parent, _parent_status) = paths.pop().unwrap();

                    parent.merge_full(current, sibling);
                    paths.push((parent, Status::Active()));
                } else {
                    panic!("we claim to be the sibling of the prime path...")
                }
                continue;
            } else {
                m_at_s_at.push(MergeInfo { merge_at, dcf_size });
            }
        }

        let stmt = program.get(&stmt_id);
        match stmt {
            None => panic!("malformed graph"),
            Some(statatement) => {
                match statatement {
                    CFGStatement::Statement(statement) => match statement {
                        Statement::Skip => {
                            set_to_next_pc(&mut current, flows);
                            paths.push((current, current_status));
                        }

                        Statement::Declare { type_, var, info } => {
                            engine.decl_in(&mut current, &type_, &var, &info);
                            set_to_next_pc(&mut current, flows);
                            paths.push((current, current_status));
                        }
                        Statement::Assign { lhs, rhs, info: _ } => {
                            if let Rhs::RhsCall { invocation, .. } = rhs {
                                let nexts: &Vec<u64> = flows
                                    .get(&current.get_pointer())
                                    .unwrap_or_else(|| panic!("malformed graph"));
                                assert_eq!(nexts.len(), 1);
                                

                                let mut constraints_target_pairs = get_possible_function_heads(
                                    &invocation,
                                    st,
                                    &function_entry_map,
                                );
                                let next = nexts.last().unwrap().clone();
                                let vals = invocation
                                    .arguments()
                                    .iter()
                                    .map(|expr| {
                                        (
                                            expr.get_type(),
                                            engine.eval_with(&mut current, expr.clone()),
                                        )
                                    })
                                    .collect();
                                current.push_stack();
                                insert_states_function_call(
                                    &mut engine,
                                    current,
                                    &vals,
                                    &mut constraints_target_pairs,
                                    &mut paths,
                                    &mut m_at_s_at,
                                    Some(lhs.clone()),
                                    next,
                                );
                            } else {
                                engine.assign_expr(&mut current, &lhs, &rhs);
                                set_to_next_pc(&mut current, flows);
                                paths.push((current, current_status));
                            }
                        }

                        Statement::Call {
                            invocation,
                            info: _,
                        } => {
                            let nexts: &Vec<u64> = flows
                                .get(&current.get_pointer())
                                .unwrap_or_else(|| panic!("malformed graph"));
                            assert_eq!(nexts.len(), 1);

                            let mut constraints_target_pairs =
                                get_possible_function_heads(&invocation, st, &function_entry_map);
                            let next = nexts.last().unwrap().clone();
                            let vals = invocation
                                .arguments()
                                .iter()
                                .map(|expr| {
                                    (
                                        expr.get_type(),
                                        engine.eval_with(&mut current, expr.clone()),
                                    )
                                })
                                .collect();
                            current.push_stack();
                            insert_states_function_call(
                                &mut engine,
                                current,
                                &vals,
                                &mut constraints_target_pairs,
                                &mut paths,
                                &mut m_at_s_at,
                                None,
                                next,
                            );
                        }
                        Statement::Assert { assertion, info } => {
                            if engine.is_valid_for(&mut current, assertion.clone()) {
                                set_to_next_pc(&mut current, flows);
                                paths.push((current, current_status));
                                continue;
                            }
                            return SymResult::Invalid(*info);
                        }
                        Statement::Assume {
                            assumption,
                            info: _,
                        } => {
                            engine.add_assumption_to(&mut current, assumption.clone());
                            if engine.is_feasible(&mut current) {
                                set_to_next_pc(&mut current, flows);
                                paths.push((current, current_status));
                                continue;
                            }

                            if let Some(_) = m_at_s_at.pop() {
                                //merge info present, so our sibling must be one
                                //behind us and our parent two behind us
                                let (sibling, _) = paths.pop().unwrap();
                                let (mut parent, _) = paths.pop().unwrap();

                                parent.merge_part(sibling);
                                paths.push((parent, Status::Active()));
                            }
                        }
                        Statement::Continue { info: _ } => {
                            let mut next: u64 = 0;
                            let mut still_searching = true;
                            while let Some(control) = current.pop_dynamic_cf() {
                                if let DynamicPointer::Whl(head, then) = control {
                                    still_searching = false;
                                    next = head;
                                    current.push_dynamic_cf(DynamicPointer::Whl(head, then));
                                    break;
                                }
                            }
                            if still_searching {
                                panic!("continue but outside of while loop")
                            };
                            current.set_pointer(next);
                            paths.push((current, current_status));
                        }

                        Statement::Break { info: _ } => {
                            let mut next: u64 = 0;
                            let mut still_searching = true;
                            while let Some(control) = current.pop_dynamic_cf() {
                                if let DynamicPointer::Whl(_, then) = control {
                                    still_searching = false;
                                    next = then;
                                    break;
                                }
                            }
                            if still_searching {
                                panic!("break but outside of while loop")
                            };
                            current.set_pointer(next);
                            paths.push((current, current_status));
                        }

                        Statement::Return { expression, info } => {
                            let mut return_pointer = 0;
                            let mut return_var: Option<Lhs> = None;
                            let return_value = match expression {
                                Some(e) => Some(Rhs::RhsExpression {
                                    value: e.clone(),
                                    type_: e.get_type(),
                                    info: *info,
                                }),
                                _ => None,
                            };
                            let mut still_searching = true;

                            while let Some(control) = current.pop_dynamic_cf() {
                                if let DynamicPointer::Ret(return_i, return_value_to) = control {
                                    still_searching = false;
                                    return_var = return_value_to;
                                    return_pointer = return_i;
                                    break;
                                }
                            }

                            if still_searching {
                                //guess we're at the end of it all :relieved:
                                //its possible there are still other states that have split
                                //but would never merge
                                //so we wait for now :relieved:
                                continue;
                            }

                            current.set_pointer(return_pointer);
                            if let Some(value) = return_value {
                                let v = engine.eval_with_r(&mut current, &value);
                                current.pop_stack();

                                if let Some(var) = return_var {
                                    engine.assign_evaled(&mut current, &var, v);
                                } else {
                                    engine.assign_evaled(
                                        &mut current,
                                        &Lhs::LhsVar {
                                            var: constants::retval(),
                                            type_: value.get_type(),
                                            info: *info,
                                        },
                                        v,
                                    );
                                }
                            } else {
                                current.pop_stack();
                            }

                            if let Some(MergeInfo { merge_at, dcf_size }) = m_at_s_at.pop() {
                                let current_dcf_size = current.get_dynamic_cf_size();
                                //oops, we've busted through our merge point
                                if current_dcf_size < dcf_size {
                                    // so we set our merge point to where we at right now
                                    m_at_s_at.push(MergeInfo {
                                        merge_at: return_pointer,
                                        dcf_size: current_dcf_size,
                                    });

                                    // need to reawaken our brother, if he was asleep
                                    let (brother, _) = paths.pop().unwrap();
                                    paths.push((brother, Status::Active()));

                                    // but we can go to sleep :relieved
                                    paths.push((current, Status::Waiting()))
                                }
                                //haven't pushed through our merge point yet
                                else {
                                    // so we restore it as it was
                                    m_at_s_at.push(MergeInfo { merge_at, dcf_size });
                                    // and stay active
                                    paths.push((current, Status::Active()))
                                }
                            } else {
                                //we didn't have a merge point at all, how quant
                                paths.push((current, Status::Active()));
                            }
                        }
                        Statement::Throw {
                            message: _,
                            info: _,
                        } => {
                            let mut return_pointer = 0;
                            let mut wait_pointer = 0;
                            let mut still_searching: bool = true;

                            while let Some(control) = current.pop_dynamic_cf() {
                                current.pop_stack();
                                if let DynamicPointer::Thr(catch_entry, try_catch_next) = control {
                                    still_searching = false;
                                    return_pointer = catch_entry;
                                    wait_pointer = try_catch_next;
                                    break;
                                }
                            }

                            if still_searching {
                                panic!("broken control flow in return statement");
                            }

                            current.set_pointer(return_pointer);

                            if let Some(MergeInfo { merge_at, dcf_size }) = m_at_s_at.pop() {
                                let current_dcf_size = current.get_dynamic_cf_size();
                                //oops, we've busted through our merge point
                                if current_dcf_size < dcf_size {
                                    // so we set our merge point to after the try catch block
                                    m_at_s_at.push(MergeInfo {
                                        merge_at: wait_pointer,
                                        dcf_size: current_dcf_size,
                                    });

                                    // need to reawaken our brother, if he was asleep
                                    let (brother, _) = paths.pop().unwrap();
                                    paths.push((brother, Status::Active()));
                                }
                                //haven't pushed through our merge point yet
                                else {
                                    // so we restore it as it was
                                    m_at_s_at.push(MergeInfo { merge_at, dcf_size });
                                }
                            }
                            //regardless of what happened, we need to stay awake.
                            paths.push((current, Status::Active()));
                        }
                        _ => unreachable!(
                            "CFGStatement::Statement should only ever be a non control statement"
                        ),
                    },

                    CFGStatement::Ite(cond, _, _, join) => {
                        let cond = cond.clone().either(|s| s, |t| Rc::new(Expression::TypeExpr { texpr: t }));
                        let (mut then_child, mut else_child) =
                            engine.split_on(&mut current, cond);

                        if let [left, right] = flows.get(&stmt_id).unwrap().as_slice() {
                            //its possible the two branches don't have a join
                            if let Some(join) = join{
                                m_at_s_at.push(MergeInfo {
                                    merge_at: join.clone(),
                                    dcf_size: current.get_dynamic_cf_size(),
                                });
                            }
                            else{
                                //not always wrong
                                //possible we have something like this:
                                // fn f() {
                                //     if (true) { foo ()}
                                //     else { bar ()}
                                // }
                                // were the two branches are not joined
                                match current.pop_dynamic_cf() {
                                    Some(DynamicPointer::Ret(return_i, return_value)) => {
                                        m_at_s_at.push(MergeInfo {
                                            merge_at: return_i,
                                            dcf_size: current.get_dynamic_cf_size(),
                                        });
                                        current.push_dynamic_cf(DynamicPointer::Ret(return_i, return_value));
                                    }
                                    Some(DynamicPointer::Whl(whl, next)) => {
                                        m_at_s_at.push(MergeInfo {
                                            merge_at: next,
                                            dcf_size: current.get_dynamic_cf_size(),
                                        });
                                        current.push_dynamic_cf(DynamicPointer::Whl(whl, next));
                                    }
                                    Some(DynamicPointer::Thr(try_catch, next)) => {
                                        m_at_s_at.push(MergeInfo {
                                            merge_at: next,
                                            dcf_size: current.get_dynamic_cf_size(),
                                        });
                                        current.push_dynamic_cf(DynamicPointer::Thr(try_catch, next));
                                    }
                                    None => {
                                        //no dynamic control flow, so we don't need to do anything
                                        //these two branches while finish seperately, can only happen if we branch
                                        //at the start of main()
                                    }
                                }
                            };
                            then_child.set_pointer(*left);
                            else_child.set_pointer(*right);

                            paths.push((current, Status::Waiting()));
                            paths.push((else_child, Status::Active()));
                            paths.push((then_child, Status::Active()));
                        } else {
                            panic!("ite with only one branch?!")
                        }
                    }
                    CFGStatement::While(expression, b) => {
                        if let Some(flow) = current.pop_dynamic_cf() {
                            if let DynamicPointer::Whl(t, _) = flow {
                                if t == stmt_id {
                                    //we've reintered the while loop, so we remove this one and readd it to the then branch
                                } else {
                                    current.push_dynamic_cf(flow);
                                }
                            } else {
                                current.push_dynamic_cf(flow);
                            }
                        }
                        let (mut then_child, mut else_child) =
                            engine.split_on(&mut current, expression.clone());

                        //get pointer to the next statement after the while
                        let nexts: Vec<_> = flows
                            .get(&stmt_id)
                            .unwrap()
                            .into_iter()
                            .filter(|next| *next != b)
                            .collect();

                        if let [head, then] = nexts.as_slice() {
                            let n_next = flows.get(then).unwrap()[0];
                            m_at_s_at.push(MergeInfo {
                                merge_at: n_next,
                                dcf_size: current.get_dynamic_cf_size(),
                            });
                            paths.push((current, Status::Waiting()));

                            then_child.set_pointer(**head);
                            else_child.set_pointer(**then);
                            paths.push((else_child, Status::Active()));

                            then_child.push_dynamic_cf(DynamicPointer::Whl(stmt_id, n_next));
                            paths.push((then_child, Status::Active()));
                        } else {
                            panic!("strange pointers coming from while: {:?}", nexts);
                        }
                    }
                    CFGStatement::TryCatch(try_entry, try_exit, catch_entry, _catch_exit) => {
                        current.set_pointer(*try_entry);

                        let nexts = flows
                            .get(&try_exit)
                            .unwrap_or_else(|| panic!("malformed graph"));
                        assert_eq!(nexts.len(), 1);
                        let t_next = nexts.last().unwrap().clone();

                        current.push_dynamic_cf(DynamicPointer::Thr(*catch_entry, t_next));
                        paths.push((current, Status::Active()));
                    }
                    CFGStatement::TryEntry(_) => {
                        set_to_next_pc(&mut current, flows);
                        paths.push((current, Status::Active()));
                    }
                    CFGStatement::TryExit => {
                        set_to_next_pc(&mut current, flows);
                        paths.push((current, Status::Active()));
                    }
                    CFGStatement::CatchEntry(_) => {
                        //and put a new one on top.
                        set_to_next_pc(&mut current, flows);
                        paths.push((current, Status::Active()));
                    }
                    CFGStatement::CatchExit => {
                        set_to_next_pc(&mut current, flows);
                        paths.push((current, Status::Active()));
                    }
                    CFGStatement::Seq(l, _r) => {
                        current.set_pointer(*l);
                        paths.push((current, Status::Active()));
                    }
                    CFGStatement::FunctionEntry {
                        decl_name,
                        method_name,
                        argument_types,
                    } => {
                        let k = (decl_name.clone(), method_name.clone(), argument_types.clone());
                        let (_,_,req) = function_entry_map.get(&k).unwrap();
                        if current.path_length() == 1 {
                            //we're at the start of the function, so we need to add our assumptions
                            engine.add_assumption_to(&mut current, Either::Left(req.clone()));
                            if engine.is_feasible(&mut current) {
                                set_to_next_pc(&mut current, flows);
                                paths.push((current, current_status));
                                continue;
                            }

                            if let Some(_) = m_at_s_at.pop() {
                                //merge info present, so our sibling must be one
                                //behind us and our parent two behind us
                                let (sibling, _) = paths.pop().unwrap();
                                let (mut parent, _) = paths.pop().unwrap();

                                parent.merge_part(sibling);
                                paths.push((parent, Status::Active()));
                            }

                        }
                        else{
                            //its not an assumption, its a requirement... 
                            if engine.is_valid_for(&mut current, req.clone()) {
                                set_to_next_pc(&mut current, flows);
                                paths.push((current, current_status));
                                continue;
                            }
                            return SymResult::Invalid(req.get_position());
                        }
                    }
                    CFGStatement::FunctionExit {
                        decl_name: _,
                        method_name: _,
                        argument_types: _,
                    } => {
                        // simpler than a return, this can't break through an enclosing while or try block :relieved
                        // and it can't possible return a value :relieved
                        current.pop_stack();
                        let next = current.pop_dynamic_cf();
                        match next {
                            None => {
                                //guess we're at the end of it all :relieved:
                                //its possible there are still other states that have split
                                //but would never merge
                                //so we wait for now :relieved:
                            }
                            Some(DynamicPointer::Ret(return_i, None)) => {
                                current.set_pointer(return_i);
                                paths.push((current, Status::Active()));
                            }
                            Some(dyn_) =>{ 
                                println!("unexpected dynamic control flow: {:?}", dyn_);
                                while let Some(dyn_) = current.pop_dynamic_cf(){
                                    println!("and: {:?}", dyn_);

                                }
                                panic!("unexpected dynamic control flow")
                            },
                        }
                    }
                }
            }
        }
    }

    return SymResult::Valid;
}

fn insert_states_function_call<T>(
    engine: &mut T,
    current: T::State,
    values: &Vec<(RuntimeType, T::EValue)>,
    constraints_target_pairs: &mut Vec<(Rc<Expression>, (u64, Vec<Identifier>))>,
    paths: &mut Vec<(T::State, Status)>,
    merges: &mut Vec<MergeInfo>,
    return_var: Option<Lhs>,
    return_ptr: u64,
) where
    T: MergeEngine,
    T::EValue: Clone,
{
    if constraints_target_pairs.len() <= 0 {
        panic!("no function entry points found")
    }
    

    let mut head = current;
    let mut must_push = true;

    while let Some((expr, (entry, args))) = constraints_target_pairs.pop() {
        if constraints_target_pairs.len() > 0 {
            merges.push(MergeInfo {
                merge_at: return_ptr,
                dcf_size: head.get_dynamic_cf_size(),
            });

            let (mut left, mut right) = engine.split_on(&mut head, expr);
            
            if must_push {
                left.push_dynamic_cf(DynamicPointer::Ret(return_ptr, return_var.clone()));
                right.push_dynamic_cf(DynamicPointer::Ret(return_ptr, return_var.clone()));
                must_push = false;
            }

            for (arg, (type_, val)) in args.iter().zip(values.iter()) {
                engine.assign_evaled(
                    &mut left,
                    &Lhs::LhsVar {
                        var: arg.clone(),
                        type_: type_.clone(),
                        info: crate::SourcePos::UnknownPosition,
                    },
                    val.clone(),
                );
            }
            left.set_pointer(entry);

            paths.push((head, Status::Waiting()));
            paths.push((left, Status::Active()));
            head = right;
        }
        // last iteration
        else {
            engine.add_assumption_to(&mut head, Either::Left(expr));
            for (arg, (type_, val)) in args.iter().zip(values.iter()) {
                engine.assign_evaled(
                    &mut head,
                    &Lhs::LhsVar {
                        var: arg.clone(),
                        type_: type_.clone(),
                        info: crate::SourcePos::UnknownPosition,
                    },
                    val.clone(),
                );
            }

            if must_push {
                head.push_dynamic_cf(DynamicPointer::Ret(return_ptr, return_var.clone()));
                must_push = false;
            }

            head.set_pointer(entry);
            paths.push((head, Status::Active()));
            break;
        }
    }
}

fn get_possible_function_heads(
    invocation: &Invocation,
    st: &SymbolTable,
    funmap: &FTable,
) -> Vec<(Rc<Expression>, (u64, Vec<Identifier>))> {
    match invocation {
        Invocation::InvokeMethod {
            lhs,
            rhs,
            arguments,
            resolved,
            info: _,
        } => {
            let arg_types: Vec<RuntimeType> = arguments
                .iter()
                .map(|expr| expr.as_ref().type_of())
                .collect();
            let mut res = vec![];

            if let Some(resolved) = resolved {
                if resolved.len() == 1 {
                    let (c, m) = resolved.get(lhs).unwrap();
                    let ptr = funmap
                        .get(&(c.name().clone(), m.name.clone(), arg_types.clone()))
                        .unwrap()
                        .clone();
                    res.push((Rc::new(Expression::TRUE), (ptr.0, ptr.1)));
                } else {
                    for (_i, (c, m)) in resolved.iter() {
                        let cond = Rc::new(Expression::TypeExpr {
                            texpr: TypeExpr::InstanceOf {
                                var: lhs.clone(),
                                rhs: RuntimeType::ReferenceRuntimeType {
                                    type_: c.name().clone(),
                                },
                                info: crate::SourcePos::UnknownPosition,
                            },
                        });

                        let ptr = funmap
                            .get(&(c.name().clone(), m.name.clone(), arg_types.clone()))
                            .unwrap()
                            .clone();
                        res.push((cond, (ptr.0, ptr.1)));
                    }
                }
            } else {
                let classes = st.subclasses(lhs);

                for class in classes {
                    let key = &(class.as_ref().name.clone(), rhs.clone(), arg_types.clone());
                    let cond = Rc::new(Expression::TypeExpr {
                        texpr: TypeExpr::InstanceOf {
                            var: lhs.clone(),
                            rhs: RuntimeType::ReferenceRuntimeType {
                                type_: class.name.clone(),
                            },
                            info: crate::SourcePos::UnknownPosition,
                        },
                    });
                    let ptr = funmap.get(key).unwrap().clone();
                    res.push((cond, (ptr.0, ptr.1)));
                }
            }
            return res;
        }
        Invocation::InvokeSuperMethod {
            rhs: _,
            arguments: _,
            resolved: _,
            info: _,
        } => todo!(),
        Invocation::InvokeConstructor {
            class_name: _,
            arguments,
            resolved,
            info: _,
        } => {
            let arg_types: Vec<RuntimeType> = arguments
                .iter()
                .map(|expr| expr.as_ref().type_of())
                .collect();

            let (i, m) = resolved.as_ref().map(AsRef::as_ref).unwrap();
            let class_name = i.name().clone();
            let cond = Rc::new(Expression::TypeExpr {
                texpr: TypeExpr::InstanceOf {
                    var: constants::this_str(),
                    rhs: RuntimeType::ReferenceRuntimeType {
                        type_: class_name.clone(),
                    },
                    info: crate::SourcePos::UnknownPosition,
                },
            });
            let ptr = funmap
                .get(&(class_name, m.name.clone(), arg_types.clone()))
                .unwrap()
                .clone();
            return vec![(cond, (ptr.0, ptr.1))];
        }
        Invocation::InvokeSuperConstructor {
            arguments: _,
            resolved: _,
            info: _,
        } => todo!(),
    }
}

fn set_to_next_pc<T>(top_state: &mut T, flows: &HashMap<u64, Vec<u64>>)
where
    T: MergeState,
{
    let nexts = flows
        .get(&top_state.get_pointer())
        .unwrap_or_else(|| panic!("malformed graph"));
    assert_eq!(nexts.len(), 1);
    let next = nexts.last().unwrap().clone();
    top_state.set_pointer(next);
}
