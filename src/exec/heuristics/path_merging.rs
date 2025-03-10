use std::{
  cell::RefCell, collections::{BTreeMap, HashMap}, os::unix::process::parent_id, rc::Rc
};

use itertools::{Either, Merge};
use slog::Logger;
use z3::SatResult;

use crate::{
  cfg::CFGStatement, exec::{constants, IdCounter, PathConstraints, SymResult}, merge::{self, DynamicPointer, MState, MergingState}, statistics::Statistics, symbol_table::SymbolTable, z3_checker, Expression, Invocation, Lhs, Options, Rhs, SourcePos, Statement
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
) -> SymResult {
  let mut state: MState = MergingState::new(init.pc, Rc::new(Expression::TRUE));
  return run(
     state,
     program, 
     flows, 
     st, 
     root_logger, 
     path_counter, 
     statistics, 
     _entry_method, options);   
}


enum Status {
  Waiting(),
  Active()
}

struct MergeInfo{
  merge_at  : u64,
  dcf_size: usize
}

fn run<P>(
  mut init_state: P ,
  program: &HashMap<u64, CFGStatement>,
  flows: &HashMap<u64, Vec<u64>>,
  st: &SymbolTable,
  root_logger: Logger,
  path_counter: Rc<RefCell<IdCounter<u64>>>,
  statistics: &mut Statistics,
  _entry_method: crate::cfg::MethodIdentifier,
  options: &Options,
) -> SymResult 
where P : MergingState {


  // states that are actively progressing
  // together with a reference to their parent and sibling
  let mut paths: Vec<(P, Status)> = vec![];
  let mut m_at_s_at: Vec<MergeInfo> = vec![];
  paths.push((init_state, Status::Active()));


  while let Some((mut current, current_status)) = paths.pop() {
    
    if current.path_length() > options.k {
      if let Some(merge_info) = m_at_s_at.pop() {
        //merge info present, so our sibling must be one 
        //behind us and our parent two behind us
        let (sibling,_)  = paths.pop().unwrap();
        let (mut parent ,_) =  paths.pop().unwrap();
        
        parent.merge_part(sibling);

        if let Some (p_merge_info) = m_at_s_at.pop(){
          // we've already moved beyond the merge point of the parent... 
          if p_merge_info.dcf_size > merge_info.dcf_size{

            // uncle needs to be reawakened if it was already asleep,
            // because its sleep point has been moved further back
            let (uncle, _) = paths.pop().unwrap();
            paths.push((uncle , Status::Active()));

            // the direct parent on the other hand can go directly
            // to sleep, because its new waiting spot is where its already
            // at.
            paths.push((parent, Status::Waiting()));

            m_at_s_at.push(merge_info)
          }
          // we've not yet moved beyond the parent's merge point
          // parent still needs to sleep though, since its waiting on its children
          else{
            paths.push((parent, Status::Waiting()));
            m_at_s_at.push(p_merge_info);
          }
        }

        //check if the parent perhaps needs their merge point moved
      }
      else{
        todo!("only path has gotten too long...")
      }
    }

    let stmt_id = current.get_pointer();

    current.incr_path();
  
    // we have reached our join point
    if let Some(MergeInfo { merge_at, dcf_size}) = m_at_s_at.pop(){

      if stmt_id == merge_at {
        let (sibling, sib_status) = paths.pop().unwrap(); 
        if let Status::Active() = sib_status{
          // our sibling still needs to do stuff, so we let push it to the top of the stack
          paths.push((current, Status::Waiting()));
          paths.push((sibling, current_status   ));

          // other sibling will need this info too :relieved:
          m_at_s_at.push(MergeInfo { merge_at, dcf_size});
        }
        else if let Status::Waiting() = sib_status{
          //our sibling has been waiting, so we can merge :relieved:
          let (mut parent, parent_status) = paths.pop().unwrap(); 
          
          parent.merge_full(current, sibling);
          paths.push((parent, Status::Active()));
        }
        else {
          panic!("we claim to be the sibling of the prime path...")
        }
        continue;
      }
    }

    match program.get(&stmt_id){
      None => panic!("malformed graph"),
      Some(statatement) => {

        match statatement{
          CFGStatement::Statement(statement) => match statement{
            Statement::Skip => {
              set_to_next_pc(&mut current, flows);
              paths.push((current, current_status));
            },

            Statement::Declare { type_, var, info } => {
              current.decl(&type_, &var, &info);
              set_to_next_pc(&mut current, flows);
              paths.push((current, current_status));
            },
            Statement::Assign { lhs, rhs, info } => {
              if let Rhs::RhsCall { invocation, .. } = rhs {
                let nexts = flows.get(&current.get_pointer()).unwrap_or_else( ||{ panic!("malformed graph") } );
                assert_eq!(nexts.len(), 1);
                let next = nexts.last().unwrap().clone();
            
                // the constraints can also be used to narrow the values on the stack/heap, but we don't do that yet
                let mut constraints_target_pairs : Vec<(Rc<Expression>, u64)> = get_possible_function_heads(&invocation);
                insert_states_function_call(current, &mut constraints_target_pairs, &mut paths, &mut m_at_s_at, Some(lhs.clone()), next);
                // there must be at least one possible function we can refer to, or else this call is impossible
              }
              else{
                current.assign(&lhs, &rhs, &info);
                set_to_next_pc(&mut current, flows);
                paths.push((current, current_status));
              }
            },

            Statement::Call { invocation, info } => {
              let nexts = flows.get(&current.get_pointer()).unwrap_or_else( ||{ panic!("malformed graph") } );
              assert_eq!(nexts.len(), 1);
              let next = nexts.last().unwrap().clone();
              

              let mut constraints_target_pairs : Vec<(Rc<Expression>, u64)> = get_possible_function_heads(&invocation);
              insert_states_function_call(current, &mut constraints_target_pairs, &mut paths, &mut m_at_s_at, None, next);
            },
            Statement::Assert { assertion, info } => {
              if current.is_valid(assertion) {
                set_to_next_pc(&mut current, flows);
                paths.push((current, current_status));
                continue;  
              }
              return SymResult::Invalid(*info)
            },
            Statement::Assume { assumption, info } => {
              current.assume(assumption.clone()); 
              if current.is_feasible()  {
                set_to_next_pc(&mut current, flows);
                paths.push((current, current_status));
                continue;  
              }

              if let Some(_) = m_at_s_at.pop() {
                //merge info present, so our sibling must be one 
                //behind us and our parent two behind us
                let (mut sibling, _) = paths.pop().unwrap();
                let (mut parent , _)=  paths.pop().unwrap();

                parent.merge_part(sibling);
                paths.push((parent, Status::Active()));
              }
              
            },
            Statement::Continue { info } => {
              todo!("pop stack until WHL, reset join point if needed");
              set_to_next_pc(&mut current, flows);
              paths.push((current, current_status));
            },
            Statement::Break { info } => {
              todo!("pop stack until WHL, reset join point if needed");
              set_to_next_pc(&mut current, flows);
              paths.push((current, current_status));
            },

            Statement::Return { expression, info } => {
              let mut return_pointer   = 0;
              let mut return_var: Option<Lhs> = None;
              let return_value =  match expression {
                Some(e) => Some(Rhs::RhsExpression { value: e.clone(), type_: e.get_type(), info: *info }),
                _ => None,
              };
              let mut still_searching = true;

              while let Some(control) = current.pop_dynamic_cf() {
                current.pop_stack();
                if let DynamicPointer::Ret(return_i, return_value_to) = control {
                    still_searching = false;
                    return_var = return_value_to;
                    return_pointer = return_i;
                    break; 
                }
              }

              if still_searching{
                panic!("broken control flow in return statement");
              }
              
              current.set_pointer(return_pointer);
              if let Some(value) = return_value {
                if let Some(var) = return_var {
                  current.assign(&var, &value, &info);
                }
                else{
                  current.assign_to_stack(constants::retval(), &value, &info);
                }
              }

              if let Some(MergeInfo{ merge_at, dcf_size }) = m_at_s_at.pop(){
                let current_dcf_size = current.get_dynamic_cf_size(); 
                //oops, we've busted through our merge point
                if current_dcf_size < dcf_size{
                  // so we set our merge point to where we at right now
                  m_at_s_at.push(MergeInfo { merge_at: return_pointer, dcf_size: current_dcf_size });

                  // need to reawaken our brother, if he was asleep
                  let (brother,_) = paths.pop().unwrap();
                  paths.push((brother, Status::Active()));
                  
                  // but we can go to sleep :relieved
                  paths.push((current, Status::Waiting()))
                }
                //haven't pushed through our merge point yet
                else{
                  // so we restore it as it was
                  m_at_s_at.push(MergeInfo { merge_at, dcf_size });
                  // and stay active
                  paths.push((current, Status::Active()))
                }
              }
              else{
                //we didn't have a merge point at all, how quant
                paths.push((current, Status::Active()));    
              }
            },
            Statement::Throw { message, info } => {
              let mut return_pointer   = 0;
              let mut wait_pointer = 0;
              let mut still_searching: bool = true;

              while let Some(control) = current.pop_dynamic_cf() {
                current.pop_stack();
                if let DynamicPointer::Thr(catch_entry, try_catch_next) = control {
                    still_searching = false;
                    return_pointer = catch_entry;
                    wait_pointer =try_catch_next;
                    break; 
                }
              }

              if still_searching{
                panic!("broken control flow in return statement");
              }
              
              if let Some(MergeInfo{ merge_at, dcf_size }) = m_at_s_at.pop(){
                let current_dcf_size = current.get_dynamic_cf_size(); 
                //oops, we've busted through our merge point
                if current_dcf_size < dcf_size{
                  // so we set our merge point to after the try catch block
                  m_at_s_at.push(MergeInfo { merge_at: wait_pointer, dcf_size: current_dcf_size });

                  // need to reawaken our brother, if he was asleep
                  let (brother,_) = paths.pop().unwrap();
                  paths.push((brother, Status::Active()));
                  
                }
                //haven't pushed through our merge point yet
                else{
                  // so we restore it as it was
                  m_at_s_at.push(MergeInfo { merge_at, dcf_size });
                }
              }
              //regardless of what happened, we need to stay awake.
              paths.push((current, Status::Active()));    
              
            },
            _ => unreachable!("CFGStatement::Statement should only ever be a non control statement"), 
          },
          
          CFGStatement::Ite(condition, left, right) => {
            match condition{
              //type conditions...
              Either::Right(_) => todo!(),
              Either::Left(expr) => {
                let join_at = get_join_point(flows, &left, &right); 
                let (mut then_child, mut else_child) = current.split_on(expr.clone());

                then_child.set_pointer(*left); 

                else_child.set_pointer(*right);

    
                m_at_s_at.push(MergeInfo { merge_at: join_at, dcf_size: current.get_dynamic_cf_size() });
                paths.push((current, Status::Waiting()));

            
                paths.push((else_child, Status::Active()));
                paths.push((then_child, Status::Active()));
              },
            }
          },
          CFGStatement::While(expression, b) => {

            if let Some(dyn_ptr) = current.pop_dynamic_cf(){
              if let DynamicPointer::Whl(head, next) = dyn_ptr{
                //we've been in this loop before
                if head == stmt_id{
                  // we reinsert this one in the then child
                }
                else{
                  // we haven't been in *this* while before
                  // so we shouldn't have removed it :pensive:
                  current.push_dynamic_cf(dyn_ptr);
                }
              }
              else{
                // top isn't a while at all
                // so we shouldn't have removed it
                current.push_dynamic_cf(dyn_ptr);
              }
            }

            let (mut then_child, mut else_child) = current.split_on(expression.clone());
            then_child.set_pointer(*b); 

            //get pointer to the next statement after the while
            let nexts : Vec<_> = flows
              .get(&stmt_id)
              .unwrap()
              .into_iter()
              .filter(|next| *next != b)
              .collect();

            assert!(nexts.len() == 1);
            let next = nexts[0];

            m_at_s_at.push(MergeInfo{ merge_at: *next, dcf_size: current.get_dynamic_cf_size()});                     
            paths.push((current, Status::Waiting()));

            else_child.set_pointer(*next);
            paths.push((else_child, Status::Waiting()));
            
            then_child.push_dynamic_cf(DynamicPointer::Whl(stmt_id, *next));
            paths.push((then_child, Status::Active() ));

          },
          CFGStatement::TryCatch(try_entry, try_exit, catch_entry, catch_exit) => {
            current.set_pointer(*try_entry); 

            let nexts = flows.get(&try_exit).unwrap_or_else( ||{ panic!("malformed graph") } );
            assert_eq!(nexts.len(), 1);
            let t_next = nexts.last().unwrap().clone();
        
            current.push_dynamic_cf(DynamicPointer::Thr(*catch_entry, t_next));
            paths.push((current, Status::Active()));

          },
          CFGStatement::TryEntry(_) => {
            set_to_next_pc(&mut current, flows);
            paths.push((current, Status::Active()));
          },
          CFGStatement::TryExit => {
            set_to_next_pc(&mut current, flows);
            paths.push((current, Status::Active()));
          },
          CFGStatement::CatchEntry(_) => {
            //and put a new one on top.
            set_to_next_pc(&mut current, flows);
            paths.push((current, Status::Active()));
          },
          CFGStatement::CatchExit => {
            set_to_next_pc(&mut current, flows);
            paths.push((current, Status::Active()));
          },
          CFGStatement::Seq(l, r) => {
            current.set_pointer(*l);
            paths.push((current, Status::Active()));
          },
          CFGStatement::FunctionEntry { decl_name, method_name, argument_types } => {
            todo!("check precondition");
            todo!("assign variables to stack");
            set_to_next_pc(&mut current, flows);
            paths.push((current, Status::Active()));
          },
          CFGStatement::FunctionExit { decl_name, method_name, argument_types } => {
            // simpler than a return, this can't break through an enclosing while or try block :relieved
            // and it can't possible return a value :relieved
            todo!("check postcondition"); 
            current.pop_stack();
            if let DynamicPointer::Ret(return_i, None) = current.pop_dynamic_cf().unwrap() {
              current.set_pointer(return_i);
            }
            else{
              panic!("functionexit, but not the top dynamic flow or it needs a return value?")
            }
            paths.push((current, Status::Active()));
          },
        }
      }
    }
  }

  return SymResult::Valid;
  
}

fn insert_states_function_call<P>(
  current: P,
  constraints_target_pairs: &mut Vec<(Rc<Expression>, u64)>,
  paths: &mut Vec<(P, Status)>,
  merges: &mut Vec<MergeInfo>,
  return_var: Option<Lhs>,
  return_ptr: u64) -> () where P : MergingState {
    if constraints_target_pairs.len() <= 0 {
      panic!("no function entry points found")
    }

    let mut head = current;
    while let Some((expr, entry)) = constraints_target_pairs.pop(){
      
      if constraints_target_pairs.len() > 0 {
        merges.push(MergeInfo { merge_at: return_ptr, dcf_size: head.get_dynamic_cf_size() });
      
        let (mut left, mut right) = head.split_on(expr);
        left.set_pointer(entry);
        left.push_dynamic_cf(DynamicPointer::Ret(return_ptr, return_var.clone()));
        paths.push((head, Status::Waiting()));
        paths.push((left, Status::Active()));
        head = right;
  
      }
      // last iteration
      else{
        head.assume(Either::Left(expr));
        head.set_pointer(entry);
        head.push_dynamic_cf(DynamicPointer::Ret(return_ptr, return_var.clone()));
        paths.push((head, Status::Active()));
        break;
      }
    }
}

fn get_possible_function_heads(invocation: &Invocation) -> Vec<(Rc<Expression>, u64)> {
    todo!()
}


fn set_to_next_pc<P>(top_state: &mut P, flows: &HashMap<u64, Vec<u64>>) where P : MergingState {
    let nexts = flows.get(&top_state.get_pointer()).unwrap_or_else( ||{ panic!("malformed graph") } );
    assert_eq!(nexts.len(), 1);
    let next = nexts.last().unwrap().clone();
    top_state.set_pointer(next);
}

fn get_join_point(flows: &HashMap<u64, Vec<u64>>, left: &u64, right: &u64) -> u64 {
  let l_n = flows.get(&left).unwrap_or_else( ||{ panic!("malformed graph") } ).last().unwrap().clone();
  let r_n = flows.get(&right).unwrap_or_else( ||{ panic!("malformed graph") }).last().unwrap().clone();
  assert!(l_n == r_n);
  return l_n;
}

