
use im_rc::vector;
use itertools::Either;
use itertools::Itertools;
use queues::Queue;
use z3::ast::Dynamic;

use itertools::iproduct;
use crate::dsl::{ands, negate, negative, ors, to_int_expr};
use crate::exec::constants::unreachable;
use crate::exec::heap::HeapValue;
use crate::state;
use crate::typeable::Typeable;
use crate::z3_checker;
use crate::SourcePos;
use std::borrow::Borrow;
use std::collections::HashSet;
use std::collections::HashMap;
use std::hash::Hash;
use std::rc::Rc;
use std::cell::RefCell;
pub mod cfg;

use crate::language::*;
use crate::language::syntax::Identifier;

pub(crate) enum Result{ Ok, Err }

type Stack = Vec<HashMap<Identifier, Rc<Expression>>>;
type Heap  = HashMap<i64, Rc<HeapValue>>;


pub trait MergingState : Sized {
  fn new(start: u64, cnstr: Rc<Expression>) -> Self;
  fn next_reference_id(&mut self) -> i64;
  fn path_length(&self) -> u64; 
  fn incr_path(&mut self) -> u64;

  fn get_pointer(&self) -> u64;
  fn set_pointer(&mut self, ptr: u64) -> u64;

  fn pop_stack(&mut self) -> ();
  fn push_stack(&mut self) -> ();

  fn decl(&mut self, r#type: &NonVoidType, var: &Identifier, info: &SourcePos) -> Result;
  fn assign(&mut self, lhs: &Lhs, rhs: &Rhs, info: &SourcePos) -> Result;
  fn assign_to_stack(&mut self, id:  Identifier, rhs: &Rhs, info: &SourcePos) -> Result;

  fn is_valid(&self, assertion: &Expression) -> bool;
  fn is_feasible(&self) -> bool;

  fn assume(&mut self, assumption: Either<Rc<Expression>, TypeExpr>);
  fn all_constraints(&self) -> Rc<Expression>;

  fn get_dynamic_cf_size(&self) -> usize;
  fn pop_dynamic_cf(&mut self) -> Option<DynamicPointer>;
  fn push_dynamic_cf(&mut self, dn : DynamicPointer) -> ();

  fn split_on(&self, expr: Rc<Expression>) -> (Self, Self);

  fn merge_full(&mut self, left : Self, right: Self) -> ();
  fn merge_part(&mut self, left : Self) -> ();
  
}


#[derive(PartialEq, Clone)]
pub(crate) enum DynamicPointer {
  Ret(u64, Option<Lhs>),
  Whl(u64, u64),
  Thr(u64, u64),
}
pub(crate) struct State<C, S, H>
{
  pub reference_s  : Rc<RefCell<i64>>,
  pub pointer      : u64,
  pub path_length  : u64,
  pub constraint   : C,
  pub unq_constr   : C,
  pub stack        : S,
  pub heap         : H ,
  pub dynamic_cont : Vec<DynamicPointer>, 
}

fn union_with<K,V, F>(mut left: HashMap<K,V>, mut right: HashMap<K,V>, fun: F) -> HashMap<K,V>
  where K:PartialEq, K:Eq, K:Hash, F: Fn(V,V) -> V{
    for (k, v) in right {
      if let Some(w) = left.remove(&k) {
        left.insert(k, fun(w, v));
      }
      else{
        left.insert(k, v);
      }
    }
    return left;
  }

fn union<V>(mut left: HashSet<V>, right: HashSet<V>) -> HashSet<V>
  where  V: Eq, V: Hash, {
  for elem in right{
    left.insert(elem);
  }
  return left;
}

/*
impl PState
  {

    pub(crate) fn new( pt: u64, constr : Rc<Expression>) -> Self{
      return State{
        path_length: 0,
        pointer: pt,
        constraint: Rc::new(Expression::TRUE),
        unq_constr: constr,
        stack: CTree::Leaf(vec![HashMap::new()]),
        heap : CTree::Leaf(     HashMap::new() ),
        dynamic_cont: vec![],
      }
    }
    fn split(&self, condition: Rc<Expression>) -> (Self, Self) {
      
      let top_constr = Expression::and(self.constraint, self.unq_constr);
      let negation = Expression::not(condition);
      let left = State { 
        path_length: self.path_length,
        pointer: self.pointer,
        constraint: top_constr,
        unq_constr: condition, 
        stack: self.stack, 
        heap: self.heap, 
        dynamic_cont: self.dynamic_cont.clone()
      };
      let right = State { 
        path_length: self.path_length,
        pointer: self.pointer,
        constraint: top_constr,
        unq_constr: negation, 
        stack: self.stack, 
        heap: self.heap, 
        dynamic_cont: self.dynamic_cont.clone() 
      };

      return (left, right);
    }
    
}


#[derive(PartialEq, Clone)]
pub enum CTree<C, N, L>{
  Leaf(L),
  Node((C, Box<CTree<C,N,L>>), N, (C, Box<CTree<C,N,L>>))
}

fn _pop_stack<C>(stack: &mut CTree<C, Stack, Stack>) -> () {
  match stack{
    CTree::Leaf(mut vec) => { assert!(vec.len() > 1); vec.pop(); },
    CTree::Node((_, mut l), mut vec, (_, mut r)) => {
      //funny quirk where the first frame on the node's value overlaps with the last frame of its children's values
      assert!(vec.len() >= 1);
      if vec.len() == 1 {
        vec[0] = HashMap::new();
      }
      else{
        vec.pop();
      }
      _pop_stack(&mut l);
      _pop_stack(&mut r);
    }
  }
}
fn _push_stack<C>(stack: &mut CTree<C, Stack, Stack>) -> () {
  match stack{
    CTree::Leaf(mut vec) => { vec.push(HashMap::new()); },
    CTree::Node((_, mut l), mut vec, (_, mut r)) => {
      //funny quirk where the first frame on the node's value overlaps with the last frame of its children's values
      vec.push(HashMap::new());
      _push_stack(&mut l);
      _push_stack(&mut r);
    }
  }
}



pub(crate) type PState = State
  < Rc<Expression>
  , CTree<Rc<Expression>, Stack, Stack>
  , CTree<Rc<Expression>, Heap, Heap>
  >;

pub fn predicate_merge_culled(
  parent: &mut PState,
  child: PState)
  {
    parent.pointer = child.pointer;
    let new_constr = child.unq_constr;
    parent.unq_constr = Expression::and(
      parent.unq_constr,
      new_constr
    );
    parent.path_length = child.path_length;
    
    //would be nice to combine these into one tree, really.
    parent.stack = child.stack;
    parent.heap  = child.heap;
    }

pub fn predicate_merge(
  parent:  &mut PState,
  left_child: PState,
  right_child:PState) -> ()
  {
  assert_eq!(left_child.pointer, right_child.pointer);
  parent.pointer = left_child.pointer;
  parent.path_length = std::cmp::min(left_child.path_length, right_child.path_length);

  let left_constr = left_child.unq_constr;
  let right_constr = right_child.unq_constr;
  parent.unq_constr = Expression::and(
    parent.unq_constr,
    Expression::or(left_constr, right_constr)
  );
  
  //would be nice to combine these into one tree, really.
  parent.stack = CTree::Node((left_constr, Box::new(left_child.stack)), vec![HashMap::new()],  (right_constr, Box::new(right_child.stack)));
  parent.heap  = CTree::Node((left_constr, Box::new(left_child.heap)),       HashMap::new() ,  (right_constr, Box::new(right_child.heap)));
  return;
}





impl MergingState for PState {
    fn path_length(self) -> u64 {
      return self.path_length;
    }

    fn incr_path(&mut self) -> u64 {
      self.path_length = self.path_length + 1; 
      return self.path_length;
    }

    fn get_pointer(self) -> u64 {
      return self.pointer;
    }

    fn set_pointer(&mut self, ptr: u64) -> u64 {
      self.pointer = ptr;
      return self.pointer;
    }

    fn pop_stack(&mut self) -> () {
      //ugly, why does it need to be like this?
      _pop_stack(&mut self.stack);
    }

    fn push_stack(&mut self) -> () {
      _push_stack(&mut self.stack);
    }

    fn decl(&mut self, r#type: &NonVoidType, var: &Identifier, info: &SourcePos) -> Result {
      return decl_def(&mut self.stack, r#type, var, info);
    }

    fn assign(&mut self, lhs: &Lhs, rhs: &Rhs, info: &SourcePos) -> Result {
      match rhs{
        Rhs::RhsExpression { value, type_, info } => {
          // we lookup all the required variables in the expression
          let (r_v, r_r) = _get_free_vars(value);
          // then we descend the stacktree, gathering the values until construction becomes possible
          return gather_and_insert_expr(
            &mut self.stack, &mut self.heap, lhs, value.clone(), 
            (r_v.into_iter().collect(), r_r.into_iter().collect()), 
            (HashMap::new(), HashMap::new())
          );
        },
        Rhs::RhsField { var, field, type_, info } => {
          if let Expression::Var { var, .. } = var.as_ref() {
            return gather_and_insert_field( &mut self.stack, &mut self.heap, lhs, &var, field); 
          } else {
              panic!(
                  "Currently only right hand sides of the form <variable>.<field> are allowed."
              )
          }
        },
        Rhs::RhsElem { var, index, type_, info } => {
          if let Expression::Var { var, .. } = var.as_ref() {
            return gather_and_insert_elem( &mut self.stack, &mut self.heap, lhs, var, index); 
          } else {
              panic!(
                  "Currently only right hand sides of the form <variable>[<index>] are allowed."
              )
          }
        },
        Rhs::RhsArray { array_type, sizes, type_, info } => {
          return construct_array_and_insert(&mut self.stack, &mut self.heap, lhs, array_type, sizes, type_,);
        },
        Rhs::RhsCast { cast_type, var, info } => {
          return gather_and_insert_cast(&mut self.stack, &mut self.heap, lhs, cast_type, var);
        },
        Rhs::RhsCall { .. } => unreachable!("should be handled in the graph itself"),
      }

    }

    fn assign_to_stack(&mut self, id:  Identifier, rhs: &Rhs, info: &SourcePos) -> Result {
      let id = Lhs::LhsVar { var: id, type_: rhs.type_of(), info: info.clone() };
      return self.assign(&id, rhs, info);
    }

    fn is_valid(&self, assertion: &Expression) -> bool {
        todo!()
    }

    fn is_feasible(&self) -> bool {
        todo!()
    }

    fn assume(&mut self, assumption: Either<Rc<Expression>, TypeExpr>) {
      self.unq_constr = Expression::and(self.unq_constr, assumption.left().unwrap())
    }

    fn all_constraints(&self) -> Rc<Expression> {
      return Expression::and(self.constraint, self.unq_constr);
    }

    fn get_dynamic_cf_size(self) -> usize {
      return self.dynamic_cont.len();
    }

    fn pop_dynamic_cf(&mut self) -> Option<DynamicPointer> {
      return self.dynamic_cont.pop();
    }

    fn push_dynamic_cf(&mut self, dn : DynamicPointer) -> () {
      self.dynamic_cont.push(dn);
    }

    fn split_on(&self, expr: Rc<Expression>) -> (Self, Self) {
      return self.split(expr);
    }

    fn merge_full(self: &mut Self, left : Self, right: Self) -> () {
      predicate_merge( self, left, right);
    }

    fn merge_part(self: &mut Self, left : Self) -> () {
      predicate_merge_culled(self, left);
    }
}

fn decl_def(stack: &mut CTree<Rc<Expression>, Stack, Stack>, r#type: &NonVoidType, var: &Identifier, info: &SourcePos) -> Result {
  match stack{
    CTree::Leaf(mut vec) => { 
      vec.last().unwrap().insert(*var, Rc::new(r#type.default())); 
    },
    CTree::Node(mut l, mut vec, mut r) => { 
      vec.last().unwrap().insert(*var, Rc::new(r#type.default())); 
      decl_def(&mut l.1, r#type, var, info);
      decl_def(&mut r.1, r#type, var, info);
    },
    _ => return Result::Err
  }
  return Result::Ok
}

fn gather_and_insert_cast(stack: &mut CTree<Rc<Expression>, Stack, Stack>, heap: &mut CTree<Rc<Expression>, Heap, Heap>, lhs: &Lhs, cast_type: &NonVoidType, var: &str) -> Result {
    todo!()
}

fn construct_array_and_insert(stack: &mut CTree<Rc<Expression>, Stack, Stack>, heap: &mut CTree<Rc<Expression>, Heap, Heap>, lhs: &Lhs, array_type: &NonVoidType, sizes: &Vec<Rc<Expression>>, r#type: &RuntimeType) -> Result {
    todo!()
}

fn gather_and_insert_elem(stack: &mut CTree<Rc<Expression>, Stack, Stack>, heap: &mut CTree<Rc<Expression>, Heap, Heap>, 
  id: &Lhs, var: &str, index: &Expression) -> Result {
    todo!()
}

fn gather_and_insert_field(stack: &mut CTree<Rc<Expression>, Stack, Stack>, heap: &mut CTree<Rc<Expression>, Heap, Heap>, id: &Lhs, 
  var: &Identifier, field: &Identifier)  -> Result {
    match (stack, heap){
        (CTree::Leaf(mut s), CTree::Leaf(mut h)) => {
          let frame = s.last().unwrap();
          if let Some(var) = frame.get(&var){
            match var.as_ref() {
              Expression::Lit { lit: Lit::NullLit, ..} => {
                return Result::Err;
              },
              Expression::Ref{ ref_, ..  } => {

              },
              _ => return Result::Err,
            }
          }
          else{
            return Result::Err;
          }
        },
        (CTree::Node(mut ls, mut s, mut rs), CTree::Node(mut lh, mut h, mut rh)) => {

        },
        _ => return Result::Err,
    }
    return Result::Ok;
  }


fn gather_and_insert_expr<C>(
  mut stack: CTree<C, Stack, Stack>, 
  mut heap: CTree<C, Heap, Heap>, 
  id: &Lhs, 
  ex: Rc<Expression>, 
  (mut r_v, mut r_r): (Vec<Identifier>, Vec<i64>), 
  (mut c_v, mut c_r): (HashMap<Identifier, Rc<Expression>>, HashMap<i64, Rc<HeapValue>>)) -> Result {
    match (stack, heap){
        (CTree::Leaf(mut s), CTree::Leaf(mut h)) => {
          // we are at a leaf, so if at the end the required variables aren't satisfied, then this branch has failed!
          let frame = s.last().unwrap();
          while let Some(v) = r_v.pop(){
            if let Some(e) = frame.get(&v){
              c_v.insert(v, e.clone());
            }
            else{
              return Result::Err
            }
          }
          while let Some(r) = r_r.pop(){
            if let Some(e) = h.get(&r){
              c_r.insert(r, e.clone());
            }
            else{
              return Result::Err
            }
          }

          if let Some(final_ex) = construct_expr(ex, &mut c_v, &mut c_r){
            match id{
              Lhs::LhsVar { var, type_, info } => {
                frame.insert(var.clone(), final_ex);
              },
              Lhs::LhsField { var, var_type, field, type_, info } => todo!(),
              Lhs::LhsElem { var, index, type_, info } => todo!(),
            }
            return Result::Ok;   
          }
          else{
            return Result::Err
          }
        },
        (CTree::Node(mut ls, mut s, mut rs), CTree::Node(mut lh, mut h, mut rh)) => {
          let mut r_w = vec![];
          let mut frame = s.last().unwrap();

          while let Some(v) = r_v.pop(){
            if let Some(e) = frame.get(&v){
              c_v.insert(v, e.clone());
            }
            else{
              r_w.push(v);
            }
          }
          let mut r_l = vec![];
          for r in r_r{
            while let Some(r) = r_r.pop(){
              if let Some(e) = h.get(&r){
                c_r.insert(r, e.clone());
              }
              else{
                r_l.push(r);
              }
            }  
          }
          // we have all the values we need at this 'level' of the CTree
          if r_w.is_empty() && r_l.is_empty(){
            if let Some(final_ex) = construct_expr(ex, &mut c_v, &mut c_r){
            match id{
                Lhs::LhsVar { var, type_, info } => {
                  frame.insert(var.clone(), final_ex);
                },
                Lhs::LhsField { var, var_type, field, type_, info } => todo!(),
                Lhs::LhsElem { var, index, type_, info } => todo!(),
            }
            return Result::Ok;
          }
          else{
            return Result::Err;
          }
            
          }
          else{
            let l = gather_and_insert_expr(ls.1.as_mut(), lh.1.as_mut(), id, ex, (r_w, r_l).clone(), (c_v, c_r).clone());
            let r = gather_and_insert_expr(rs.1.as_mut(), rh.1.as_mut(), id, ex, (r_w, r_l), (c_v, c_r));
            if let (Result::Ok, Result::Ok) = (l, r){
              return Result::Ok;
            }
            else{
              return Result::Err;
            }
          }
        },
        (_, _) => { return Result::Err; } 
    }


}

fn construct_expr(ex: Rc<Expression>,  c_v: &mut HashMap<Identifier, Rc<Expression>>, c_r: &mut HashMap<i64, Rc<HeapValue>>) -> Option<Rc<Expression>> {
    match ex.borrow() {
      Expression::Forall { elem, range, domain, formula, type_, info } => {
        // elem is not a free variable in formula
        let v : Option<Rc<Expression>> = c_v.remove(elem);
        let new_form = construct_expr(formula.clone(), c_v, c_r)?;
        if let Some(v) = v{
          c_v.insert(elem.clone(), v);
        }

        return Some(Rc::new(Expression::Forall{ 
          elem:elem.clone(), 
          range:range.clone(), 
          domain:domain.clone(), 
          formula: new_form, 
          type_: type_.clone(), 
          info: info.clone() 
        }))
      },
      Expression::Exists { elem, range, domain, formula, type_, info } => {
        let v : Option<Rc<Expression>> = c_v.remove(elem);
        let new_form = construct_expr(formula.clone(), c_v, c_r)?;
        if let Some(v) = v{
          c_v.insert(elem.clone(), v);
        }

        return Some(Rc::new(Expression::Exists{ 
          elem:elem.clone(), 
          range:range.clone(), 
          domain:domain.clone(), 
          formula: new_form, 
          type_: type_.clone(), 
          info: info.clone() 
        }))
        
      },
      Expression::BinOp { bin_op, lhs, rhs, type_, info } => {
        let new_lhs : Rc<Expression> = construct_expr(lhs.clone(), c_v, c_r)?;
        let new_rhs : Rc<Expression> = construct_expr(rhs.clone(), c_v, c_r)?;

        return Some(simplify_bin_op(&bin_op, &type_, &info, new_lhs, new_rhs))
        
      },
      Expression::UnOp { un_op, value, type_, info } => {
        let new_value : Rc<Expression> = construct_expr(value.clone(), c_v, c_r)?;
        return Some(simplify_un_op(&un_op, &type_, &info, new_value));
      },
      Expression::Var { var, type_, info } => {
        if let Some(expr) = c_v.get(var){
          return Some(expr.clone());
        }
        else{
          // this must be a existential, then
          return Some(ex.clone());
        }
      },
      Expression::SizeOf { var, type_, info } => { 
        // its possible we want to see if var resolves to a clean instance of an Ref
        // which we can then take the size of, but for now we do nothing
        let expr : Option<&Rc<Expression>> = c_v.get(&var);
        match expr {
          Some(expr) => { 
            match expr.as_ref(){
              Expression::Lit { lit: Lit::NullLit, ..} => {
                  // infeasible path
                  return None;
                },
              Expression::Ref { ref_, .. } => {
                  if let Some(HeapValue::ArrayValue { elements, .. }) = c_r.get(ref_).map(|rc|{rc.as_ref()}) {
                    return Some(Expression::int(elements.len() as i64));
                  }
                  else{
                    //size of Object!?
                    return None;
                  }
              },
              _ => return Some(ex.clone()),
            }
          },
          _ => return Some(ex.clone()),
        }
      },
      Expression::Ref { ref_, type_, info } => return Some(ex.clone()),
      Expression::Conditional { guard, true_, false_, type_, info } => {
        let new_guard = construct_expr(guard.clone(), c_v, c_r)?;
        let new_true = construct_expr(true_.clone(), c_v, c_r)?;
        let new_false = construct_expr(false_.clone(), c_v, c_r)?;

        if let Some(Lit::BoolLit { bool_value }) = try_get_lit(new_guard.as_ref()){
          if bool_value{
            return Some(new_true);
          }
          else{
            return Some(new_false);
          }
        }
        else{
          return Some(
            Rc::new(Expression::Conditional { guard: new_guard, true_: new_true, false_: new_false, type_: type_.clone(), info: info.clone() })
          )
        }
      },
      Expression::SymbolicVar { var, type_, info } => { return Some(ex.clone()) },
      Expression::SymbolicRef { var, type_, info } => { return Some(ex.clone()) },
      Expression::Lit { lit, type_, info }                => { return Some(ex.clone()) },
    }
}

fn simplify_un_op(un_op: &UnOp, type_: &RuntimeType, info: &SourcePos, new_value: Rc<Expression>) -> Rc<Expression> {
    match (un_op, try_get_lit(&new_value)){
        (UnOp::Negative, Some(Lit::IntLit { int_value })) => {
          let v = Lit::IntLit { int_value: -int_value };
          return Rc::new(Expression::Lit { lit: v, type_: type_.clone(), info: info.clone() });
        },
        (UnOp::Negative, Some(Lit::FloatLit { float_value })) => {
          let v = Lit::FloatLit { float_value: -float_value };
          return Rc::new(Expression::Lit { lit: v, type_: type_.clone(), info: info.clone() });
        },
        (UnOp::Negate, Some(Lit::BoolLit { bool_value })) => {
          let v = Lit::BoolLit { bool_value: !bool_value };
          return Rc::new(Expression::Lit { lit: v, type_: type_.clone(), info: info.clone() });

        },
        (_, _) => Rc::new(Expression::UnOp { un_op: un_op.clone(), value: new_value, type_: type_.clone(), info: info.clone() })

      }
}

fn simplify_bin_op(bin_op: &BinOp, type_: &RuntimeType, info: &SourcePos, new_lhs: Rc<Expression>, new_rhs: Rc<Expression>) -> Rc<Expression> {
    match (bin_op, try_get_lit(&new_lhs), try_get_lit(&new_rhs)){
        (BinOp::Implies, _, Some(Lit::BoolLit { bool_value: true })) => {
          let value = Lit::BoolLit { bool_value: true };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },
        (BinOp::Implies, Some(Lit::BoolLit { bool_value: false }), _) => {
          let value = Lit::BoolLit { bool_value: true };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },
        (BinOp::And, Some(Lit::BoolLit { bool_value: l }), Some(Lit::BoolLit { bool_value: r })) => {
          let value = Lit::BoolLit { bool_value: !l || r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },


        (BinOp::And, Some(Lit::BoolLit { bool_value: false }), _) => {
          let value = Lit::BoolLit { bool_value: false };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },
        (BinOp::And, _, Some(Lit::BoolLit { bool_value: false })) => {
          let value = Lit::BoolLit { bool_value: false };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },
        (BinOp::And, Some(Lit::BoolLit { bool_value: l }), Some(Lit::BoolLit { bool_value: r })) => {
          let value = Lit::BoolLit { bool_value: l && r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },
    
        (BinOp::Or, Some(Lit::BoolLit { bool_value: true }), _) => {
          let value = Lit::BoolLit { bool_value: true };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },
        (BinOp::Or, _, Some(Lit::BoolLit { bool_value: true })) => {
          let value = Lit::BoolLit { bool_value: true };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },
        (BinOp::Or, Some(Lit::BoolLit { bool_value: l }), Some(Lit::BoolLit { bool_value: r })) => {
          let value = Lit::BoolLit { bool_value: l || r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },

        (BinOp::Equal, Some(Lit::IntLit { int_value: l }), Some(Lit::IntLit { int_value: r })) => {
          let value = Lit::BoolLit { bool_value: l == r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        }
        (BinOp::Equal, Some(Lit::FloatLit { float_value: l }), Some(Lit::FloatLit { float_value: r })) => {
          let value = Lit::BoolLit { bool_value: l == r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },
        (BinOp::Equal, Some(Lit::BoolLit { bool_value: l }), Some(Lit::BoolLit { bool_value: r })) => {
          let value = Lit::BoolLit { bool_value: l == r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },

        (BinOp::NotEqual, Some(Lit::IntLit { int_value: l }), Some(Lit::IntLit { int_value: r })) => {
          let value = Lit::BoolLit { bool_value: l != r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        }
        (BinOp::NotEqual, Some(Lit::FloatLit { float_value: l }), Some(Lit::FloatLit { float_value: r })) => {
          let value = Lit::BoolLit { bool_value: l != r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },
        (BinOp::NotEqual, Some(Lit::BoolLit { bool_value: l }), Some(Lit::BoolLit { bool_value: r })) => {
          let value = Lit::BoolLit { bool_value: l != r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },

        (BinOp::LessThan, Some(Lit::IntLit { int_value: l }), Some(Lit::IntLit { int_value: r })) => {
          let value = Lit::BoolLit { bool_value: l < r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        }
        (BinOp::LessThan, Some(Lit::FloatLit { float_value: l }), Some(Lit::FloatLit { float_value: r })) => {
          let value = Lit::BoolLit { bool_value: l < r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },

        (BinOp::LessThanEqual, Some(Lit::IntLit { int_value: l }), Some(Lit::IntLit { int_value: r })) => {
          let value = Lit::BoolLit { bool_value: l <= r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        }
        (BinOp::LessThanEqual, Some(Lit::FloatLit { float_value: l }), Some(Lit::FloatLit { float_value: r })) => {
          let value = Lit::BoolLit { bool_value: l <= r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },

        (BinOp::GreaterThan, Some(Lit::IntLit { int_value: l }), Some(Lit::IntLit { int_value: r })) => {
          let value = Lit::BoolLit { bool_value: l > r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        }
        (BinOp::GreaterThan, Some(Lit::FloatLit { float_value: l }), Some(Lit::FloatLit { float_value: r })) => {
          let value = Lit::BoolLit { bool_value: l > r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },

        (BinOp::GreaterThanEqual, Some(Lit::IntLit { int_value: l }), Some(Lit::IntLit { int_value: r })) => {
          let value = Lit::BoolLit { bool_value: l >= r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        }
        (BinOp::GreaterThanEqual, Some(Lit::FloatLit { float_value: l }), Some(Lit::FloatLit { float_value: r })) => {
          let value = Lit::BoolLit { bool_value: l >= r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },

        (BinOp::Plus, Some(Lit::IntLit { int_value: l }), Some(Lit::IntLit { int_value: r })) => {
          let value = Lit::IntLit { int_value: l + r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        }
        (BinOp::Plus, Some(Lit::FloatLit { float_value: l }), Some(Lit::FloatLit { float_value: r })) => {
          let value = Lit::FloatLit { float_value: l + r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },

        (BinOp::Minus, Some(Lit::IntLit { int_value: l }), Some(Lit::IntLit { int_value: r })) => {
          let value = Lit::IntLit { int_value: l - r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        }
        (BinOp::Minus, Some(Lit::FloatLit { float_value: l }), Some(Lit::FloatLit { float_value: r })) => {
          let value = Lit::FloatLit { float_value: l - r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },

        (BinOp::Multiply, Some(Lit::IntLit { int_value: l }), Some(Lit::IntLit { int_value: r })) => {
          let value = Lit::IntLit { int_value: l * r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        }
        (BinOp::Multiply, Some(Lit::FloatLit { float_value: l }), Some(Lit::FloatLit { float_value: r })) => {
          let value = Lit::FloatLit { float_value: l * r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },
    
        (BinOp::Divide, Some(Lit::IntLit { int_value: l }), Some(Lit::IntLit { int_value: r })) => {
          let value = Lit::IntLit { int_value: l / r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        }
        (BinOp::Divide, Some(Lit::FloatLit { float_value: l }), Some(Lit::FloatLit { float_value: r })) => {
          let value = Lit::FloatLit { float_value: l / r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },

        (BinOp::Modulo, Some(Lit::IntLit { int_value: l }), Some(Lit::IntLit { int_value: r })) => {
          let value = Lit::IntLit { int_value: l % r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },
        (BinOp::Modulo, Some(Lit::FloatLit { float_value: l }), Some(Lit::FloatLit { float_value: r })) => {
          let value = Lit::FloatLit  { float_value: l % r };
          return Rc::new(Expression::Lit { lit: value, type_: type_.clone(), info: info.clone() });
        },

        (_, _, _) => return Rc::new(Expression::BinOp{bin_op: bin_op.clone(), lhs: new_lhs, rhs: new_rhs, type_: type_.clone(), info: info.clone()})
      }
}

fn try_get_lit(expr: &Expression) -> Option<Lit> {
  match expr{
    Expression::Lit { lit, .. } => Some(lit.clone()),
    _ => None
  }
}

fn _get_free_vars(value: &Expression) -> (HashSet<Identifier>, HashSet<i64>) {
  match value{
    Expression::Forall { elem, range, domain, formula, type_, info } => {
      let (mut l, r) = _get_free_vars(formula);
      l.remove(elem);
      return (l,r);
    } 
    ,
    Expression::Exists { elem, range, domain, formula, type_, info } => {
      let (mut l, r) = _get_free_vars(formula);
      l.remove(elem);
      return (l,r);
    },
    Expression::BinOp { bin_op, lhs, rhs, type_, info } => {
      let (mut l1, l2) = _get_free_vars(lhs);
      let (mut r1, r2) = _get_free_vars(rhs);
      return (union(l1,r1), union(l2,r2));
    },
    Expression::UnOp { un_op, value, type_, info } => _get_free_vars(value),
    Expression::Var { var, type_, info } => { 
      let mut res = HashSet::new();
      res.insert(var.clone());
      return (res, HashSet::new());
    },
    Expression::SymbolicVar { var, type_, info } => {
      return (HashSet::new(), HashSet::new());
    },
    Expression::Lit { lit, type_, info } => {
      return (HashSet::new(), HashSet::new());
    },
    Expression::SizeOf { var, type_, info } => {
      let mut res = HashSet::new();
      res.insert(var.clone());
      return (res, HashSet::new());
    }
    Expression::Ref { ref_, type_, info } => {
      let mut res = HashSet::new();
      res.insert(ref_.clone());
      return (HashSet::new(), res);
    },
    Expression::SymbolicRef { var, type_, info } => {
      return (HashSet::new(), HashSet::new());
    },
    Expression::Conditional { guard, true_, false_, type_, info } => {
      let (mut gv, mut gr) = _get_free_vars(guard);
      let (tv, tr) = _get_free_vars(true_);
      let (fv, fr) = _get_free_vars(false_);

      return (
        union(union(gv,tv), fv),
        union(union(gr,tr), fr),
      )
    },
  };
  return (HashSet::new(), HashSet::new())
}
*/

type MValue = HashSet<Rc<Expression>>;
type MStack = Vec<HashMap<Identifier, MValue>>;
type MHeap  = HashMap<i64, HashSet<HeapValue>>;
pub(crate) type MState = State<Rc<Expression>, MStack, MHeap>; 

impl MergingState for MState {
  fn new( pt: u64, constr : Rc<Expression>) -> Self{
    return State{
      reference_s: Rc::new(RefCell::new(0)),
      path_length: 0,
      pointer: pt,
      constraint: Rc::new(Expression::TRUE),
      unq_constr: constr,
      stack: vec![HashMap::new()],
      heap : HashMap::new(),
      dynamic_cont: vec![],
    }
  }

  fn next_reference_id(&mut self) -> i64 {
    let mut s_ref = self.reference_s.as_ref().borrow_mut();
    let s = s_ref.clone();
    *s_ref = s+1;
    return s;
  }
  fn path_length(&self) -> u64 {
    return self.path_length.clone();
  }

  fn incr_path(&mut self) -> u64 {
    self.path_length = self.path_length + 1; 
    return self.path_length.clone();
  }

  fn get_pointer(&self) -> u64 {
    return self.pointer.clone();
  }

  fn set_pointer(&mut self, ptr: u64) -> u64 {
    self.pointer = ptr;
    return self.pointer.clone();
  }

  fn pop_stack(&mut self) -> () {
    //ugly, why does it need to be like this?
    if self.stack.len() > 1{
      self.stack.pop();
    }
    else if self.stack.len() == 1{
      self.stack[0] = HashMap::new();
    }
    else{
      unreachable!("stack should always be at least 1 long");
    }
  }

  fn push_stack(&mut self) -> () {
    self.stack.push(HashMap::new());
  }

  fn decl(&mut self, r#type: &NonVoidType, var: &Identifier, _info: &SourcePos) -> Result {
    let mut set = HashSet::new();
    set.insert(Rc::new(r#type.default()));
    self.stack.last_mut().map(| frame |{ frame.insert(var.clone(), set) } );
    return Result::Ok;
  }

  fn assign(&mut self, lhs: &Lhs, rhs: &Rhs, _info: &SourcePos) -> Result {

    let r = self.next_reference_id();
    match lhs{
      Lhs::LhsVar { var, .. } => {
        
        if let Some(value_set) = gen_expr_set(rhs, &mut self.stack, &mut self.heap, r){
          return assign_var_set(&mut self.stack, var, value_set);
        }
        else{
          return Result::Err;
        }
      },
      Lhs::LhsField { var, field, .. } => {
        if let Some(value_set) = gen_expr_set(rhs, &mut self.stack, &mut self.heap, r){
          return assign_field_set(&mut self.stack, &mut self.heap, var, field, value_set);
        }
        else{
          return Result::Err;
        }
      },
      Lhs::LhsElem { var, index, .. } => {
        if let Some(value_set) = gen_expr_set(rhs, &mut self.stack, &mut self.heap, r){
          let is :HashSet<usize> = evaluate_as_ints(index.clone(), &self.stack, &self.heap, ).into_iter().map(|i|{i.expect_right("") as usize}).collect();
          return assign_elem_set(&mut self.stack, &mut self.heap, var, is, value_set);
        }
        else{
          return Result::Err;
        }

      },
    }
  }

  fn assign_to_stack(&mut self, id:  Identifier, rhs: &Rhs, info: &SourcePos) -> Result {
    let id = Lhs::LhsVar { var: id, type_: rhs.type_of(), info: info.clone() };
    return self.assign(&id, rhs, info);
  }

  fn is_valid(&self, assertion: &Expression) -> bool {
    let precons = eval_locally(self.all_constraints(), &self.stack, &self.heap);
    let postcons = eval_locally(Rc::new(assertion.clone()), &self.stack, &self.heap);

    let mut expr = Rc::new(Expression::TRUE);
    for (precon, postcon) in iproduct!(precons.iter(), postcons.iter()) {
      expr = Expression::and(expr, Expression::implies(precon.clone(), postcon.clone()));
    }
    match z3_checker::concretization::verify(expr.as_ref()){
        z3::SatResult::Unsat => return false,
        _ => return true,
    }
  }

  fn is_feasible(&self) -> bool {
    let precons = eval_locally(self.all_constraints(), &self.stack, &self.heap);
    let mut expr = Rc::new(Expression::FALSE);
    for precon in precons{
      expr = Expression::or(expr, precon.clone());
    }
    match z3_checker::concretization::verify(expr.as_ref()){
        z3::SatResult::Unsat => return false,
        _ => return true,
    }
  }

  fn assume(&mut self, assumption: Either<Rc<Expression>, TypeExpr>) {
    self.unq_constr = Expression::and(self.unq_constr.clone(), assumption.left().unwrap())
  }

  fn all_constraints(&self) -> Rc<Expression> {
    return Expression::and(self.constraint.clone(), self.unq_constr.clone());
  }

  fn get_dynamic_cf_size(&self) -> usize {
    return self.dynamic_cont.len();
  }

  fn pop_dynamic_cf(&mut self) -> Option<DynamicPointer> {
    return self.dynamic_cont.pop();
  }

  fn push_dynamic_cf(&mut self, dn : DynamicPointer) -> () {
    self.dynamic_cont.push(dn);
  }

  fn split_on(&self, expr: Rc<Expression>) -> (Self, Self) {
    let top_constr = Expression::and(self.constraint.clone(), self.unq_constr.clone());
    let negation = Expression::not(expr.clone());
    let left = State { 
      reference_s: self.reference_s.clone(),
      path_length: self.path_length,
      pointer: self.pointer,
      constraint: top_constr.clone(),
      unq_constr: expr.clone(), 
      stack: self.stack.clone(), 
      heap: self.heap.clone(), 
      dynamic_cont: self.dynamic_cont.clone()
    };
    let right = State { 
      reference_s: self.reference_s.clone(),
      path_length: self.path_length,
      pointer: self.pointer,
      constraint: top_constr.clone(),
      unq_constr: negation, 
      stack: self.stack.clone(), 
      heap: self.heap.clone(), 
      dynamic_cont: self.dynamic_cont.clone() 
    };

    return (left, right);
  }

  fn merge_full(&mut self, left : Self, right: Self) -> () {
    assert_eq!(self.stack.len(), left.stack.len());
    assert_eq!(self.stack.len(), right.stack.len());
    assert_eq!(left.pointer, right.pointer);

    self.pointer = left.pointer;
    self.path_length = std::cmp::min(left.path_length, right.path_length);
  
    self.unq_constr = Expression::and(
      self.unq_constr.clone(),
      Expression::or(left.unq_constr, right.unq_constr)
    );
  
    let paired  =  left.stack.into_iter().zip(right.stack);

    self.heap = union_with(left.heap, right.heap,
       |v, w|{ union(v, w )});
    self.stack = paired.map(|(frame_1, frame_2)|{
      union_with(frame_1, frame_2, |v, w|{ union(v, w )})
    }).collect();
  }

  fn merge_part(&mut self, left : Self) -> () {
    assert_eq!(self.stack.len(), left.stack.len());

    self.pointer = left.pointer;
    self.path_length = left.path_length;
  
    self.unq_constr = Expression::and(
      self.unq_constr.clone(),
      left.unq_constr
    );


    self.heap = left.heap;
    self.stack = left.stack;
    return;  
  }
}

fn gen_expr_set(rhs: &Rhs, stack: &mut MStack, heap: &mut MHeap, r: i64) -> Option<HashSet<Rc<Expression>>> {
  match rhs{
    Rhs::RhsExpression { value, .. } => return Some(eval_locally(value.clone(), stack, heap)),
    Rhs::RhsField { var, field, .. } => {
      let mut result = HashSet::new();
      let exprs = eval_locally(var.clone(), stack, heap);
      for expr in exprs{
        if let Expression::Var { var, .. } = expr.as_ref() {
          let references = stack.last().unwrap().get(&var).unwrap();
          for reference in references{
            match reference.as_ref() {
              Expression::Ref { ref_, .. } => {
                let heap_obs = heap[&ref_].clone();
                for obj in heap_obs{
                  
                  if let HeapValue::ObjectValue { fields, .. } = obj{
                    result.insert(fields[field].clone());
                  }
                  else{
                    return None;
                  }    
                }
              }
              Expression::Lit { lit: Lit::NullLit, .. } =>{
                return None;
              }
              _ => {
                //this should be a panic, because its our fault.
                panic!("trying to get field of unknown ref")
              }
            }
          }
        } else {
          panic!(
              "Currently only right hand sides of the form <variable>.<field> are allowed."
          )
        }
      }
      return Some(result);
    },
    Rhs::RhsElem { var, index, .. } => {
      let mut result = HashSet::new();
      let exprs = eval_locally(var.clone(), stack, heap);
      let is: HashSet<usize>    = evaluate_as_ints(index.clone(), stack, heap, ).into_iter().map(|i|{i.expect_right("") as usize}).collect();
      for (expr, i) in iproduct!(exprs.iter(), is.iter()){
        if let Expression::Var { var, .. } = expr.as_ref() {
          let references = stack.last().unwrap().get(&var).unwrap();
          for reference in references{
            match reference.as_ref() {
              Expression::Ref { ref_, .. } => {
                let heap_obs = heap[&ref_].clone();
                for obj in heap_obs{
                  if let HeapValue::ArrayValue { elements, .. } = obj{
                    result.insert(elements[*i].clone());
                  }
                  else{
                    return None;
                  }    
                }
              }
              Expression::Lit { lit: Lit::NullLit, .. } =>{
                return None;
              }
              _ => {
                //this should be a panic, because its our fault.
                panic!("trying to get field of unknown ref")
              }
            }
          }
        } else {
          panic!(
              "Currently only right hand sides of the form <variable>.<field> are allowed."
          )
        }
      }
      return Some(result);
    },
    Rhs::RhsCall { invocation, type_, info } =>{
      unreachable!("should be handled before getting here")
    },
    Rhs::RhsArray { array_type, sizes, type_, info } => {
      let ref_ = Rc::new(Expression::Ref {
        ref_: r,
        type_: type_.clone(),
        info: SourcePos::UnknownPosition,
      });
      let mut return_refs = HashSet::new();
      return_refs.insert(ref_);

      assert!(sizes.len() == 1, "Support for only 1D arrays");
      let sizes : HashSet<i64> = evaluate_as_ints(sizes[0].clone(), stack, heap, ).into_iter().map(|i|{i.expect_right("")}).collect();

      let mut arrs = HashSet::new();
      for size in sizes.into_iter(){
        // int[][] a = new int[10][10]
        let array = (0..size)
            .map(|_| Rc::new(array_type.default()))
            .collect_vec();
    
        arrs.insert(
            HeapValue::ArrayValue {
                elements: array,
                type_: type_.clone(),
            },
        );
      }
      heap.insert(r, arrs);
      return Some(return_refs);
    },
    Rhs::RhsCast { .. } => todo!(),
  }
}

fn evaluate_as_ints(  expression: Rc<Expression>,
  stack: &MStack,
  heap:  &MHeap,
)-> HashSet<Either<Rc<Expression>, i64>> {
  let expressions = eval_locally(expression, stack, heap);
  let mut res= HashSet::new();
  for expr in expressions{
    if let Expression::Lit {
      lit: Lit::IntLit { int_value },
      ..
    } = expr.clone().as_ref()
    {
      res.insert(Either::Right(*int_value));
    } else {
      res.insert(Either::Left(expr.clone()));
    }

  }
  return res;
  
  }

fn assign_var_set(stack: &mut MStack, var: &Identifier, value: MValue) -> Result {
  stack.last_mut().map(|frame|{
    frame.insert(var.clone(), value);
  });
  return Result::Ok;
}

fn assign_field_set(stack: &mut MStack, heap: &mut MHeap, var: &Identifier, field: &Identifier, value_set: MValue) -> Result {
  let frame = stack.last().unwrap();
  if let Some(ref_set) = frame.get(var){
    for r in ref_set.clone(){
      match r.as_ref(){
        Expression::Lit{ lit: Lit::NullLit, .. } => {
          //this is a (possibly false positive) null pointer exception
          return Result::Err;
        }  
        Expression::Ref { ref_, .. } => {
          let old_objects: &mut HashSet<HeapValue> = heap.get_mut(&ref_).unwrap();
          let mut new_objects: HashSet<HeapValue> = HashSet::new();

          for (object, value) in iproduct!(old_objects.iter(), value_set.iter()){
            if let HeapValue::ObjectValue { mut fields, type_ } = object.clone(){
              fields.remove(field);
              fields.insert(field.clone(), value.clone());
              new_objects.insert(HeapValue::ObjectValue{ fields: fields.clone(), type_: type_.clone()});
            }
            else{
              // type error
              // and this *really* is an error
              return Result::Err
            }
          }
          heap.remove(&ref_);
          heap.insert(*ref_, new_objects);

        }
        _ => return Result::Err
      }
    }
    return Result::Ok;
  }
  else{
    return Result::Err;
  }
}


fn assign_elem_set(stack: &mut MStack, heap: &mut MHeap, var: &Identifier, index_set: HashSet<usize>, value_set: MValue) -> Result {
  let frame = stack.last().unwrap();
  if let Some(ref_set) = frame.get(var){
    for r in ref_set.clone(){
      match r.as_ref(){
        Expression::Lit{ lit: Lit::NullLit, .. } => {
          //this is a (possibly false positive) null pointer exception
          return Result::Err;
        }  
        Expression::Ref { ref_, .. } => {
          let old_arrs: &mut HashSet<HeapValue> = heap.get_mut(&ref_).unwrap();
          let mut new_arrs: HashSet<HeapValue> = HashSet::new();

          for (object, (index, value)) in iproduct!(old_arrs.iter(), index_set.iter().zip(value_set.iter())){
            if let HeapValue::ArrayValue { mut elements, type_ } = object.clone(){
              elements[*index] = value.clone();
              new_arrs.insert(HeapValue::ArrayValue{ elements, type_: type_.clone()});
            }
            else{
              // type error
              // and this *really* is an error
              return Result::Err
            }
          }
          heap.remove(&ref_);
          heap.insert(*ref_, new_arrs);
        },
        _ => { return Result::Err; }
      }
    }
    return Result::Ok;
  }
  else{
    return Result::Err;
  }
}






fn eval_locally(
  expression: Rc<Expression>,
  stack: &MStack,
  heap:  &MHeap,
) -> HashSet<Rc<Expression>> {
  match expression.as_ref() {
      Expression::BinOp {
          bin_op, lhs, rhs, ..
      } => {
          let lhss = eval_locally(lhs.clone(), stack, heap);
          let rhss = eval_locally(rhs.clone(), stack, heap);
          return iproduct!(lhss.iter(), rhss.iter()).map(|(lhs, rhs)|{
            evaluate_binop(*bin_op, lhs.clone(), rhs.clone(), stack, heap)
          }).collect()
      }
      Expression::UnOp { un_op, value, .. } => {
          let values = eval_locally(value.clone(), stack, heap);
          return values.into_iter().map(|value|{ evaluate_unop(un_op.clone(), value.clone(), stack, heap)}).collect()
      }
      Expression::Var { var, .. } => {
          let os = stack
              .last().unwrap()
              .get(&var)
              .unwrap_or_else(|| panic!("infeasible, object does not exist: {:?}", var));

          return os.into_iter().flat_map(|o|{eval_locally(o.clone(), stack, heap)}).collect();
      }
      Expression::SymbolicVar { .. } => {
        let mut r = HashSet::new();
        r.insert(expression);
        return r;
      },
      Expression::Lit { .. } => {
        let mut r = HashSet::new();
        r.insert(expression);
        return r;
      },
      Expression::SizeOf { .. } => {
        todo!();
      }
      Expression::Ref { .. } => {
        let mut r = HashSet::new();
        r.insert(expression);
        return r;
      },
      Expression::SymbolicRef { .. } => { todo!(); }
      Expression::Conditional {
          guard,
          true_,
          false_,
          type_,
          info,
      } => {
          let guards = eval_locally(guard.clone(), stack, heap);
          let trues = eval_locally(true_.clone(), stack, heap);
          let falses = eval_locally(false_.clone(), stack, heap);

          return iproduct!(guards.iter(), trues.iter(), falses.iter()).map(|(guard, true_, false_)|{
            match guard.as_ref() {
              Expression::Lit {
                  lit: Lit::BoolLit { bool_value: true },
                  ..
              } => true_.clone(),

              Expression::Lit {
                  lit: Lit::BoolLit { bool_value: false },
                  ..
              } => false_.clone(),
              _ => Rc::new(Expression::Conditional {
                  guard:  guard.clone(),
                  true_:  true_.clone(),
                  false_: false_.clone(),
                  type_:  type_.clone(),
                  info:   *info,
              }),
            }
          }).collect()
      },
      Expression::Forall {..} => todo!(),
      Expression::Exists {..} => todo!(),
  }
}

fn evaluate_binop(bin_op: BinOp, lhs: Rc<Expression>, rhs: Rc<Expression>, _stack: &MStack, _heap: &MHeap,
) -> Rc<Expression> {
  use crate::syntax::BinOp::*;
  use crate::syntax::Lit::*;
  use Expression::*;

  // dbg!(&bin_op, lhs, rhs);

  match (bin_op, lhs.as_ref(), rhs.as_ref()) {
      // Boolean evaluation
      (
          bin_op,
          Lit {
              lit: BoolLit { bool_value: a },
              ..
          },
          Lit {
              lit: BoolLit { bool_value: b },
              ..
          },
      ) => match bin_op {
          Implies => Expression::bool(!a || *b),
          And => Expression::bool(*a && *b),
          Or => Expression::bool(*a || *b),
          Equal => Expression::bool(*a == *b),
          NotEqual => Expression::bool(*a != *b),
          _ => panic!("unsupported boolean operator"),
      },
      (
          bin_op,
          Lit {
              lit: BoolLit { bool_value: a },
              ..
          },
          _rhs,
      ) => match bin_op {
          Implies => {
              if *a {
                  rhs
              } else {
                  Rc::new(Expression::TRUE)
              }
          }
          And => {
              if *a {
                  rhs
              } else {
                  Rc::new(Expression::FALSE)
              }
          }
          Or => {
              if *a {
                  Rc::new(Expression::TRUE)
              } else {
                  rhs
              }
          }
          _ => Rc::new(Expression::BinOp {
              bin_op,
              lhs,
              rhs,
              type_: RuntimeType::BoolRuntimeType,
              info: SourcePos::UnknownPosition,
          }),
      },
      (
          bin_op,
          _lhs,
          Lit {
              lit: BoolLit { bool_value: b },
              ..
          },
      ) => match bin_op {
          Implies => {
              if *b {
                  Rc::new(Expression::TRUE)
              } else {
                  negate(lhs).into()
              }
          }
          And => {
              if *b {
                  lhs
              } else {
                  Rc::new(Expression::FALSE)
              }
          }
          Or => {
              if *b {
                  Rc::new(Expression::TRUE)
              } else {
                  lhs
              }
          }
          _ => Rc::new(Expression::BinOp {
              bin_op,
              lhs,
              rhs,
              type_: RuntimeType::BoolRuntimeType,
              info: SourcePos::UnknownPosition,
          }),
      },
      // Integer evaluation
      (
          Divide | Modulo,
          _,
          Lit {
              lit: IntLit { int_value: 0 },
              ..
          },
      ) => panic!("infeasible, division/modulo by zero"),
      (
          bin_op,
          Lit {
              lit: IntLit { int_value: a },
              ..
          },
          Lit {
              lit: IntLit { int_value: b },
              ..
          },
      ) => match bin_op {
          Equal => Expression::bool(*a == *b),
          NotEqual => Expression::bool(*a != *b),
          LessThan => Expression::bool(*a < *b),
          LessThanEqual => Expression::bool(*a <= *b),
          GreaterThan => Expression::bool(*a > *b),
          GreaterThanEqual => Expression::bool(*a >= *b),
          Plus => Expression::int(*a + *b),
          Minus => Expression::int(*a - *b),
          Multiply => Expression::int(*a * *b),
          Divide => Expression::int(*a / *b),
          Modulo => Expression::int(*a % *b),
          _ => panic!("unsupported integer operator"),
      },
      (bin_op, Ref { ref_: a, .. }, Ref { ref_: b, .. }) => match bin_op {
          Equal => Expression::bool(*a == *b),
          NotEqual => Expression::bool(*a != *b),
          _ => panic!("unsupported ref operator"),
      },
      (bin_op, Ref { .. }, Lit { lit: NullLit, .. }) => match bin_op {
          Equal => Rc::new(Expression::FALSE),
          NotEqual => Rc::new(Expression::TRUE),
          _ => panic!("unsupported ref operator"),
      },
      (bin_op, Lit { lit: NullLit, .. }, Ref { .. }) => match bin_op {
          Equal => Rc::new(Expression::FALSE),
          NotEqual => Rc::new(Expression::TRUE),
          _ => panic!("unsupported ref operator"),
      },
      (bin_op, Lit { lit: NullLit, .. }, Lit { lit: NullLit, .. }) => match bin_op {
          Equal => Rc::new(Expression::TRUE),
          NotEqual => Rc::new(Expression::FALSE),
          _ => panic!("unsupported ref operator"),
      },
      (bin_op, SymbolicRef { var: a, .. }, SymbolicRef { var: b, .. }) => {
          if *a == *b {
              match bin_op {
                  Equal => Rc::new(Expression::TRUE),
                  NotEqual => Rc::new(Expression::FALSE),
                  _ => panic!("unsupported ref operator"),
              }
          } else {
              Rc::new(Expression::BinOp {
                  bin_op,
                  lhs,
                  rhs,
                  type_: RuntimeType::BoolRuntimeType,
                  info: SourcePos::UnknownPosition,
              })
          }
      }
      (bin_op, _, _) => Rc::new(Expression::BinOp {
          bin_op,
          lhs,
          rhs,
          type_: RuntimeType::BoolRuntimeType,
          info: SourcePos::UnknownPosition,
      }),
  }
}

fn evaluate_unop(unop: UnOp, expression: Rc<Expression>, stack: &MStack, heap: &MHeap,
) -> Rc<Expression> {
  match (unop, expression.as_ref()) {
      (
          UnOp::Negative,
          Expression::Lit {
              lit: Lit::IntLit { int_value },
              ..
          },
      ) => Rc::new(Expression::Lit {
          lit: Lit::IntLit {
              int_value: -int_value,
          },
          type_: RuntimeType::IntRuntimeType,
          info: SourcePos::UnknownPosition,
      }),
      (
          UnOp::Negative,
          Expression::BinOp {
              bin_op: BinOp::Equal,
              lhs,
              rhs,
              ..
          },
      ) => evaluate_binop(BinOp::NotEqual, lhs.clone(), rhs.clone(), stack, heap).into(),
      (UnOp::Negative, _) => Rc::new(negative(expression)),
      (
          UnOp::Negate,
          Expression::Lit {
              lit: Lit::BoolLit { bool_value },
              ..
          },
      ) => Rc::new(Expression::Lit {
          lit: Lit::BoolLit {
              bool_value: !bool_value,
          },
          type_: RuntimeType::BoolRuntimeType,
          info: SourcePos::UnknownPosition,
      }),
      (UnOp::Negate, _) => Rc::new(negate(expression)),
  }
}

