

use itertools::Either;
use itertools::Itertools;



use itertools::iproduct;
use utils::utils::union;
use utils::utils::union_with;
use crate::dsl::{negate, negative};

use crate::exec::heap::HeapValue;

use crate::exec::State;
use crate::typeable::Typeable;
use crate::z3_checker;
use crate::SourcePos;
use std::collections::HashSet;
use std::collections::HashMap;
use std::hash::Hash;
use std::rc::Rc;
pub mod cfg;
pub mod utils;

use crate::language::*;
use crate::language::syntax::Identifier;

pub(crate) enum Result{ Ok, Err }

type Stack = Vec<HashMap<Identifier, Rc<Expression>>>;
type Heap  = HashMap<i64, Rc<HeapValue>>;


#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Debug)]
pub(crate) enum TyOp{
  IsInstanceOf,
  IsNotInstanceOf
}
//"resolved" expression
//at least it would be resolved, if we didn't have symbols :pensive:
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Debug)]
pub(crate) enum RExpr {
  Lit{ lit: Lit                                          , type_: RuntimeType},
  Sym{ id : Identifier                                   , type_: RuntimeType},
  Ref{ ptr: i64                                          , type_: RuntimeType},
  Bin{ op : BinOp    , left: Rc<RExpr>, right: Rc<RExpr> , type_: RuntimeType},
  Typ{ op : TyOp     , val : Rc<RExpr>, of: RuntimeType  , type_: RuntimeType},
  Uno{ op : UnOp     , val : Rc<RExpr>                   , type_: RuntimeType},
  Con{ con: Rc<RExpr>, left: Rc<RExpr>, right: Rc<RExpr> , type_: RuntimeType},
  
}
impl RExpr {
  fn or(unq_constr_1: HashSet<Rc<RExpr>>, unq_constr_2: HashSet<Rc<RExpr>>) -> HashSet<Rc<RExpr>> {
    iproduct!(unq_constr_1.iter(), unq_constr_2.iter()).map(|(l,r)|{
      evaluate_binop(BinOp::Or, l.clone(), r.clone(), RuntimeType::BoolRuntimeType)
    }).collect()
  }
  fn and(unq_constr_1: HashSet<Rc<RExpr>>, unq_constr_2: HashSet<Rc<RExpr>>) -> HashSet<Rc<RExpr>> {
    iproduct!(unq_constr_1.iter(), unq_constr_2.iter()).map(|(l,r)|{
      evaluate_binop(BinOp::And, l.clone(), r.clone(), RuntimeType::BoolRuntimeType)
    }).collect()
  }
  
  fn mk_true() -> HashSet<Rc<RExpr>> {
    return hashunit(Rc::new(RExpr::Lit { lit: Lit::BoolLit { bool_value: true }, type_: RuntimeType::BoolRuntimeType }));
  }
}

#[derive(PartialEq, Clone)]
pub(crate) enum DynamicPointer {
  Ret(u64, Option<Lhs>),
  Whl(u64, u64),
  Thr(u64, u64),
}

pub(crate) type SValue = HashSet<Rc<RExpr>>;
type SStack = Vec<HashMap<Identifier, SValue>>;
type SHeap  = HashMap<i64, HashSet<HeapValue>>;

pub(crate) struct SetState
{
  pub pointer      : u64,
  pub path_length  : u64,
  pub hed_constr   : SValue,
  pub unq_constr   : SValue,
  pub stack        : SStack,
  pub heap         : SHeap,
  pub dynamic_cont : Vec<DynamicPointer>, 
}

pub(crate) struct SetMergeEngine{
  supply: i64,
}

impl SetMergeEngine{
  pub(crate) fn new() -> Self {
    return SetMergeEngine { supply: 0 }
  }

  fn next_reference_id(&mut self) -> i64 {
    let s = self.supply.clone();
    self.supply = self.supply+1;
    return s;
  }

  pub(crate) fn make_new_state(&self, pc: u64, expr: Rc<Expression>, symbols: Vec<(Identifier, Identifier, RuntimeType)>) -> SetState {
    let mut hashmap = HashMap::new();
    for (k, s, t) in symbols { 
      hashmap.insert(k, hashunit(Rc::new(RExpr::Sym{id:s, type_: t})));
    }

    let mut temp = SetState{
      path_length: 0,
      pointer: pc,
      hed_constr: RExpr::mk_true(),
      unq_constr: RExpr::mk_true(),
      stack: vec![hashmap],
      heap : HashMap::new(),
      dynamic_cont: vec![],
    };

    let constr = self.eval_with(&temp, expr);

    temp.hed_constr = constr;
    return temp;
  }

  pub(crate) fn split_on(&self, state: &SetState, expr: Rc<Expression>) -> (SetState, SetState) {

    let new_top: SValue= iproduct!(state.hed_constr.iter(), state.unq_constr.iter())
      .map(|(l,r)| { evaluate_binop(BinOp::And, l.clone(), r.clone(), RuntimeType::BoolRuntimeType) } )
      .collect();
    let constrs: SValue = self.eval_with(state, expr);
    let negats: SValue = constrs.iter().map(|c|{evaluate_unop(UnOp::Negate, c.clone())}).collect();


    let left = SetState { 
      path_length: state.path_length,
      pointer: state.pointer,
      hed_constr: new_top.clone(),
      unq_constr: constrs, 
      stack: state.stack.clone(), 
      heap: state.heap.clone(), 
      dynamic_cont: state.dynamic_cont.clone()
    };
    let right = SetState { 
      path_length: state.path_length,
      pointer: state.pointer,
      hed_constr: new_top,
      unq_constr: negats, 
      stack: state.stack.clone(), 
      heap: state.heap.clone(), 
      dynamic_cont: state.dynamic_cont.clone() 
    };

    return (left, right);
  }

  pub(crate) fn decl_in(&self, state: &mut SetState, r#type: &NonVoidType, var: &Identifier, _info: &SourcePos) -> Result {
    let val= self.eval_with(state, Rc::new(r#type.default()));
    state.stack.last_mut().map(| frame |{ frame.insert(var.clone(), val) } );
    return Result::Ok;
  }

  pub(crate) fn eval_with_r(&self, state: &SetState, rhs: &Rhs) -> SValue{
    match rhs {
      Rhs::RhsExpression { value, type_, info } => {
        let vals = self.eval_with(state, value.clone());
        return vals;
      },
      Rhs::RhsField { var, field, type_, info } => todo!("field getting"),
      Rhs::RhsElem { var, index, type_, info } => todo!("elem getting"),
      Rhs::RhsArray { array_type, sizes, type_, info } => todo!("array construction"),
      Rhs::RhsCast { cast_type, var, info } => todo!("casting"),
      Rhs::RhsCall { invocation, type_, info } => unreachable!("should be handled by the engine"),
    }

  }
  pub(crate) fn eval_with(&self, state: &SetState, expr: Rc<Expression>) -> SValue{
    match expr.as_ref(){
      Expression::Lit { lit, type_, info } 
        => hashunit(Rc::new(RExpr::Lit { lit: lit.clone(), type_: type_.clone() })),
        Expression::SymbolicVar { var, type_, info } 
        => hashunit(Rc::new(RExpr::Sym { id: var.clone(), type_: type_.clone() })),
      Expression::Ref { ref_, type_, info } 
        => hashunit(Rc::new(RExpr::Ref { ptr: ref_.clone(), type_: type_.clone() })),

      Expression::Var { var, type_, info } => {
        state.stack.last().unwrap().get(var).unwrap().clone()
      },
      
      Expression::Conditional { guard, true_, false_, type_, info } => {
        let gs = self.eval_with(state, guard.clone());
        let ls = self.eval_with(state, true_.clone());
        let rs = self.eval_with(state, false_.clone());
        iproduct!(gs.iter(), ls.iter(), rs.iter()).map(|(g,l,r)|{
          evaluate_guard(g.clone(),l.clone(),r.clone(), type_.clone())
        }).collect()

      },
      Expression::BinOp { bin_op, lhs, rhs, type_, info } => {
        let ls = self.eval_with(state, lhs.clone());
        let rs = self.eval_with(state, rhs.clone());
        iproduct!(ls.iter(), rs.iter()).map(|(l, r)|{
          evaluate_binop(bin_op.clone(), l.clone(), r.clone(), type_.clone())
        }).collect()
      },

      Expression::TypeExpr { texpr } => {
        match texpr {
            TypeExpr::InstanceOf { var, rhs, info } => {
              let vals = state.stack.last().unwrap().get(var).unwrap().clone();
              vals.iter().map(|val|{(evaluate_tyop(TyOp::IsInstanceOf, val.clone(), rhs.clone()))}).collect()
            },
            TypeExpr::NotInstanceOf { var, rhs, info } => {
              let vals = state.stack.last().unwrap().get(var).unwrap().clone();
              vals.iter().map(|val|{(evaluate_tyop(TyOp::IsNotInstanceOf, val.clone(), rhs.clone()))}).collect()
            },
        }        

      },

      Expression::UnOp { un_op, value, type_, info } => {
        let vals = self.eval_with(state, value.clone());
        vals.iter().map(|val|{ evaluate_unop(un_op.clone(), val.clone())}).collect()
      },

      //shoul de doable
      Expression::SizeOf { var, type_, info } => todo!(),

      //won't be done for a while
      Expression::SymbolicRef { var, type_, info } => todo!(),
      Expression::Forall { elem, range, domain, formula, type_, info } => todo!(),
      Expression::Exists { elem, range, domain, formula, type_, info } => todo!(),

    }
  }

  pub(crate) fn assign_expr(&self, state: &mut SetState, lhs: &Lhs, rhs: &Rhs) -> bool{
    match rhs {
      Rhs::RhsExpression { value, type_, info } => {
        let vals = self.eval_with(state, value.clone());
        self.assign_evaled(state, lhs, vals);
        return true;
      },
      Rhs::RhsField { var, field, type_, info } => todo!("field getting"),
      Rhs::RhsElem { var, index, type_, info } => todo!("elem getting"),
      Rhs::RhsArray { array_type, sizes, type_, info } => todo!("array construction"),
      Rhs::RhsCast { cast_type, var, info } => todo!("casting"),
      Rhs::RhsCall { invocation, type_, info } => unreachable!("should be handled by the engine"),
    }
  }
  pub(crate) fn assign_evaled(&self, state: &mut SetState, lhs: &Lhs, value: SValue){
    match lhs{
      Lhs::LhsVar { var, type_, info } => {
        let stack = state.stack.last_mut().unwrap();
        stack.insert(var.clone(), value);

      },
      Lhs::LhsElem { var, index, type_, info } => todo!("elem setting"),
      Lhs::LhsField { var, var_type, field, type_, info } => todo!("field setting"),
    }
  }

  pub(crate) fn is_feasible(&self, state: &SetState) -> bool {
    return true;
  }
  pub(crate) fn is_valid_for(&self, state: &SetState, expr: Rc<Expression>) -> bool {
    return true;
  }

  pub(crate) fn add_assumption_to(&self, state: &mut SetState, assumption: Either<Rc<Expression>, TypeExpr>) {
    let expr = assumption.either(
    | s|{ s }, 
    | t|{ Rc::new(Expression::TypeExpr { texpr: t })});
    let cond = self.eval_with(state, expr);
    state.unq_constr = RExpr::and(state.unq_constr.clone(), cond);
  }
}

impl  SetState {

  pub(crate) fn path_length(&self) -> u64 {
    return self.path_length.clone();
  }

  pub(crate) fn incr_path(&mut self) -> u64 {
    self.path_length = self.path_length + 1; 
    return self.path_length.clone();
  }

  pub(crate) fn get_pointer(&self) -> u64 {
    return self.pointer.clone();
  }

  pub(crate) fn set_pointer(&mut self, ptr: u64) -> u64 {
    self.pointer = ptr;
    return self.pointer.clone();
  }

  pub(crate) fn pop_stack(&mut self) -> () {
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

  pub(crate) fn push_stack(&mut self) -> () {
    self.stack.push(HashMap::new());
  }

  pub(crate) fn get_dynamic_cf_size(&self) -> usize {
    return self.dynamic_cont.len();
  }

  pub(crate) fn pop_dynamic_cf(&mut self) -> Option<DynamicPointer> {
    return self.dynamic_cont.pop();
  }

  pub(crate) fn push_dynamic_cf(&mut self, dn : DynamicPointer) -> () {
    self.dynamic_cont.push(dn);
  }

  pub(crate) fn merge_full(&mut self, left : Self, right: Self) -> () {
    assert_eq!(self.stack.len(), left.stack.len());
    assert_eq!(self.stack.len(), right.stack.len());
    assert_eq!(left.pointer, right.pointer);

    self.pointer = left.pointer;
    self.path_length = std::cmp::min(left.path_length, right.path_length);
  
    self.unq_constr = RExpr::and(
      self.unq_constr.clone(),
      RExpr::or(left.unq_constr, right.unq_constr)
    );
  
    let paired  =  left.stack.into_iter().zip(right.stack);

    self.heap = union_with(left.heap, right.heap,
       |v, w|{ union(v, w )});
    self.stack = paired.map(|(frame_1, frame_2)|{
      union_with(frame_1, frame_2, |v, w|{ union(v, w )})
    }).collect();
  }

  pub(crate) fn merge_part(&mut self, left : Self) -> () {
    assert_eq!(self.stack.len(), left.stack.len());

    self.pointer     = left.pointer;
    self.path_length = left.path_length;
  
    self.unq_constr = RExpr::and(
      self.unq_constr.clone(),
      left.unq_constr
    );


    self.heap = left.heap;
    self.stack = left.stack;
    return;  
  }
  
}

fn hashunit<T>(t: T) -> HashSet<T> where T: Eq, T: Hash{
  let mut h = HashSet::new();
  h.insert(t);
  return h;
}

fn evaluate_guard(guard: Rc<RExpr>, lhs: Rc<RExpr>, rhs: Rc<RExpr>, type_: RuntimeType) -> Rc<RExpr> {
  use crate::syntax::Lit::*;
  use RExpr::*;

  match guard.as_ref(){
    Lit { lit: BoolLit{bool_value: true}, type_ }  => lhs,
    Lit { lit: BoolLit{bool_value: false}, type_ } => rhs,
    _ => Rc::new(RExpr::Con { con: guard, left: lhs, right: rhs, type_ })
  }
}

fn evaluate_binop(bin_op: BinOp, lhs: Rc<RExpr>, rhs: Rc<RExpr>, type_: RuntimeType) -> Rc<RExpr> {
  use crate::syntax::BinOp::*;
  use crate::syntax::RuntimeType::*;
  use crate::syntax::Lit::*;
  use RExpr::*;

  match (bin_op, lhs.as_ref(), rhs.as_ref()){
    (Implies         , Lit { lit: BoolLit{bool_value: false}, .. }, _) 
      => Rc::new(Lit { lit: BoolLit{bool_value: true}, type_: BoolRuntimeType}),
    (Implies         , Lit { lit: BoolLit{bool_value: true}, .. }, _) 
      => rhs,
    (Implies         , _, Lit { lit: BoolLit{bool_value: true}, ..}) 
      => rhs,
    (Implies         , _, Lit { lit: BoolLit{bool_value: false}, ..}) 
      => Rc::new(Uno { op: UnOp::Negate, val: lhs, type_: BoolRuntimeType }),
    (Implies         , _, _) 
      => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_: BoolRuntimeType }),

    (And             , Lit { lit: BoolLit{bool_value: false}, ..}, _) 
      => lhs,
    (And             , Lit { lit: BoolLit{bool_value: true}, ..}, _) 
      => rhs,
    (And             , _, Lit { lit: BoolLit{bool_value: false}, ..}) 
      => rhs,
    (And             , _, Lit { lit: BoolLit{bool_value: true}, ..}) 
      => lhs,
    (And             , _, _) 
      => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_: BoolRuntimeType }),
    
    (Or             , Lit { lit: BoolLit{bool_value: false}, ..}, _) 
      => rhs,
    (Or             , Lit { lit: BoolLit{bool_value: true}, ..}, _) 
      => lhs,
    (Or             , _, Lit { lit: BoolLit{bool_value: false}, ..}) 
      => lhs,
    (Or             , _, Lit { lit: BoolLit{bool_value: true}, ..}) 
      => rhs,
    (Or             , _, _) 
      => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_: BoolRuntimeType }),
    
    // rest to be done at some other time :releved:
    (Equal           , _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_: BoolRuntimeType }),
    (NotEqual        , _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_: BoolRuntimeType }),
    (LessThan        , _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_: BoolRuntimeType }),
    (LessThanEqual   , _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_: BoolRuntimeType }),
    (GreaterThan     , _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_: BoolRuntimeType }),
    (GreaterThanEqual, _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_: BoolRuntimeType }),
    (Plus            , _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_ }),
    (Minus           , _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_ }),
    (Multiply        , _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_ }),
    (Divide          , _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_ }),
    (Modulo          , _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_ }),
  }
}

fn evaluate_tyop(ty_op: TyOp, value: Rc<RExpr>, of_this_type: RuntimeType, ) -> Rc<RExpr> {
  use TyOp::*;
  use crate::syntax::Lit::*;
  use RExpr::*;

  todo!();
}

fn evaluate_unop(unop: UnOp, expression: Rc<RExpr>) -> Rc<RExpr> {
  use crate::syntax::UnOp::*;
  use crate::syntax::Lit::*;
  use RExpr::*;

  match (unop, expression.as_ref()){

    (Negative, Lit { lit: IntLit{int_value}, type_ }) 
      => Rc::new(Lit{lit: IntLit{int_value: -int_value.clone()}, type_: type_.clone()}),
    (Negative, Lit { lit: FloatLit{float_value}, type_ }) 
      => Rc::new(Lit{lit: FloatLit{float_value: -float_value.clone()}, type_: type_.clone()}),
    //todo: negative of expressions
    //but maybe that one is less of a big deal?

    (Negate, Lit { lit: BoolLit{bool_value}, type_ }) 
      => Rc::new(Lit { lit: BoolLit{bool_value: !bool_value.clone()}, type_: type_.clone()}),
    (Negate, Typ { op, val, of, type_ }) 
      => Rc::new(Typ{op: flip_t(op.clone()), val: val.clone(), of: of.clone(), type_: type_.clone()}),
    (Negate, Uno { op, val, type_ }) => val.clone(),

    (_, Con { con, left, right, type_ }) 
      => Rc::new(Con { 
        con  : con.clone(), 
        left : evaluate_unop(unop, left.clone()), 
        right: evaluate_unop(unop, right.clone()),
        type_: type_.clone()}),

    (Negate, Bin { op: BinOp::Equal, left, right, type_ }) 
      => Rc::new(Bin{op: BinOp::NotEqual, left: left.clone(), right: right.clone(), type_: type_.clone()}),
    (Negate, Bin { op: BinOp::NotEqual, left, right, type_ }) 
      => Rc::new(Bin{op: BinOp::Equal, left: left.clone(), right: right.clone(), type_: type_.clone()}),
    (Negate, Bin { op: BinOp::LessThan, left, right, type_ }) 
      => Rc::new(Bin{op: BinOp::GreaterThanEqual, left: left.clone(), right: right.clone(), type_: type_.clone()}),
    (Negate, Bin { op: BinOp::LessThanEqual, left, right, type_ }) 
      => Rc::new(Bin{op: BinOp::GreaterThan, left: left.clone(), right: right.clone(), type_: type_.clone()}),
    (Negate, Bin { op: BinOp::GreaterThan, left, right, type_ }) 
      => Rc::new(Bin{op: BinOp::LessThanEqual, left: left.clone(), right: right.clone(), type_: type_.clone()}),
    (Negate, Bin { op: BinOp::GreaterThanEqual, left, right, type_ }) 
      => Rc::new(Bin{op: BinOp::LessThan, left: left.clone(), right: right.clone(), type_: type_.clone()}),  
    _ => expression
  }
}


fn flip_t(ty_op: TyOp) -> TyOp {
  match ty_op{
    TyOp::IsInstanceOf => TyOp::IsNotInstanceOf,
    TyOp::IsNotInstanceOf => TyOp::IsInstanceOf,
  }
}

