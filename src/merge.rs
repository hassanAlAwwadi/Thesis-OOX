

use itertools::Either;


use itertools::iproduct;
use ordered_float::NotNan;
use utils::utils::{union, union_with, hash_unit};


use crate::typeable::Typeable;

use crate::SourcePos;
use std::collections::BTreeMap;
use std::collections::HashSet;
use std::collections::HashMap;

use std::hash::Hash;
use std::panic;

use std::rc::Rc;
pub mod cfg;
pub mod utils;

use crate::language::*;
use crate::language::syntax::Identifier;
use z3::{Config, Context, Solver, ast::Bool, ast::Int, ast::Ast};

pub(crate) enum Result{ Ok, Err }

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Debug)]
pub(crate) enum TyOp{
  IsInstanceOf,
  IsNotInstanceOf
}
// "resolved" expression
// at least it would be resolved, if we didn't have symbols :pensive:
// or quantifiers, which are unhandled for now
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Debug)]
pub(crate) enum RExpr<T> {
  Lit{ lit: Lit                                                  , type_: RuntimeType},
  Sym{ id : Identifier                                           , type_: RuntimeType},
  Ref{ ptr: i64                                                  , type_: RuntimeType},
  Bin{ op : BinOp       , left: Rc<RExpr<T>>, right: Rc<RExpr<T>>, type_: RuntimeType},
  Typ{ op : TyOp        , val : Rc<RExpr<T>>, of: RuntimeType    , type_: RuntimeType},
  Uno{ op : UnOp        , val : Rc<RExpr<T>>                     , type_: RuntimeType},
  Con{ con: Rc<RExpr<T>>, left: Rc<RExpr<T>>, right: Rc<RExpr<T>>, type_: RuntimeType},
  Pur{ pur: T, type_: RuntimeType }
}
impl<T> RExpr<T> where T: Clone {
  fn get_type(&self) -> RuntimeType {
    match self{
        RExpr::Lit { type_, .. } => type_.clone(),
        RExpr::Sym { type_, .. } => type_.clone(),
        RExpr::Ref { type_, .. } => type_.clone(),
        RExpr::Bin { type_, .. } => type_.clone(),
        RExpr::Typ { type_, .. } => type_.clone(),
        RExpr::Uno { type_, .. } => type_.clone(),
        RExpr::Con { type_, ..} => type_.clone(),
        RExpr::Pur { type_, ..} => type_.clone(),
    }
  }
  
  fn and(left: Rc<Self>, right: Rc<Self>) -> Self {
    return RExpr::Bin{
      op: BinOp::And,
      left: left,
      right: right,
      type_: RuntimeType::BoolRuntimeType
    }
  }

  fn or(left: Rc<Self>, right: Rc<Self>) -> Self {
    return RExpr::Bin{
      op: BinOp::Or,
      left: left,
      right: right,
      type_: RuntimeType::BoolRuntimeType
    }
  }

  fn evaluate_guard(guard: Rc<Self>, lhs: Rc<Self>, rhs: Rc<Self>, type_: RuntimeType) -> Rc<Self> {
    use crate::syntax::Lit::*;
    use RExpr::*;

    match guard.as_ref(){
      Lit { lit: BoolLit{bool_value: true}, type_: _ }  => lhs,
      Lit { lit: BoolLit{bool_value: false}, type_: _ } => rhs,
      _ => Rc::new(RExpr::Con { con: guard, left: lhs, right: rhs, type_ })
    }
  }
  
  fn evaluate_binop(bin_op: BinOp, lhs: Rc<Self>, rhs: Rc<Self>, type_: RuntimeType) -> Rc<Self> {
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
      
      (NotEqual        , Lit { lit: IntLit { int_value: l }, .. }, Lit { lit: IntLit { int_value: r }, .. }) => Rc::new(Lit { lit: BoolLit { bool_value: l != r }, type_: BoolRuntimeType }),
      (LessThan        , Lit { lit: IntLit { int_value: l }, .. }, Lit { lit: IntLit { int_value: r }, .. }) => Rc::new(Lit { lit: BoolLit { bool_value: l < r }, type_: BoolRuntimeType }),
      (LessThanEqual   , Lit { lit: IntLit { int_value: l }, .. }, Lit { lit: IntLit { int_value: r }, .. }) => Rc::new(Lit { lit: BoolLit { bool_value: l <= r }, type_: BoolRuntimeType }),
      (GreaterThan     , Lit { lit: IntLit { int_value: l }, .. }, Lit { lit: IntLit { int_value: r }, .. }) => Rc::new(Lit { lit: BoolLit { bool_value: l > r }, type_: BoolRuntimeType }),
      (GreaterThanEqual, Lit { lit: IntLit { int_value: l }, .. }, Lit { lit: IntLit { int_value: r }, .. }) => Rc::new(Lit { lit: BoolLit { bool_value: l >= r }, type_: BoolRuntimeType }),
      
      (Equal, Sym{ id: l, .. }, Sym { id: r, .. }) => {
        if l == r {
          Rc::new(Lit { lit: BoolLit { bool_value: true }, type_: BoolRuntimeType })
        } else {
          //could still theoretically be equal
          //but we don't know that
          Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_: BoolRuntimeType })
        }
      },
      (NotEqual, Sym{ id: l, .. }, Sym { id: r, .. }) => {
        if l == r {
          Rc::new(Lit { lit: BoolLit { bool_value: false }, type_: BoolRuntimeType })
        } else {
          //could still theoretically be equal
          //but we don't know that
          Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_: BoolRuntimeType })
        }
      },
      (LessThan, Sym { id: l, .. }, Sym { id: r, .. }) => {
        if l == r {
          Rc::new(Lit { lit: BoolLit { bool_value: false }, type_: BoolRuntimeType })
        } else {
          Rc::new(RExpr::Bin { op: bin_op, left: lhs, right: rhs, type_: BoolRuntimeType })
        }
      },
      (LessThanEqual, Sym { id: l, .. }, Sym { id: r, .. }) => {
        if l == r {
          Rc::new(Lit { lit: BoolLit { bool_value: true }, type_: BoolRuntimeType })
        } else {
          Rc::new(RExpr::Bin { op: bin_op, left: lhs, right: rhs, type_: BoolRuntimeType })
        }
      },
      (GreaterThan, Sym { id: l, .. }, Sym { id: r, .. }) => {
        if l == r {
          Rc::new(Lit { lit: BoolLit { bool_value: false }, type_: BoolRuntimeType })
        } else {
          Rc::new(RExpr::Bin { op: bin_op, left: lhs, right: rhs, type_: BoolRuntimeType })
        }
      },
      (GreaterThanEqual, Sym { id: l, .. }, Sym { id: r, .. }) => {
        if l == r {
          Rc::new(Lit { lit: BoolLit { bool_value: true }, type_: BoolRuntimeType })
        } else {
          Rc::new(RExpr::Bin { op: bin_op, left: lhs, right: rhs, type_: BoolRuntimeType })
        }
      },


      (Plus, Lit { lit: IntLit { int_value: l }, .. }, Lit { lit: IntLit { int_value: r }, .. }) 
        => Rc::new(Lit { lit: IntLit { int_value: l + r }, type_: type_.clone() }),
      (Minus, Lit { lit: IntLit { int_value: l }, .. }, Lit { lit: IntLit { int_value: r }, .. }) 
        => Rc::new(Lit { lit: IntLit { int_value: l - r }, type_: type_.clone() }),  
      (Multiply, Lit { lit: IntLit { int_value: l }, .. }, Lit { lit: IntLit { int_value: r }, .. }) 
        => Rc::new(Lit { lit: IntLit { int_value: l * r }, type_: type_.clone() }),
      (Divide, Lit { lit: IntLit { int_value: l }, .. }, Lit { lit: IntLit { int_value: r }, .. }) => {
        if *r != 0 {
          Rc::new(Lit { lit: IntLit { int_value: l / r }, type_: type_.clone() })
        } else {
          panic!("Division by zero")
        }
      },
      (Modulo, Lit { lit: IntLit { int_value: l }, .. }, Lit { lit: IntLit { int_value: r }, .. }) => {
        if *r != 0 {
          Rc::new(Lit { lit: IntLit { int_value: l % r }, type_: type_.clone() })
        } else {
          panic!("Modulo by zero")
        }
      },
      (Plus, Lit { lit: IntLit { int_value: 0 }, .. }, _) => rhs,
      (Plus, _, Lit { lit: IntLit { int_value: 0 }, .. }) => lhs,
      (Minus, _, Lit { lit: IntLit { int_value: 0 }, .. }) => lhs,
      (Multiply, Lit { lit: IntLit { int_value: 1 }, .. }, _) => rhs,
      (Multiply, _, Lit { lit: IntLit { int_value: 1 }, .. }) => lhs,
      (Multiply, Lit { lit: IntLit { int_value: 0 }, .. }, _) => lhs,
      (Multiply, _, Lit { lit: IntLit { int_value: 0 }, .. }) => rhs,
      (Divide, _, Lit { lit: IntLit { int_value: 1 }, .. }) => lhs,
      (Modulo, _, Lit { lit: IntLit { int_value: 1 }, .. }) => Rc::new(Lit { lit: IntLit { int_value: 0 }, type_: type_.clone() }),
      
      (Minus, 
        Bin { op: Minus, left: symbol, right: lit1, type_ }, 
        Lit { lit: lit2, .. }) => {
        if let (RExpr::Sym { .. }, RExpr::Lit { lit: IntLit { int_value: x, .. }, ..}) = (symbol.as_ref(), lit1.as_ref()) {
          if let IntLit { int_value: y, .. } = lit2 {
            let combined_lit = Rc::new(Lit { lit: IntLit { int_value: x + y }, type_: type_.clone() });
            return Rc::new(Bin { op: Minus, left: symbol.clone(), right: combined_lit, type_: type_.clone() });
          }
        }
        Rc::new(Bin { op: bin_op, left: lhs.clone(), right: rhs.clone(), type_: type_.clone() })
      }
      (Plus, 
        Bin { op: Plus, left, right, type_ }, 
        Lit { lit, .. }) => {
        if let IntLit { int_value: y, .. } = lit {  
          if let (RExpr::Sym { .. }, RExpr::Lit { lit: IntLit { int_value: x }, ..}) = (left.as_ref(), right.as_ref()) {
            
              let combined_lit = Rc::new(Lit { lit: IntLit { int_value: x + y }, type_: type_.clone() });
              return Rc::new(Bin { op: Plus, left: left.clone(), right: combined_lit, type_: type_.clone() });
            }
          else if let (RExpr::Lit { lit: IntLit { int_value: x }, ..}, RExpr::Sym { .. }) = (left.as_ref(), right.as_ref()) {
            let combined_lit = Rc::new(Lit { lit: IntLit { int_value: x + y }, type_: type_.clone() });
            return Rc::new(Bin { op: Plus, left: right.clone(), right: combined_lit, type_: type_.clone() });
          } 
        }

        Rc::new(Bin { op: bin_op, left: lhs.clone(), right: rhs.clone(), type_: type_.clone() })
      },
      // rest to be done at some other time :releved:
      (Equal           , _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_: BoolRuntimeType }),
      (NotEqual           , _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_: BoolRuntimeType }),
      (LessThan        , _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_ }),
      (LessThanEqual   , _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_ }),
      (GreaterThan     , _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_ }),
      (GreaterThanEqual, _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_ }),

      (Plus, _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_ }),
      (Minus, _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_ }),
      (Multiply, _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_ }),
      (Divide, _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_ }),
      (Modulo, _, _) => Rc::new(RExpr::Bin{ op: bin_op, left: lhs, right: rhs, type_ }),
    }
  }
  fn evaluate_tyop(_ty_op: TyOp, _value: Rc<Self>, _of_this_type: RuntimeType, ) -> Rc<Self> {
    
    
    

    todo!();
  }
  
  fn evaluate_unop(unop: UnOp, expression: Rc<Self>) -> Rc<Self> {
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
        => Rc::new(Typ{op: Self::flip_t(op), val: val.clone(), of: of.clone(), type_: type_.clone()}),

    
      (Negate, Bin { op, left, right, type_ }) 
        => {
          if let Some(binop) = Self::try_invert_bool_binop(op){
            Rc::new(Bin{op: binop, left: left.clone(), right: right.clone(), type_: type_.clone()})
          }
          else {
            Rc::new(Uno { op: Negate, val: expression.clone(), type_: type_.clone()})
          }
        },
      (_, Con { con, left, right, type_ }) 
        => Rc::new(Con { 
          con  : con.clone(), 
          left : Self::evaluate_unop(unop, left.clone()), 
          right: Self::evaluate_unop(unop, right.clone()),
          type_: type_.clone()}),
      (_, Uno { val, .. }) => val.clone(),
      (Negate, _) => Rc::new(Uno { op: Negate, val: expression.clone(), type_: RuntimeType::BoolRuntimeType}),
      (Negative, _) => Rc::new(Uno { op: Negate, val: expression.clone(), type_: expression.get_type()}),
    }
  }

  fn flip_t(ty_op: &TyOp) -> TyOp {
    match ty_op{
      TyOp::IsInstanceOf => TyOp::IsNotInstanceOf,
      TyOp::IsNotInstanceOf => TyOp::IsInstanceOf,
    }
  }

  fn try_invert_bool_binop(bin_op: &BinOp) -> Option<BinOp>{
    use crate::syntax::BinOp::*;
    match bin_op{
      Equal => Some(NotEqual),
      NotEqual => Some(Equal),
      LessThan => Some(GreaterThanEqual),
      LessThanEqual => Some(GreaterThan),
      GreaterThan => Some(LessThanEqual),
      GreaterThanEqual => Some(LessThan),
      _ => None,
    }
  }

  fn expr_to_bool<'a>(expr: Rc<Self>, context: &'a Context, 
    bmemory: &mut HashMap<Identifier, Bool<'a>>,
    imemory: &mut HashMap<Identifier, Int<'a>>) -> Bool<'a> {
      match expr.as_ref(){
          RExpr::Lit { lit, type_: _ } => {
            match lit{
              Lit::BoolLit { bool_value } => Bool::from_bool(context, *bool_value),
              _ => panic!("Expected a boolean literal, but got {:?}", lit),
            }
          },
          RExpr::Sym { id, type_ } => {
            if let Some(ast) = bmemory.get(id){
              return ast.clone();
            }
            else{
              let ast = match type_{
                RuntimeType::BoolRuntimeType => Bool::new_const(&context, id.as_str()),
                _ => panic!("Expected a boolean type, but got {:?}", type_),
              };
              bmemory.insert(id.clone(), ast.clone());
              return ast; 
            }
          },
          RExpr::Ref { ptr: _, type_: _ } => unreachable!("this one really should not be here"),
          RExpr::Bin { op, left, right, type_: _ } => {
            match op{
                BinOp::Implies => {
                    let left = Self::expr_to_bool(left.clone(), context, bmemory, imemory);
                    let right = Self::expr_to_bool(right.clone(), context, bmemory, imemory);
                    return Bool::implies(&left, &right);
                },
                BinOp::And => {
                    let left = Self::expr_to_bool(left.clone(), context, bmemory, imemory);
                    let right = Self::expr_to_bool(right.clone(), context, bmemory, imemory);
                    return Bool::and(context, &[&left, &right]);
                },
                BinOp::Or => {
                    let left = Self::expr_to_bool(left.clone(), context, bmemory, imemory);
                    let right = Self::expr_to_bool(right.clone(), context, bmemory, imemory);
                    return Bool::or(context, &[&left, &right]);
                },
                BinOp::Equal => {
                  let ltype = left.get_type();
                  let rtype = right.get_type();
                  assert!(ltype == rtype, "Expected the same type for both sides of the equality, but got {:?} and {:?}", ltype, rtype);
                  match ltype{
                    RuntimeType::BoolRuntimeType => {
                      let left = Self::expr_to_bool(left.clone(), context, bmemory, imemory);
                      let right = Self::expr_to_bool(right.clone(), context, bmemory, imemory);
                      return left._eq(&right);
                    },
                    RuntimeType::IntRuntimeType => {
                      let left = Self::expr_to_int(left.clone(), context, bmemory, imemory);
                      let right = Self::expr_to_int(right.clone(), context, bmemory, imemory);
                      return left._eq(&right);
                    },
                    _ => panic!("Expected a boolean or integer type for equality, but got {:?}", ltype),
                  }
                },
                BinOp::NotEqual => {
                  let ltype = left.get_type();
                  let rtype = right.get_type();
                  assert!(ltype == rtype, "Expected the same type for both sides of the equality, but got {:?} and {:?}", ltype, rtype);
                  match ltype{
                    RuntimeType::BoolRuntimeType => {
                      let left = Self::expr_to_bool(left.clone(), context, bmemory, imemory);
                      let right = Self::expr_to_bool(right.clone(), context, bmemory, imemory);
                      return left._eq(&right).not();
                    },
                    RuntimeType::IntRuntimeType => {
                      let left = Self::expr_to_int(left.clone(), context, bmemory, imemory);
                      let right = Self::expr_to_int(right.clone(), context, bmemory, imemory);
                      return left._eq(&right).not();
                    },
                    _ => panic!("Expected a boolean or integer type for equality, but got {:?}", ltype),
                  }
                },
                BinOp::LessThan =>{
                  let ltype = left.get_type();
                  let rtype = right.get_type();
                  assert!(ltype == rtype, "Expected the same type for both sides of the equality, but got {:?} and {:?}", ltype, rtype);
                  match ltype{
                    RuntimeType::IntRuntimeType => {
                      let left : Int<'_> = Self::expr_to_int(left.clone(), context, bmemory, imemory);
                      let right: Int<'_> = Self::expr_to_int(right.clone(), context, bmemory, imemory);
                      return left.lt(&right);
                    },
                    _ => panic!("Expected a integer type for lt, but got {:?}", ltype),
                  }
                },
                BinOp::LessThanEqual => {
                  let ltype = left.get_type();
                  let rtype = right.get_type();
                  assert!(ltype == rtype, "Expected the same type for both sides of the equality, but got {:?} and {:?}", ltype, rtype);
                  match ltype{
                    RuntimeType::IntRuntimeType => {
                      let left : Int<'_> = Self::expr_to_int(left.clone(), context, bmemory, imemory);
                      let right: Int<'_> = Self::expr_to_int(right.clone(), context, bmemory, imemory);
                      return left.le(&right);
                    },
                    _ => panic!("Expected a integer type for lt, but got {:?}", ltype),
                  }
                },
                BinOp::GreaterThan => {
                  let ltype = left.get_type();
                  let rtype = right.get_type();
                  assert!(ltype == rtype, "Expected the same type for both sides of the equality, but got {:?} and {:?}", ltype, rtype);
                  match ltype{
                    RuntimeType::IntRuntimeType => {
                      let left : Int<'_> = Self::expr_to_int(left.clone(), context, bmemory, imemory);
                      let right: Int<'_> = Self::expr_to_int(right.clone(), context, bmemory, imemory);
                      return left.gt(&right);
                    },
                    _ => panic!("Expected a integer type for lt, but got {:?}", ltype),
                  }
                },
                BinOp::GreaterThanEqual => {
                  let ltype = left.get_type();
                  let rtype = right.get_type();
                  assert!(ltype == rtype, "Expected the same type for both sides of the equality, but got {:?} and {:?}", ltype, rtype);
                  match ltype{
                    RuntimeType::IntRuntimeType => {
                      let left : Int<'_> = Self::expr_to_int(left.clone(), context, bmemory, imemory);
                      let right: Int<'_> = Self::expr_to_int(right.clone(), context, bmemory, imemory);
                      return left.ge(&right);
                    },
                    _ => panic!("Expected a integer type for lt, but got {:?}", ltype),
                  }
                },
                _ => panic!("Expected a boolean binop, but got {:?}", op),
            }
          },
          RExpr::Typ { op, val, of, type_: _ } => {
            let _type = val.get_type();
            match op{
              TyOp::IsInstanceOf => {
                return Bool::from_bool(context, _type == *of);
              },
              TyOp::IsNotInstanceOf => {
                return Bool::from_bool(context, _type != *of);
              },
            }
          },
          RExpr::Uno { op, val, type_: _ } => {
            match op{
              UnOp::Negate => {
                let val = Self::expr_to_bool(val.clone(), context, bmemory, imemory);
                return val.not();
              },
              UnOp::Negative => panic!("expected a negate, but got a negative of number"),
            }
          },
          RExpr::Con { con, left, right, type_: _ } => {
            let cond  = Self::expr_to_bool(con.clone(), context, bmemory, imemory);
            let left  = Self::expr_to_bool(left.clone(), context, bmemory, imemory);
            let right = Self::expr_to_bool(right.clone(), context, bmemory, imemory);
            return cond.ite(&left, &right);
          },
          RExpr::Pur { pur: _, type_: _ } => panic!("resolve pure before calling"),
      }
    }
    
  fn expr_to_int<'a>(clone: Rc<RExpr<T>>, context: &'a Context, 
    bmemory: &mut HashMap<Identifier, Bool<'a>>, 
    imemory: &mut HashMap<Identifier, Int<'a>>) -> Int<'a> {
      match clone.as_ref(){
        RExpr::Lit { lit, type_: _ } => {
          match lit{
            Lit::IntLit { int_value } => Int::from_i64(context, *int_value),
            _ => panic!("Expected an integer literal, but got {:?}", lit),
          }
        },
        RExpr::Sym { id, type_ } => {
          if let Some(ast) = imemory.get(id){
            return ast.clone();
          }
          else{
            let ast = match type_{
              RuntimeType::IntRuntimeType => Int::new_const(&context, id.as_str()),
              _ => panic!("Expected a integer  type, but got {:?}", type_),
            };
            imemory.insert(id.clone(), ast.clone());
            return ast; 
          }
        },
        RExpr::Ref { ptr: _, type_: _ } => unreachable!("this one really should not be here"),
        RExpr::Bin { op, left, right, type_: _ } => {
          match op{
              BinOp::Plus => {
                  let left = Self::expr_to_int(left.clone(), context, bmemory, imemory);
                  let right = Self::expr_to_int(right.clone(), context, bmemory, imemory);
                  return left + right;
              },
              BinOp::Minus => {
                  let left = Self::expr_to_int(left.clone(), context, bmemory, imemory);
                  let right = Self::expr_to_int(right.clone(), context, bmemory, imemory);
                  return left - right;
              },
              BinOp::Multiply => {
                  let left = Self::expr_to_int(left.clone(), context, bmemory, imemory);
                  let right = Self::expr_to_int(right.clone(), context, bmemory, imemory);
                  return left * right;
              },
              BinOp::Divide => {
                  let left = Self::expr_to_int(left.clone(), context, bmemory, imemory);
                  let right = Self::expr_to_int(right.clone(), context, bmemory, imemory);
                  return left / right;
              },
              BinOp::Modulo => {
                  let left = Self::expr_to_int(left.clone(), context, bmemory, imemory);
                  let right = Self::expr_to_int(right.clone(), context, bmemory, imemory);
                  return left.modulo(&right);
              }
              _ => panic!("Expected a integer binop, but got {:?}", op),
            }
          }
        RExpr::Typ { op: _, val: _, of: _, type_: _ } => panic!("this one should not be here"),
        RExpr::Uno { op, val, type_: _ } => {
          match op{
            UnOp::Negate => panic!("expected a negative, but got a negate of bool"),
            UnOp::Negative => {
              let val = Self::expr_to_int(val.clone(), context, bmemory, imemory);
              return Int::from_i64(context, 0) - val;
            },
          }
        },
        RExpr::Con { con, left, right, type_: _ } => {
          let cond  = Self::expr_to_bool(con.clone(), context, bmemory, imemory);
          let left  = Self::expr_to_int(left.clone(), context, bmemory, imemory);
          let right = Self::expr_to_int(right.clone(), context, bmemory, imemory);
          return cond.ite(&left, &right);
        },
        RExpr::Pur { pur: _, type_: _ } => panic!("resolve pure before calling"),
      }
    }

  fn as_string(self: Rc<Self>, f: impl Clone + Fn(T) -> String) -> String{
    match self.as_ref(){
      RExpr::Lit { lit, type_: _ } => {
        match lit{
            Lit::IntLit { int_value } => format!("{}", int_value),
            Lit::FloatLit { float_value } => format!("{}", float_value),
            Lit::BoolLit { bool_value } => format!("{}", bool_value),
            Lit::StringLit { string_value } => format!("\"{}\"", string_value),
            Lit::NullLit {} => format!("null"),
            Lit::CharLit { char_value } => format!("'{}'", char_value),
            Lit::UIntLit { uint_value } => format!("{}", uint_value),
        }
      },
      RExpr::Sym { id, type_: _ } => {
        format!("${}", id)
      },
      RExpr::Ref { ptr, type_: _ } => {
        format!("${}", ptr)
      },
      RExpr::Bin { op, left, right, type_: _ } => {
        
        match op{
            BinOp::Implies => format!("({} => {})", left.clone().as_string(f.clone()), right.clone().as_string(f.clone())),
            BinOp::And => format!("({} && {})", left.clone().as_string(f.clone()), right.clone().as_string(f.clone())),
            BinOp::Or =>  format!("({} || {})", left.clone().as_string(f.clone()), right.clone().as_string(f.clone())),
            BinOp::Equal => format!("({} == {})", left.clone().as_string(f.clone()), right.clone().as_string(f.clone())),
            BinOp::NotEqual => format!("({} != {})", left.clone().as_string(f.clone()), right.clone().as_string(f.clone())),
            BinOp::LessThan => format!("({} < {})", left.clone().as_string(f.clone()), right.clone().as_string(f.clone())),
            BinOp::LessThanEqual => format!("({} <= {})", left.clone().as_string(f.clone()), right.clone().as_string(f.clone())),
            BinOp::GreaterThan => format!("({} > {})", left.clone().as_string(f.clone()), right.clone().as_string(f.clone())),
            BinOp::GreaterThanEqual => format!("({} >= {})", left.clone().as_string(f.clone()), right.clone().as_string(f.clone())),
            BinOp::Plus => format!("({} + {})", left.clone().as_string(f.clone()), right.clone().as_string(f.clone())),
            BinOp::Minus => format!("({} - {})", left.clone().as_string(f.clone()), right.clone().as_string(f.clone())),
            BinOp::Multiply => format!("({} * {})", left.clone().as_string(f.clone()), right.clone().as_string(f.clone())),
            BinOp::Divide => format!("({} / {})", left.clone().as_string(f.clone()), right.clone().as_string(f.clone())),
            BinOp::Modulo => format!("({} % {})", left.clone().as_string(f.clone()), right.clone().as_string(f.clone())),
            
        }
      },
      RExpr::Typ { op, val, of, type_: _ } => {
        match op{
            TyOp::IsInstanceOf => format!("({} instanceof {})", val.clone().as_string(f.clone()), of),
            TyOp::IsNotInstanceOf => format!("({} not instanceof {})", val.clone().as_string(f.clone()), of),
        }
      },
      RExpr::Uno { op, val, type_: _ } => {
        match op{
            UnOp::Negate => format!("!{}", val.clone().as_string(f.clone())),
            UnOp::Negative => format!("-{}", val.clone().as_string(f.clone())),
        }
      },
      RExpr::Con { con, left, right, type_: _ } => {
        let con_str = con.clone().as_string(f.clone());
        let left_str = left.clone().as_string(f.clone());
        let right_str = right.clone().as_string(f.clone());
        format!("({} ? {} : {})", con_str, left_str, right_str)
      },
      RExpr::Pur { pur, type_: _ } => {
        f(pur.clone())
      }
    }
  }

  fn default(type_: &NonVoidType) -> Rc<Self> {
    match type_ {
      NonVoidType::IntType{..} => Rc::new(RExpr::Lit { lit: Lit::IntLit { int_value: 0 }, type_: RuntimeType::IntRuntimeType}),
      NonVoidType::FloatType{..} => Rc::new(RExpr::Lit { lit: Lit::FloatLit { float_value: NotNan::new(0.0).unwrap() }, type_: RuntimeType::FloatRuntimeType}),
      NonVoidType::BoolType{..} => Rc::new(RExpr::Lit { lit: Lit::BoolLit { bool_value: false }, type_: RuntimeType::BoolRuntimeType }),
      NonVoidType::StringType{..} => Rc::new(RExpr::Lit { lit: Lit::StringLit { string_value: String::new() }, type_: RuntimeType::StringRuntimeType }),
      _ => panic!("Unsupported runtime type for default value"),
    }
  }
}


//Resolved heapvalue
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Debug)]
pub(crate) enum RHeapValue<T> {
  ObjectValue {
      fields: BTreeMap<Identifier, Rc<T>>,
      type_: RuntimeType,
  },
  ArrayValue {
      elements: Vec<Rc<T>>,
      type_: RuntimeType,
  },
}


#[derive(PartialEq, Clone)]
pub(crate) enum DynamicPointer {
  //return pointer, value to assign
  Ret(u64, Option<Lhs>),
  //Whl entry, after while
  Whl(u64, u64),
  //catch entry, catch exit
  Thr(u64, u64),
}

pub trait MergeEngine {
  type State : MergeState;
  type EValue;
  fn new() -> Self;

  fn next_reference_id(&mut self) -> i64;

  fn make_new_state(self: &mut Self, pc: u64, expr: Rc<Expression>, symbols: Vec<(Identifier, Identifier, RuntimeType)>) -> Self::State;

  fn split_on(&mut self, state: &mut Self::State, expr: Rc<Expression>) -> (Self::State, Self::State);

  fn decl_in(&mut self, state: &mut Self::State, r#type: &NonVoidType, var: &Identifier, _info: &SourcePos) -> Result;

  fn eval_with_r(&mut self, state: &mut Self::State, rhs: &Rhs) -> Self::EValue;
  fn eval_with(&self, state: &Self::State, expr: Rc<Expression>) -> Self::EValue;

  fn assign_expr(&mut self, state: &mut Self::State, lhs: &Lhs, rhs: &Rhs) -> bool;
  fn assign_evaled(&mut self, state: &mut Self::State, lhs: &Lhs, value: Self::EValue);

  fn is_feasible(&self, state: &Self::State) -> bool;
  fn is_valid_for(&self, state: &Self::State, expr: Rc<Expression>) -> bool;

  fn add_assumption_to(&self, state: &mut Self::State, assumption: Either<Rc<Expression>, TypeExpr>);
}
pub trait MergeState {

  fn path_length(&self) -> u64;

  fn incr_path(&mut self) -> u64;

  fn get_pointer(&self) -> u64;

  fn set_pointer(&mut self, ptr: u64) -> u64;

  fn pop_stack(&mut self) -> ();

  fn push_stack(&mut self) -> ();

  fn get_dynamic_cf_size(&self) -> usize;

  fn pop_dynamic_cf(&mut self) -> Option<DynamicPointer>;

  fn push_dynamic_cf(&mut self, dn : DynamicPointer) -> ();

  fn merge_full(&mut self, left : Self, right: Self) -> ();

  fn merge_part(&mut self, left : Self) -> ();
 
}


pub(crate) type SValue = HashSet<Rc<RExpr<()>>>;
type SStack = Vec<HashMap<Identifier, SValue>>;
type SHeap  = HashMap<i64, HashSet<RHeapValue<RExpr<()>>>>;

pub mod svalue{
  use super::*;
  pub fn or(unq_constr_1: SValue, unq_constr_2: SValue) -> SValue {
    iproduct!(unq_constr_1.iter(), unq_constr_2.iter()).map(|(l,r)|{
      RExpr::evaluate_binop(BinOp::Or, l.clone(), r.clone(), RuntimeType::BoolRuntimeType)
    }).collect()
  }
  
  pub fn and(unq_constr_1: SValue, unq_constr_2: SValue) -> SValue {
    iproduct!(unq_constr_1.iter(), unq_constr_2.iter()).map(|(l,r)|{
      RExpr::evaluate_binop(BinOp::And, l.clone(), r.clone(), RuntimeType::BoolRuntimeType)
    }).collect()
  }
  
  pub fn mk_true() -> SValue {
    return hash_unit(Rc::new(RExpr::Lit { lit: Lit::BoolLit { bool_value: true }, type_: RuntimeType::BoolRuntimeType }));
  }
  
}
pub(crate) struct SetState{
  pointer     : u64,
  path_length : u64,
  hed_constr  : SValue,
  unq_constr  : SValue,
  stack       : SStack,
  heap        : SHeap,
  dynamic_cont: Vec<DynamicPointer>
}
pub(crate) struct SetEngine{
  supply: i64,
}

impl MergeEngine for SetEngine{
  type State   = SetState;
  type EValue  = SValue;
  fn new() -> Self {
    return SetEngine { supply: 0 }
  }

  fn next_reference_id(&mut self) -> i64 {
    let s = self.supply.clone();
    self.supply = self.supply+1;
    return s;
  }

   fn make_new_state(self: &mut Self, pc: u64, expr: Rc<Expression>, symbols: Vec<(Identifier, Identifier, RuntimeType)>) -> SetState {
    let mut hashmap = HashMap::new();
    for (k, s, t) in symbols { 
      hashmap.insert(k, hash_unit(Rc::new(RExpr::Sym{id:s, type_: t})));
    }

    let mut temp = SetState{
      path_length: 0,
      pointer: pc,
      hed_constr: svalue::mk_true(),
      unq_constr: svalue::mk_true(),
      stack: vec![hashmap],
      heap : HashMap::new(),
      dynamic_cont: vec![],
    };

    let constr = self.eval_with(&mut temp, expr);

    temp.hed_constr = constr;
    return temp;
  }

   fn split_on(&mut self, state: &mut SetState, expr: Rc<Expression>) -> (SetState, SetState) {

    let new_top: SValue= iproduct!(state.hed_constr.iter(), state.unq_constr.iter())
      .map(|(l,r)| { RExpr::evaluate_binop(BinOp::And, l.clone(), r.clone(), RuntimeType::BoolRuntimeType) } )
      .collect();
    let constrs: SValue = self.eval_with(state, expr);
    let negats: SValue = constrs.iter().map(|c|{ RExpr::evaluate_unop(UnOp::Negate, c.clone())}).collect();


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

   fn decl_in(&mut self, state: &mut SetState, r#type: &NonVoidType, var: &Identifier, _info: &SourcePos) -> Result {
    let val= self.eval_with(state, Rc::new(r#type.default()));
    state.stack.last_mut().map(| frame |{ frame.insert(var.clone(), val) } );
    return Result::Ok;
  }

   fn eval_with_r(&mut self, state: &mut SetState, rhs: &Rhs) -> SValue{
    
    match rhs {
      Rhs::RhsExpression { value, type_: _, info: _ } => {
        let vals = self.eval_with(state, value.clone());
        return vals;
      },
      Rhs::RhsField { var, field, type_: _, info: _ } => {
        let _stack = state.stack.last().unwrap();
        let reference_set = self.eval_with(state, var.clone());
        let mut new_values = HashSet::new();
        for reference in reference_set {
          if let RExpr::Ref { ptr, type_: _ } = reference.as_ref() {
            for heap_value in state.heap.get(ptr).unwrap_or(&HashSet::new()) {
              if let RHeapValue::ObjectValue { fields, type_: _ } = heap_value {
                if let Some(value) = fields.get(field) {
                  new_values.insert(value.clone());
                }
              } else {
                panic!("Expected an object value in the heap, but got {:?}", heap_value);
              }
            }
          } else {
            panic!("Expected a reference, but got {:?}", reference);
          }
        }
        return new_values;
      },
      Rhs::RhsElem { var, index, type_: _, info: _ } => {
        let _stack = state.stack.last().unwrap();
        let reference_set = self.eval_with(state, var.clone());

        let index_set: Vec<usize> = self.eval_with(state, index.clone()).into_iter().map(|i| {
          if let RExpr::Lit { lit: Lit::IntLit { int_value }, .. } = i.as_ref() {
            *int_value as usize
          } else {
            panic!("Expected an integer literal for array index, but got {:?}", i);
          }
        }).collect();

        let mut new_values = HashSet::new();
        for (reference, index) in iproduct!(reference_set.iter(), index_set.iter()) {
          if let RExpr::Ref { ptr, type_: _ } = reference.as_ref() {
            for heap_value in state.heap.get(ptr).unwrap_or(&HashSet::new()) {
              if let RHeapValue::ArrayValue { elements, type_: _ } = heap_value {
                if let Some(value) = elements.get(*index) {
                  new_values.insert(value.clone());
                }
              } else {
                panic!("Expected an array value in the heap, but got {:?}", heap_value);
              }
            }
          } else {
            panic!("Expected a reference, but got {:?}", reference);
          }
        }
        return new_values;
      },
      Rhs::RhsArray { array_type, sizes, type_, info: _ } => {
        assert!(sizes.len() == 1, "Support for only 1D arrays");
        let size = sizes[0].clone();
        let sizes: Vec<_> = self.eval_with(state, size).into_iter().map(|i| {
          if let RExpr::Lit { lit: Lit::IntLit { int_value }, .. } = i.as_ref() {
            *int_value as usize
          } else {
            panic!("Expected an integer literal for array index, but got {:?}", i);
          }
        }).collect();

        let new_ref = self.next_reference_id();
        let mut new_values = HashSet::new();
        for size in sizes{
          let mut new_elements = vec![];
          for _ in 0..size {
            
            new_elements.push(RExpr::default(array_type));
          }
          let new_value = RHeapValue::ArrayValue {
            elements: new_elements,
            type_: array_type.clone().into(),
          };

          
          new_values.insert(new_value);
        }
        state.heap.insert(new_ref,new_values);
        return hash_unit(Rc::new(RExpr::Ref { ptr: new_ref, type_: type_.clone() }));
      },
      Rhs::RhsCast { cast_type: _, var: _, info: _ } => todo!("casting"),
      Rhs::RhsCall { invocation: _, type_: _, info: _ } => unreachable!("should be handled by the engine"),
    }

  }
   fn eval_with(& self, state: &SetState, expr: Rc<Expression>) -> SValue{
    match expr.as_ref(){
      Expression::Lit { lit, type_, info: _ } 
        => hash_unit(Rc::new(RExpr::Lit { lit: lit.clone(), type_: type_.clone() })),
        Expression::SymbolicVar { var, type_, info: _ } 
        => hash_unit(Rc::new(RExpr::Sym { id: var.clone(), type_: type_.clone() })),
      Expression::Ref { ref_, type_, info: _ } 
        => hash_unit(Rc::new(RExpr::Ref { ptr: ref_.clone(), type_: type_.clone() })),

      Expression::Var { var, type_: _, info: _ } => {
        state.stack.last().unwrap().get(var).unwrap().clone()
      },
      
      Expression::Conditional { guard, true_, false_, type_, info: _ } => {
        let gs = self.eval_with(state, guard.clone());
        let ls = self.eval_with(state, true_.clone());
        let rs = self.eval_with(state, false_.clone());
        iproduct!(gs.iter(), ls.iter(), rs.iter()).map(|(g,l,r)|{
          RExpr::evaluate_guard(g.clone(),l.clone(),r.clone(), type_.clone())
        }).collect()

      },
      Expression::BinOp { bin_op, lhs, rhs, type_, info: _ } => {
        let ls = self.eval_with(state, lhs.clone());
        let rs = self.eval_with(state, rhs.clone());
        iproduct!(ls.iter(), rs.iter()).map(|(l, r)|{
          RExpr::evaluate_binop(bin_op.clone(), l.clone(), r.clone(), type_.clone())
        }).collect()
      },

      Expression::TypeExpr { texpr } => {
        match texpr {
            TypeExpr::InstanceOf { var, rhs, info: _ } => {
              let vals = state.stack.last().unwrap().get(var).unwrap().clone();
              vals.iter().map(|val|{RExpr::evaluate_tyop(TyOp::IsInstanceOf, val.clone(), rhs.clone())}).collect()
            },
            TypeExpr::NotInstanceOf { var, rhs, info: _ } => {
              let vals = state.stack.last().unwrap().get(var).unwrap().clone();
              vals.iter().map(|val|{RExpr::evaluate_tyop(TyOp::IsNotInstanceOf, val.clone(), rhs.clone())}).collect()
            },
        }        

      },

      Expression::UnOp { un_op, value, type_: _, info: _ } => {
        let vals = self.eval_with(state, value.clone());
        vals.iter().map(|val|{ RExpr::evaluate_unop(un_op.clone(), val.clone())}).collect()
      },

      //should de doable
      Expression::SizeOf { var: _, type_: _, info: _ } => todo!(),

      //won't be done for a while
      Expression::SymbolicRef { var: _, type_: _, info: _ } => todo!(),
      Expression::Forall { elem: _, range: _, domain: _, formula: _, type_: _, info: _ } => todo!(),
      Expression::Exists { elem: _, range: _, domain: _, formula: _, type_: _, info: _ } => todo!(),

    }
  }

   fn assign_expr(&mut self, state: &mut SetState, lhs: &Lhs, rhs: &Rhs) -> bool{
    let expr = self.eval_with_r(state, rhs);
    self.assign_evaled(state, lhs, expr);
    return true;
  }
   fn assign_evaled(&mut self, state: &mut SetState, lhs: &Lhs, value: SValue){
    match lhs{
      Lhs::LhsVar { var, type_: _, info: _ } => {
        let stack = state.stack.last_mut().unwrap();
        stack.insert(var.clone(), value);

      },
      Lhs::LhsElem { var, index, type_: _, info: _ } => {
        let indexset: Vec<usize> = self.eval_with(state, index.clone()).into_iter().map(|i|{
          if let RExpr::Lit { lit: Lit::IntLit { int_value }, .. } = i.as_ref() {
            *int_value as usize
          } else {
            panic!("Expected an integer literal for array index, but got {:?}", i);
          }
        }).collect();
        let stack = state.stack.last().unwrap();
        let references = stack.get(var).unwrap();
        //its a hashset of possibilities, but each one should be fully resolved

        let i_rs : Vec<_> = iproduct!(indexset, references).collect();
        // if there is only one possible reference to change, then the old value of that reference can be thrown away; 
        let mut buffer = HashMap::new(); 
        for (index, reference) in i_rs {
          if let RExpr::Ref { ptr, type_: _ } = reference.as_ref() {
            let mut new_values = HashSet::new();
            for heap_value in state.heap.get(ptr).unwrap_or(&HashSet::new()) {
              if let RHeapValue::ArrayValue { elements, type_ } = heap_value {
                for val in &value {
                  let mut updated_elements = elements.clone();
                  updated_elements[index] = val.clone();
                  new_values.insert(RHeapValue::ArrayValue {
                    elements: updated_elements,
                    type_: type_.clone(),
                  });
                }
              } else {
                panic!("Expected an array value in the heap, but got {:?}", heap_value);
              }
              if references.len() != 1 {
                new_values.insert(heap_value.clone());
              }
            }
            buffer.insert(ptr, new_values);
          } else {
            panic!("Expected a reference, but got {:?}", reference);
          }
        }  for (k,v) in buffer{
          state.heap.insert(*k, v);
        }
      }
      Lhs::LhsField { var, var_type: _, field, type_: _, info: _ } => {
        let stack = state.stack.last().unwrap();
        let references = stack.get(var).unwrap();

        let mut buffer = HashMap::new();
        for reference in references {
          if let RExpr::Ref { ptr, type_: _ } = reference.as_ref() {
            let mut new_values = HashSet::new();
            for heap_value in state.heap.get(ptr).unwrap_or(&HashSet::new()) {
              if let RHeapValue::ObjectValue { fields, type_ } = heap_value {
                for val in &value {
                  let mut updated_fields = fields.clone();
                  updated_fields.insert(field.clone(), val.clone());
                  new_values.insert(RHeapValue::ObjectValue {
                    fields: updated_fields,
                    type_: type_.clone(),
                  });
                }
              } else {
                panic!("Expected an object value in the heap, but got {:?}", heap_value);
              }
              if references.len() != 1 {
                new_values.insert(heap_value.clone());
              }
            }
            buffer.insert(ptr, new_values);
          } else {
            panic!("Expected a reference, but got {:?}", reference);
          }
        }
        for (k, v) in buffer {
          state.heap.insert(*k, v);
        }
      }  
    }
  }

  fn is_feasible(&self, state: &SetState) -> bool {
    let mut config = Config::new();
    config.set_proof_generation(true);
    let context: Context = Context::new(&config);
    let mut bmemory =  HashMap::new();
    let mut imemory =  HashMap::new();
    let solver = Solver::new(&context);
    solver.push();

    let constrs: Vec<_> = iproduct!(state.hed_constr.iter(), state.unq_constr.iter())
      .map(|(l, r)|{
        let temp = Rc::new(RExpr::Bin { 
          op: BinOp::And, 
          left: l.clone(), 
          right: r.clone(), 
          type_: RuntimeType::BoolRuntimeType 
        });
        RExpr::expr_to_bool(temp, &context, &mut bmemory, &mut imemory)
      }).collect();
    
    let constr: Bool<'_> = Bool::or(&context, constrs.iter().collect::<Vec<_>>().as_slice());
    solver.assert(&constr);
    let result = solver.check();
    
    // Check satisfiability
    if let z3::SatResult::Sat = result{
      //println!("Model: {:?}", solver.get_model());
      //println!("proof: {:?}", solver.get_proof());
      solver.pop(1);
      return true;
    }
    else{
      //println!("Model: {:?}", solver.get_model());
      //println!("proof: {:?}", solver.get_proof());
      solver.pop(1);
      return false;
    }
  }
  fn is_valid_for(&self, state: &SetState, expr: Rc<Expression>) -> bool {
    /* 
    if let Some(last_frame) = state.stack.last() {
      for (key, value) in last_frame {
        println!("Key: {:?}", key);
        for possible_value in value {
          println!("Possible Value: {:?}", possible_value.clone().as_string(|v| {return format!("()")} ));
        }
      }
    } else {
      println!("Stack is empty");
    } 
    */
    let config = Config::new();
    let context: Context = Context::new(&config);
    let mut bmemory =  HashMap::new();
    let mut imemory =  HashMap::new();
    let solver = Solver::new(&context);
    solver.push();

    let premise = svalue::and(state.hed_constr.clone(), state.unq_constr.clone());
    let premise: Vec<_> = premise.iter().map(|v|{ RExpr::expr_to_bool(v.clone(), &context, &mut bmemory, &mut imemory) }).collect();
    let premise = Bool::or(&context, premise.iter().collect::<Vec<_>>().as_slice());

    let conclusion = self.eval_with(state, expr);
    let conclusion: Vec<_> = conclusion.iter().map(|v|{ RExpr::expr_to_bool(v.clone(), &context, &mut bmemory, &mut imemory) }).collect();
    let conclusion = Bool::or(&context, conclusion.iter().collect::<Vec<_>>().as_slice()); 
    
    let constraint = premise.implies(&conclusion);
    let constraint = constraint.not();

    solver.assert(&constraint);
    let result = solver.check();
    
    // Check satisfiability
    if let z3::SatResult::Sat = result{
      println!("Model: {:?}", solver.get_model());
      solver.pop(1);
      return false;
    }
    else{
      println!("Model: {:?}", solver.get_model());
      solver.pop(1);
      return true;
    }
  }

   fn add_assumption_to(&self, state: &mut SetState, assumption: Either<Rc<Expression>, TypeExpr>) {
    let expr = assumption.either(
    | s|{ s }, 
    | t|{ Rc::new(Expression::TypeExpr { texpr: t })});
    let cond = self.eval_with(state, expr);
    state.unq_constr = svalue::and(state.unq_constr.clone(), cond);
  }
}

impl  MergeState for SetState {

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

   fn get_dynamic_cf_size(&self) -> usize {
    return self.dynamic_cont.len();
  }

   fn pop_dynamic_cf(&mut self) -> Option<DynamicPointer> {
    return self.dynamic_cont.pop();
  }

   fn push_dynamic_cf(&mut self, dn : DynamicPointer) -> () {
    self.dynamic_cont.push(dn);
  }

   fn merge_full(&mut self, left : Self, right: Self) -> () {
    assert_eq!(self.stack.len(), left.stack.len());
    assert_eq!(self.stack.len(), right.stack.len());
    assert_eq!(left.pointer, right.pointer);

    self.pointer = left.pointer;
    self.path_length = std::cmp::min(left.path_length, right.path_length);
  
    self.unq_constr = svalue::and(
      self.unq_constr.clone(),
      svalue::or(left.unq_constr, right.unq_constr)
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

    self.pointer     = left.pointer;
    self.path_length = left.path_length;
  
    self.unq_constr = svalue::and(
      self.unq_constr.clone(),
      left.unq_constr
    );


    self.heap = left.heap;
    self.stack = left.stack;
    return;  
  }
  
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Debug)]
pub(crate) enum Tree<C, T>{
  Leaf(T),
  Node{ 
    left : (C, Rc<Tree<C, T>>),
    right: (C, Rc<Tree<C, T>>) 
  }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub(crate) struct ITValue(Rc<Tree<TValue, TValue>>);
pub(crate) type TValue = Rc<RExpr<ITValue>>;
type TStack = Vec<HashMap<Identifier, TValue>>;
type THeap  = HashMap<i64, Rc<Tree<Rc<RExpr<ITValue>>, RHeapValue<RExpr<ITValue>>>>>;

pub mod tvalue{
  use super::*;
  
  pub fn mk_true() -> TValue {
    return Rc::new(RExpr::Lit { lit: Lit::BoolLit { bool_value: true }, type_: RuntimeType::BoolRuntimeType });
  }
  
}
pub(crate) struct TreeState
{
  pointer     : u64,
  path_length : u64,
  hed_constr  : TValue,
  unq_constr  : TValue,
  stack       : TStack,
  heap        : THeap,
  dynamic_cont: Vec<DynamicPointer>
}
pub(crate) struct TreeEngine{
  supply: i64,
}


impl MergeState for TreeState{
  fn path_length(&self) -> u64 {
    return self.path_length;
  }

  fn incr_path(&mut self) -> u64 {
    self.path_length = self.path_length + 1;
    return self.path_length;
  }

  fn get_pointer(&self) -> u64 {
    return self.pointer;
  }

  fn set_pointer(&mut self, ptr: u64) -> u64 {
    self.pointer = ptr;
    return self.pointer;
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

  fn get_dynamic_cf_size(&self) -> usize {
    return self.dynamic_cont.len();
  }

  fn pop_dynamic_cf(&mut self) -> Option<DynamicPointer> {
  return self.dynamic_cont.pop();
  }

  fn push_dynamic_cf(&mut self, dn : DynamicPointer) -> () {
    self.dynamic_cont.push(dn);
  }

  fn merge_full(&mut self, left : Self, right: Self) -> () {
    assert_eq!(self.stack.len(), left.stack.len());
    assert_eq!(self.stack.len(), right.stack.len());
    assert_eq!(left.pointer, right.pointer);

    self.pointer = left.pointer;
    self.path_length = std::cmp::min(left.path_length, right.path_length);
  
    let lc = left.unq_constr;
    let rc = right.unq_constr;
    self.unq_constr = RExpr::evaluate_binop(
      BinOp::And,
      self.unq_constr.clone(),
      RExpr::evaluate_binop(
        BinOp::Or, 
        lc.clone(),
        rc.clone(),
        RuntimeType::BoolRuntimeType
      ),
      RuntimeType::BoolRuntimeType
    );
  
    let paired  =  left.stack.into_iter().zip(right.stack);

    self.heap = union_with(left.heap, right.heap,
      |v, w|{
        let ntree = Tree::Node{ left: (lc.clone(), v), right: (rc.clone(), w)} ;
        Rc::new(ntree)
      }
    );
    self.stack = paired.map(|(frame_1, frame_2)|{
      union_with(frame_1, frame_2, |v, w|{ 
        let t = v.get_type();
        Rc::new(RExpr::Pur{
          pur: ITValue(Rc::new(Tree::Node{ 
            left: (lc.clone(), Rc::new(Tree::Leaf(v))), 
            right: (rc.clone(), Rc::new(Tree::Leaf(w)))
          })),
          type_: t
        })
      })
    }).collect();

  }

  fn merge_part(&mut self, left : Self) -> () {
    self.pointer = left.pointer;
    self.path_length = left.path_length;
    self.unq_constr = RExpr::evaluate_binop(
      BinOp::And,
      self.unq_constr.clone(),
      left.unq_constr,
      RuntimeType::BoolRuntimeType
    );
    self.heap = left.heap;
    self.stack = left.stack;
  }
}

impl MergeEngine for TreeEngine{
    type State = TreeState;
    type EValue = TValue;
    fn new() -> Self {
      return TreeEngine{
        supply: 0,
      }
    }

    fn next_reference_id(&mut self) -> i64 {
      let s = self.supply.clone();
      self.supply = self.supply+1;
      return s;
    }

    fn make_new_state(self: &mut Self, pc: u64, expr: Rc<Expression>, symbols: Vec<(Identifier, Identifier, RuntimeType)>) -> Self::State {
      let mut hashmap: HashMap<Identifier, TValue> = HashMap::new();
      for (k, s, t) in symbols { 
        hashmap.insert(k, Rc::new(RExpr::Sym{id:s, type_: t}));
      }
  
      let mut temp = TreeState{
        path_length: 0,
        pointer: pc,
        hed_constr: tvalue::mk_true(),
        unq_constr: tvalue::mk_true(),
        stack: vec![hashmap],
        heap : HashMap::new(),
        dynamic_cont: vec![],
      };
  
      let constr = self.eval_with(&mut temp, expr);
  
      temp.hed_constr = constr;
      return temp;
    }

    fn split_on(&mut self, state: &mut Self::State, expr: Rc<Expression>) -> (Self::State, Self::State) {
      let new_top: TValue = RExpr::evaluate_binop(
        BinOp::And,
        state.hed_constr.clone(),
        state.unq_constr.clone(),
        RuntimeType::BoolRuntimeType
      );
      let constrs: TValue = self.eval_with(state, expr.clone());
      let negates = self.eval_with(state, Expression::not(expr));

      let left = TreeState { 
        path_length: state.path_length,
        pointer: state.pointer,
        hed_constr: new_top.clone(),
        unq_constr: constrs, 
        stack: state.stack.clone(), 
        heap: state.heap.clone(), 
        dynamic_cont: state.dynamic_cont.clone()
      };
      let right = TreeState{ 
        path_length: state.path_length,
        pointer: state.pointer,
        hed_constr: new_top,
        unq_constr: negates, 
        stack: state.stack.clone(), 
        heap: state.heap.clone(), 
        dynamic_cont: state.dynamic_cont.clone() 
      };

      return (left, right);
    }

    fn decl_in(&mut self, state: &mut Self::State, r#type: &NonVoidType, var: &Identifier, _info: &SourcePos) -> Result {
      let val= self.eval_with(state, Rc::new(r#type.default()));
      state.stack.last_mut().map(| frame |{ frame.insert(var.clone(), val) } );
      return Result::Ok;
    }

    fn eval_with_r(&mut self, state: &mut Self::State, rhs: &Rhs) -> TValue {
      match rhs {
        Rhs::RhsExpression { value, type_: _, info: _ } => {
          let vals = self.eval_with(state, value.clone());
          return vals;
        },
        Rhs::RhsField { var, field, type_: _, info: _ } => {
          let _stack = state.stack.last().unwrap();
          let reference = self.eval_with(state, var.clone());
          if let RExpr::Ref { ptr, type_ } = reference.as_ref() {
            let tree= state.heap.get(&ptr).unwrap();
            let tree = Tree::map(tree.clone(), |heap_value| {
              if let RHeapValue::ObjectValue { fields, type_: _ } = heap_value {
                fields.get(field).unwrap().clone()
              } else {
                panic!("Expected an object value in the heap, but got {:?}", heap_value)
              }
            });
            return Rc::new(RExpr::Pur { pur: ITValue(tree), type_: type_.clone() });
          } else if let RExpr::Pur { pur, type_ } = reference.as_ref() {
            let tree = pur.0.clone();
            let fields = Tree::flat_map(tree, |obj|{
              if let RExpr::Ref { ptr, type_: _ } = obj.as_ref(){
                let value = state.heap.get(&ptr).unwrap();
                Tree::map(value.clone(), |heap_value| {
                  if let RHeapValue::ObjectValue { fields, type_: _ } = heap_value {
                    fields.get(field).unwrap().clone()
                  } else {
                    panic!("Expected an object value in the heap, but got {:?}", heap_value);
                  }
                })
              } else {
                panic!("Expected a reference, but got {:?}", obj);
              }
            });
            return Rc::new(RExpr::Pur { pur: ITValue(fields), type_: type_.clone() });

          }
          else {
            panic!("Expected a reference, but got {:?}", reference);
          }
        },
        Rhs::RhsElem { var, index, type_: _, info: _ } => {
          let _stack = state.stack.last().unwrap();
          let reference = self.eval_with(state, var.clone());
          let index = self.eval_with(state, index.clone());
          match index.as_ref(){
            RExpr::Lit{ lit: Lit::IntLit { int_value }, .. } => {
              let index = *int_value as usize;
              match reference.as_ref() {
                RExpr::Ref { ptr, type_ } => {
                  let tree= state.heap.get(&ptr).unwrap();
                  let tree = Tree::map(tree.clone(), |heap_value| {
                    if let RHeapValue::ArrayValue { elements, type_: _ } = heap_value {
                      elements[index].clone()
                    } else {
                      panic!("Expected an array value in the heap, but got {:?}", heap_value)
                    }
                  });
                  return Rc::new(RExpr::Pur { pur: ITValue(tree), type_: type_.clone() });
                },
                RExpr::Pur { pur, type_ } => {
                  let tree = pur.0.clone();
                  let elements = Tree::flat_map(tree, |arr|{
                    if let RExpr::Ref { ptr, type_: _ } = arr.as_ref(){
                      let value = state.heap.get(&ptr).unwrap();
                      Tree::map(value.clone(), |heap_value| {
                        if let RHeapValue::ArrayValue { elements, type_: _ } = heap_value {
                          elements[index].clone()
                        } else {
                          panic!("Expected an array value in the heap, but got {:?}", heap_value);
                        }
                      })
                    } else {
                      panic!("Expected a reference, but got {:?}", arr);
                    }
                  });
                  return Rc::new(RExpr::Pur { pur: ITValue(elements), type_: type_.clone() });
                },
                _ => panic!("Expected an integer literal for array index, but got {:?}", index),
              }
              
            },
            RExpr::Pur{ pur, type_} => {
              let tree = pur.0.clone();
              let tree = Tree::flat_map(tree, |index|{
                let index = if let RExpr::Lit{ lit: Lit::IntLit { int_value }, .. } = index.as_ref() {
                  *int_value as usize
                } else {
                  panic!("Expected an integer literal for array index, but got {:?}", index);
                };
                match reference.as_ref(){
                  RExpr::Ref { ptr, type_: _ } => {
                    let tree= state.heap.get(&ptr).unwrap();
                    let tree = Tree::map(tree.clone(), |heap_value| {
                      if let RHeapValue::ArrayValue { elements, type_: _ } = heap_value {
                        elements[index].clone()
                      } else {
                        panic!("Expected an array value in the heap, but got {:?}", heap_value)
                      }
                    });
                    return tree;
                  },
                  RExpr::Pur { pur, type_: _ } => {
                    let tree = pur.0.clone();
                    let elements = Tree::flat_map(tree, |arr|{
                      if let RExpr::Ref { ptr, type_: _ } = arr.as_ref(){
                        let value = state.heap.get(&ptr).unwrap();
                        Tree::map(value.clone(), |heap_value| {
                          if let RHeapValue::ArrayValue { elements, type_: _ } = heap_value {
                            elements[index].clone()
                          } else {
                            panic!("Expected an array value in the heap, but got {:?}", heap_value);
                          }
                        })
                      } else {
                        panic!("Expected a reference, but got {:?}", arr);
                      }
                    });
                    return elements;
                  }
                  _ => panic!("Expected an reference but got {:?}", reference),
                }
              });
              return Rc::new(RExpr::Pur { pur: ITValue(tree), type_: type_.clone() });
            }
            _ => panic!("Expected an integer literal for array index, but got {:?}", index),
          }
           
           
          
        },
        Rhs::RhsArray { array_type, sizes, type_, info: _ } => {
          assert!(sizes.len() == 1, "Support for only 1D arrays");
          let size = sizes[0].clone();
          let sizes = self.eval_with(state, size);
          let new_ref = self.next_reference_id();
          let heap_value = match sizes.as_ref(){
            RExpr::Lit{ lit: Lit::IntLit { int_value }, .. } => {
              let size = *int_value as usize;
              Rc::new(Tree::Leaf(RHeapValue::ArrayValue {
                elements: vec![RExpr::default(array_type); size],
                type_: array_type.clone().into(),
              }))
            },
            RExpr::Pur{ pur, type_: _} => {
              let tree = pur.0.clone();
              Tree::map(tree, |size|{
                let size = if let RExpr::Lit{ lit: Lit::IntLit { int_value }, .. } = size.as_ref() {
                  *int_value as usize
                } else {
                  panic!("Expected an integer literal for array index, but got {:?}", size);
                };
                RHeapValue::ArrayValue {
                  elements: vec![RExpr::default(array_type); size],
                  type_: array_type.clone().into(),
                }
              })
            }
            _ => panic!("Expected an integer literal for array size, but got {:?}", sizes),
          };

          state.heap.insert(new_ref, heap_value);
          return Rc::new(RExpr::Ref { ptr: new_ref, type_: type_.clone() });
        },
        Rhs::RhsCast { cast_type: _, var: _, info: _ } => todo!("casting"),
        Rhs::RhsCall { invocation: _, type_: _, info: _ } => unreachable!("should be handled by the engine"),
      }
    }

    fn eval_with(&self, state: &Self::State, expr: Rc<Expression>) -> TValue {
      match expr.as_ref(){
        Expression::Lit { lit, type_, info: _ } 
          => Rc::new(RExpr::Lit { lit: lit.clone(), type_: type_.clone() }),
        Expression::SymbolicVar { var, type_, info: _ } 
          => Rc::new(RExpr::Sym { id: var.clone(), type_: type_.clone() }),
        Expression::Ref { ref_, type_, info: _ } 
          => Rc::new(RExpr::Ref { ptr: ref_.clone(), type_: type_.clone() }),
  
        Expression::Var { var, type_: _, info: _ } => {
          state.stack.last().unwrap().get(var).unwrap().clone()
        },
        
        Expression::Conditional { guard, true_, false_, type_, info: _ } => {
          let g = self.eval_with(state, guard.clone());
          let l = self.eval_with(state, true_.clone());
          let r = self.eval_with(state, false_.clone());
          
          RExpr::evaluate_guard(g,l,r, type_.clone())
        }
  
        Expression::BinOp { bin_op, lhs, rhs, type_, info: _ } => {
          let l = self.eval_with(state, lhs.clone());
          let r = self.eval_with(state, rhs.clone());
          RExpr::evaluate_binop(bin_op.clone(), l, r, type_.clone())
        },
  
        Expression::TypeExpr { texpr } => {
          match texpr {
              TypeExpr::InstanceOf { var, rhs, info: _ } => {
                let val = state.stack.last().unwrap().get(var).unwrap().clone();
                RExpr::evaluate_tyop(TyOp::IsInstanceOf, val.clone(), rhs.clone())
              },
              TypeExpr::NotInstanceOf { var, rhs, info: _ } => {
                let val = state.stack.last().unwrap().get(var).unwrap().clone();
                RExpr::evaluate_tyop(TyOp::IsNotInstanceOf, val.clone(), rhs.clone())
              },
          }        
  
        },
  
        Expression::UnOp { un_op, value, type_: _, info: _ } => {
          let val = self.eval_with(state, value.clone());
          RExpr::evaluate_unop(un_op.clone(), val.clone())
        },
  
        //should be doable
        Expression::SizeOf { var: _, type_: _, info: _ } => todo!(),
  
        //won't be done for a while
        Expression::SymbolicRef { var: _, type_: _, info: _ } => todo!(),
        Expression::Forall { elem: _, range: _, domain: _, formula: _, type_: _, info: _ } => todo!(),
        Expression::Exists { elem: _, range: _, domain: _, formula: _, type_: _, info: _ } => todo!(),
  
      }
    }

    fn assign_expr(&mut self, state: &mut Self::State, lhs: &Lhs, rhs: &Rhs) -> bool {
      let rhs = self.eval_with_r(state, rhs);
      self.assign_evaled(state, lhs, rhs);
      return true;
    }

    fn assign_evaled(&mut self,  state:  &mut Self::State, lhs: &Lhs, value: TValue) {
      match lhs{
        Lhs::LhsVar { var, type_: _, info: _ } => {
          let stack = state.stack.last_mut().unwrap();
          stack.insert(var.clone(), value);
  
        },
        Lhs::LhsElem { var, index, type_: _, info: _ } => {
          // It's a single TValue, but it should be fully resolved

          let index_value = self.eval_with(state, index.clone());
          if let RExpr::Lit { lit: Lit::IntLit { int_value }, .. } = index_value.as_ref() {
            let index = *int_value as usize;
            let stack = state.stack.last().unwrap();
            let references = stack.get(var).unwrap();

            if let RExpr::Ref { ptr, type_: _ } = references.as_ref() {
              let heap_value = state.heap.get(ptr).unwrap();
              let new_value = Tree::map(heap_value.clone(), |arr|{
                if let RHeapValue::ArrayValue{ elements, type_ } = arr {  
                  let mut updated_elements = elements.clone();
                  updated_elements[index] = value.clone();
                  RHeapValue::ArrayValue { elements: updated_elements, type_: type_.clone() }
                } else {
                  panic!("Expected an array value in the heap, but got {:?}", arr);
                }
              });
              state.heap.insert(*ptr, new_value);
            } else {
              panic!("Expected a reference, but got {:?}", references);
            }   
          } else {
            panic!("Expected an integer literal for array index, but got {:?}", index_value);
          }
        },  
        Lhs::LhsField { var, var_type: _, field, type_: _, info: _ } => {
          let stack = state.stack.last().unwrap();
          let references = stack.get(var).unwrap();
          if let RExpr::Ref { ptr, type_: _ } = references.as_ref() {
            let heap_value = state.heap.get(ptr).unwrap();
            let new_value = Tree::map(heap_value.clone(),  |obj|{
              if let RHeapValue::ObjectValue { fields, type_ } = obj {
                let mut updated_field = fields.clone();
                updated_field.insert(field.clone(), value.clone());
                RHeapValue::ObjectValue { fields: updated_field, type_: type_.clone() }
              } else {
                panic!("Expected an object value in the heap, but got {:?}", obj);
              }
            });
            state.heap.insert(*ptr, new_value); 
          } else {
            panic!("Expected a reference, but got {:?}", references);
          }
        },
      }
    }

    fn is_feasible(&self, _state: &Self::State) -> bool {
      return true;
    }
    fn is_valid_for(&self, _state: &Self::State, _expr: Rc<Expression>) -> bool {
      return true;
    }
  
     fn add_assumption_to(&self, state: &mut Self::State, assumption: Either<Rc<Expression>, TypeExpr>) {
      let expr = assumption.either(
      | s|{ s }, 
      | t|{ Rc::new(Expression::TypeExpr { texpr: t })});
      let cond = self.eval_with(state, expr);
      state.unq_constr = RExpr::evaluate_binop(
        BinOp::And,
        state.unq_constr.clone(),
        cond,
        RuntimeType::BoolRuntimeType
      );
    }
  }
  

  impl<C, T> Tree<C,T>{
  fn map<F, R>(tree: Rc<Self>, f: F) -> Rc<Tree<C,R>> where T: Clone, C:Clone, F: Clone + Fn(T) -> R {
    match tree.as_ref() {
      Tree::Leaf(value) => Rc::new(Tree::Leaf(f(value.clone()))),
      Tree::Node { left: (p, l), right: (q, r) } => Rc::new(Tree::Node {
        left: (p.clone(), Self::map(l.clone(), f.clone())),
        right: (q.clone(), Self::map(r.clone(), f)),
        }),
      }
    }

  fn flat_map<F, R>(tree: Rc<Self>, f: F) -> Rc<Tree<C,R>> where T: Clone, C:Clone, F: Clone + Fn(T) -> Rc<Tree<C,R>> {
    match tree.as_ref() {
      Tree::Leaf(value) => f(value.clone()),
      Tree::Node { left: (p, l), right: (q, r) } => Rc::new(Tree::Node {
        left: (p.clone(), Self::flat_map(l.clone(), f.clone())),
        right: (q.clone(), Self::flat_map(r.clone(), f)),
        }),
      }
    }

  }