use itertools::izip;
use itertools::Either;

use itertools::iproduct;
use itertools::Merge;
use ordered_float::NotNan;
use utils::utils::{hash_unit, union, union_with};
use z3::ast::Array;
use z3::ast::Datatype;
use z3::DatatypeBuilder;
use z3::DatatypeSort;
use z3::Sort;

use crate::typeable::Typeable;

use crate::SourcePos;
use crate::SymbolTable;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;

use std::hash::Hash;
use std::marker::PhantomData;
use std::panic;

use std::rc::Rc;
pub mod cfg;
pub mod utils;

use crate::language::syntax::Identifier;
use crate::language::*;
use z3::{ast::Ast, ast::Bool, ast::Int, Config, Context, Solver};

pub(crate) enum Result {
    Ok,
    Err,
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Debug)]
pub(crate) enum TyOp {
    IsInstanceOf,
    IsNotInstanceOf,
}
// "resolved" expression
// at least it would be resolved, if we didn't have symbols :pensive:
// or quantifiers, which are unhandled for now
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Debug)]
pub(crate) enum RExpr {
    //literal
    Lit {
        lit: Lit,
        type_: RuntimeType,
    },
    //symbolic literal
    Sym {
        id: Identifier,
        type_: RuntimeType,
    },
    //reference to a variable
    Ref {
        ptr: i64,
        type_: RuntimeType,
        // we expand lazely, when needed
    },
    //binary operation
    Bin {
        op: BinOp,
        left: Rc<RExpr>,
        right: Rc<RExpr>,
        type_: RuntimeType,
    },
    //type operation
    Typ {
        op: TyOp,
        val: Rc<RExpr>,
        of: RuntimeType,
        type_: RuntimeType,
    },
    //unary operation
    Uno {
        op: UnOp,
        val: Rc<RExpr>,
        type_: RuntimeType,
    },
    //constructor
    Con {
        con: Rc<RExpr>,
        left: Rc<RExpr>,
        right: Rc<RExpr>,
        type_: RuntimeType,
    },
}

/** mainly front end simplification **/
impl RExpr {
    fn get_type(&self) -> RuntimeType {
        match self {
            RExpr::Lit { type_, .. } => type_.clone(),
            RExpr::Sym { type_, .. } => type_.clone(),
            RExpr::Ref { type_, .. } => type_.clone(),
            RExpr::Bin { type_, .. } => type_.clone(),
            RExpr::Typ { type_, .. } => type_.clone(),
            RExpr::Uno { type_, .. } => type_.clone(),
            RExpr::Con { type_, .. } => type_.clone(),
        }
    }

    fn and(left: Rc<Self>, right: Rc<Self>) -> Self {
        return RExpr::Bin {
            op: BinOp::And,
            left: left,
            right: right,
            type_: RuntimeType::BoolRuntimeType,
        };
    }

    fn or(left: Rc<Self>, right: Rc<Self>) -> Self {
        return RExpr::Bin {
            op: BinOp::Or,
            left: left,
            right: right,
            type_: RuntimeType::BoolRuntimeType,
        };
    }

    fn evaluate_guard(
        guard: Rc<Self>,
        lhs: Rc<Self>,
        rhs: Rc<Self>,
        type_: RuntimeType,
    ) -> Rc<Self> {
        use crate::syntax::Lit::*;
        use RExpr::*;

        match guard.as_ref() {
            Lit {
                lit: BoolLit { bool_value: true },
                type_: _,
            } => lhs,
            Lit {
                lit: BoolLit { bool_value: false },
                type_: _,
            } => rhs,
            _ => Rc::new(RExpr::Con {
                con: guard,
                left: lhs,
                right: rhs,
                type_,
            }),
        }
    }

    fn evaluate_binop(bin_op: BinOp, lhs: Rc<Self>, rhs: Rc<Self>, type_: RuntimeType) -> Rc<Self> {
        use crate::syntax::BinOp::*;
        use crate::syntax::Lit::*;
        use crate::syntax::RuntimeType::*;
        use RExpr::*;

        match (bin_op, lhs.as_ref(), rhs.as_ref()) {
            (
                _,
                Con {
                    con: p,
                    left: v,
                    right: w,
                    ..
                },
                Con {
                    con: q,
                    left: x,
                    right: y,
                    ..
                },
            ) => {
                if Rc::ptr_eq(p, q) {
                    return Rc::new(Con {
                        con: p.clone(),
                        left: Self::evaluate_binop(bin_op, v.clone(), x.clone(), type_.clone()),
                        right: Self::evaluate_binop(bin_op, w.clone(), y.clone(), type_.clone()),
                        type_: type_.clone(),
                    });
                } else {
                    return Rc::new(Bin {
                        op: bin_op,
                        left: lhs.clone(),
                        right: rhs.clone(),
                        type_: type_.clone(),
                    });
                }
            }
            (
                Implies,
                Lit {
                    lit: BoolLit { bool_value: true },
                    ..
                },
                _,
            ) => rhs,
            (
                Implies,
                Lit {
                    lit: BoolLit { bool_value: false },
                    ..
                },
                _,
            ) => Rc::new(Lit {
                lit: BoolLit { bool_value: true },
                type_: BoolRuntimeType,
            }),
            (
                Implies,
                _,
                Lit {
                    lit: BoolLit { bool_value: true },
                    ..
                },
            ) => rhs,
            (
                Implies,
                _,
                Lit {
                    lit: BoolLit { bool_value: false },
                    ..
                },
            ) => Rc::new(Uno {
                op: UnOp::Negate,
                val: lhs,
                type_: BoolRuntimeType,
            }),
            (Implies, _, _) => Rc::new(RExpr::Bin {
                op: bin_op,
                left: lhs,
                right: rhs,
                type_: BoolRuntimeType,
            }),

            (
                And,
                Lit {
                    lit: BoolLit { bool_value: false },
                    ..
                },
                _,
            ) => lhs,
            (
                And,
                Lit {
                    lit: BoolLit { bool_value: true },
                    ..
                },
                _,
            ) => rhs,
            (
                And,
                _,
                Lit {
                    lit: BoolLit { bool_value: false },
                    ..
                },
            ) => rhs,
            (
                And,
                _,
                Lit {
                    lit: BoolLit { bool_value: true },
                    ..
                },
            ) => lhs,
            (And, _, _) => Rc::new(RExpr::Bin {
                op: bin_op,
                left: lhs,
                right: rhs,
                type_: BoolRuntimeType,
            }),

            (
                Or,
                Lit {
                    lit: BoolLit { bool_value: false },
                    ..
                },
                _,
            ) => rhs,
            (
                Or,
                Lit {
                    lit: BoolLit { bool_value: true },
                    ..
                },
                _,
            ) => lhs,
            (
                Or,
                _,
                Lit {
                    lit: BoolLit { bool_value: false },
                    ..
                },
            ) => lhs,
            (
                Or,
                _,
                Lit {
                    lit: BoolLit { bool_value: true },
                    ..
                },
            ) => rhs,
            (Or, _, _) => Rc::new(RExpr::Bin {
                op: bin_op,
                left: lhs,
                right: rhs,
                type_: BoolRuntimeType,
            }),

            (
                NotEqual,
                Lit {
                    lit: IntLit { int_value: l },
                    ..
                },
                Lit {
                    lit: IntLit { int_value: r },
                    ..
                },
            ) => Rc::new(Lit {
                lit: BoolLit { bool_value: l != r },
                type_: BoolRuntimeType,
            }),
            (
                LessThan,
                Lit {
                    lit: IntLit { int_value: l },
                    ..
                },
                Lit {
                    lit: IntLit { int_value: r },
                    ..
                },
            ) => Rc::new(Lit {
                lit: BoolLit { bool_value: l < r },
                type_: BoolRuntimeType,
            }),
            (
                LessThanEqual,
                Lit {
                    lit: IntLit { int_value: l },
                    ..
                },
                Lit {
                    lit: IntLit { int_value: r },
                    ..
                },
            ) => Rc::new(Lit {
                lit: BoolLit { bool_value: l <= r },
                type_: BoolRuntimeType,
            }),
            (
                GreaterThan,
                Lit {
                    lit: IntLit { int_value: l },
                    ..
                },
                Lit {
                    lit: IntLit { int_value: r },
                    ..
                },
            ) => Rc::new(Lit {
                lit: BoolLit { bool_value: l > r },
                type_: BoolRuntimeType,
            }),
            (
                GreaterThanEqual,
                Lit {
                    lit: IntLit { int_value: l },
                    ..
                },
                Lit {
                    lit: IntLit { int_value: r },
                    ..
                },
            ) => Rc::new(Lit {
                lit: BoolLit { bool_value: l >= r },
                type_: BoolRuntimeType,
            }),

            (Equal, Sym { id: l, .. }, Sym { id: r, .. }) => {
                if l == r {
                    Rc::new(Lit {
                        lit: BoolLit { bool_value: true },
                        type_: BoolRuntimeType,
                    })
                } else {
                    //could still theoretically be equal
                    //but we don't know that
                    Rc::new(RExpr::Bin {
                        op: bin_op,
                        left: lhs,
                        right: rhs,
                        type_: BoolRuntimeType,
                    })
                }
            }
            (NotEqual, Sym { id: l, .. }, Sym { id: r, .. }) => {
                if l == r {
                    Rc::new(Lit {
                        lit: BoolLit { bool_value: false },
                        type_: BoolRuntimeType,
                    })
                } else {
                    //could still theoretically be equal
                    //but we don't know that
                    Rc::new(RExpr::Bin {
                        op: bin_op,
                        left: lhs,
                        right: rhs,
                        type_: BoolRuntimeType,
                    })
                }
            }
            (LessThan, Sym { id: l, .. }, Sym { id: r, .. }) => {
                if l == r {
                    Rc::new(Lit {
                        lit: BoolLit { bool_value: false },
                        type_: BoolRuntimeType,
                    })
                } else {
                    Rc::new(RExpr::Bin {
                        op: bin_op,
                        left: lhs,
                        right: rhs,
                        type_: BoolRuntimeType,
                    })
                }
            }
            (LessThanEqual, Sym { id: l, .. }, Sym { id: r, .. }) => {
                if l == r {
                    Rc::new(Lit {
                        lit: BoolLit { bool_value: true },
                        type_: BoolRuntimeType,
                    })
                } else {
                    Rc::new(RExpr::Bin {
                        op: bin_op,
                        left: lhs,
                        right: rhs,
                        type_: BoolRuntimeType,
                    })
                }
            }
            (GreaterThan, Sym { id: l, .. }, Sym { id: r, .. }) => {
                if l == r {
                    Rc::new(Lit {
                        lit: BoolLit { bool_value: false },
                        type_: BoolRuntimeType,
                    })
                } else {
                    Rc::new(RExpr::Bin {
                        op: bin_op,
                        left: lhs,
                        right: rhs,
                        type_: BoolRuntimeType,
                    })
                }
            }
            (GreaterThanEqual, Sym { id: l, .. }, Sym { id: r, .. }) => {
                if l == r {
                    Rc::new(Lit {
                        lit: BoolLit { bool_value: true },
                        type_: BoolRuntimeType,
                    })
                } else {
                    Rc::new(RExpr::Bin {
                        op: bin_op,
                        left: lhs,
                        right: rhs,
                        type_: BoolRuntimeType,
                    })
                }
            }

            (
                Plus,
                Lit {
                    lit: IntLit { int_value: l },
                    ..
                },
                Lit {
                    lit: IntLit { int_value: r },
                    ..
                },
            ) => Rc::new(Lit {
                lit: IntLit { int_value: l + r },
                type_: type_.clone(),
            }),
            (
                Minus,
                Lit {
                    lit: IntLit { int_value: l },
                    ..
                },
                Lit {
                    lit: IntLit { int_value: r },
                    ..
                },
            ) => Rc::new(Lit {
                lit: IntLit { int_value: l - r },
                type_: type_.clone(),
            }),
            (
                Multiply,
                Lit {
                    lit: IntLit { int_value: l },
                    ..
                },
                Lit {
                    lit: IntLit { int_value: r },
                    ..
                },
            ) => Rc::new(Lit {
                lit: IntLit { int_value: l * r },
                type_: type_.clone(),
            }),
            (
                Divide,
                Lit {
                    lit: IntLit { int_value: l },
                    ..
                },
                Lit {
                    lit: IntLit { int_value: r },
                    ..
                },
            ) => {
                if *r != 0 {
                    Rc::new(Lit {
                        lit: IntLit { int_value: l / r },
                        type_: type_.clone(),
                    })
                } else {
                    panic!("Division by zero")
                }
            }
            (
                Modulo,
                Lit {
                    lit: IntLit { int_value: l },
                    ..
                },
                Lit {
                    lit: IntLit { int_value: r },
                    ..
                },
            ) => {
                if *r != 0 {
                    Rc::new(Lit {
                        lit: IntLit { int_value: l % r },
                        type_: type_.clone(),
                    })
                } else {
                    panic!("Modulo by zero")
                }
            }
            (
                Plus,
                Lit {
                    lit: IntLit { int_value: 0 },
                    ..
                },
                _,
            ) => rhs,
            (
                Plus,
                _,
                Lit {
                    lit: IntLit { int_value: 0 },
                    ..
                },
            ) => lhs,
            (
                Minus,
                _,
                Lit {
                    lit: IntLit { int_value: 0 },
                    ..
                },
            ) => lhs,
            (
                Multiply,
                Lit {
                    lit: IntLit { int_value: 1 },
                    ..
                },
                _,
            ) => rhs,
            (
                Multiply,
                _,
                Lit {
                    lit: IntLit { int_value: 1 },
                    ..
                },
            ) => lhs,
            (
                Multiply,
                Lit {
                    lit: IntLit { int_value: 0 },
                    ..
                },
                _,
            ) => lhs,
            (
                Multiply,
                _,
                Lit {
                    lit: IntLit { int_value: 0 },
                    ..
                },
            ) => rhs,
            (
                Divide,
                _,
                Lit {
                    lit: IntLit { int_value: 1 },
                    ..
                },
            ) => lhs,
            (
                Modulo,
                _,
                Lit {
                    lit: IntLit { int_value: 1 },
                    ..
                },
            ) => Rc::new(Lit {
                lit: IntLit { int_value: 0 },
                type_: type_.clone(),
            }),

            (
                Minus,
                Bin {
                    op: Minus,
                    left: symbol,
                    right: lit1,
                    type_,
                },
                Lit { lit: lit2, .. },
            ) => {
                if let (
                    RExpr::Sym { .. },
                    RExpr::Lit {
                        lit: IntLit { int_value: x, .. },
                        ..
                    },
                ) = (symbol.as_ref(), lit1.as_ref())
                {
                    if let IntLit { int_value: y, .. } = lit2 {
                        let combined_lit = Rc::new(Lit {
                            lit: IntLit { int_value: x + y },
                            type_: type_.clone(),
                        });
                        return Rc::new(Bin {
                            op: Minus,
                            left: symbol.clone(),
                            right: combined_lit,
                            type_: type_.clone(),
                        });
                    }
                }
                Rc::new(Bin {
                    op: bin_op,
                    left: lhs.clone(),
                    right: rhs.clone(),
                    type_: type_.clone(),
                })
            }
            (
                Plus,
                Bin {
                    op: Plus,
                    left,
                    right,
                    type_,
                },
                Lit { lit, .. },
            ) => {
                if let IntLit { int_value: y, .. } = lit {
                    if let (
                        RExpr::Sym { .. },
                        RExpr::Lit {
                            lit: IntLit { int_value: x },
                            ..
                        },
                    ) = (left.as_ref(), right.as_ref())
                    {
                        let combined_lit = Rc::new(Lit {
                            lit: IntLit { int_value: x + y },
                            type_: type_.clone(),
                        });
                        return Rc::new(Bin {
                            op: Plus,
                            left: left.clone(),
                            right: combined_lit,
                            type_: type_.clone(),
                        });
                    } else if let (
                        RExpr::Lit {
                            lit: IntLit { int_value: x },
                            ..
                        },
                        RExpr::Sym { .. },
                    ) = (left.as_ref(), right.as_ref())
                    {
                        let combined_lit = Rc::new(Lit {
                            lit: IntLit { int_value: x + y },
                            type_: type_.clone(),
                        });
                        return Rc::new(Bin {
                            op: Plus,
                            left: right.clone(),
                            right: combined_lit,
                            type_: type_.clone(),
                        });
                    }
                }

                Rc::new(Bin {
                    op: bin_op,
                    left: lhs.clone(),
                    right: rhs.clone(),
                    type_: type_.clone(),
                })
            }
            // rest to be done at some other time :releved:
            (Equal, _, _) => Rc::new(RExpr::Bin {
                op: bin_op,
                left: lhs,
                right: rhs,
                type_: BoolRuntimeType,
            }),
            (NotEqual, _, _) => Rc::new(RExpr::Bin {
                op: bin_op,
                left: lhs,
                right: rhs,
                type_: BoolRuntimeType,
            }),
            (LessThan, _, _) => Rc::new(RExpr::Bin {
                op: bin_op,
                left: lhs,
                right: rhs,
                type_,
            }),
            (LessThanEqual, _, _) => Rc::new(RExpr::Bin {
                op: bin_op,
                left: lhs,
                right: rhs,
                type_,
            }),
            (GreaterThan, _, _) => Rc::new(RExpr::Bin {
                op: bin_op,
                left: lhs,
                right: rhs,
                type_,
            }),
            (GreaterThanEqual, _, _) => Rc::new(RExpr::Bin {
                op: bin_op,
                left: lhs,
                right: rhs,
                type_,
            }),

            (Plus, _, _) => Rc::new(RExpr::Bin {
                op: bin_op,
                left: lhs,
                right: rhs,
                type_,
            }),
            (Minus, _, _) => Rc::new(RExpr::Bin {
                op: bin_op,
                left: lhs,
                right: rhs,
                type_,
            }),
            (Multiply, _, _) => Rc::new(RExpr::Bin {
                op: bin_op,
                left: lhs,
                right: rhs,
                type_,
            }),
            (Divide, _, _) => Rc::new(RExpr::Bin {
                op: bin_op,
                left: lhs,
                right: rhs,
                type_,
            }),
            (Modulo, _, _) => Rc::new(RExpr::Bin {
                op: bin_op,
                left: lhs,
                right: rhs,
                type_,
            }),
        }
    }
    fn evaluate_tyop(ty_op: TyOp, value: Rc<Self>, _of_this_type: RuntimeType) -> Rc<Self> {
        let t = value.get_type();
        let x = match ty_op {
            TyOp::IsInstanceOf => RExpr::Lit {
                lit: Lit::BoolLit {
                    bool_value: t == _of_this_type,
                },
                type_: RuntimeType::BoolRuntimeType,
            },
            TyOp::IsNotInstanceOf => RExpr::Lit {
                lit: Lit::BoolLit {
                    bool_value: t != _of_this_type,
                },
                type_: RuntimeType::BoolRuntimeType,
            },
        };
        return Rc::new(x);
    }

    fn evaluate_unop(unop: UnOp, expression: Rc<Self>) -> Rc<Self> {
        use crate::syntax::Lit::*;
        use crate::syntax::UnOp::*;
        use RExpr::*;

        match (unop, expression.as_ref()) {
            (
                Negative,
                Lit {
                    lit: IntLit { int_value },
                    type_,
                },
            ) => Rc::new(Lit {
                lit: IntLit {
                    int_value: -int_value.clone(),
                },
                type_: type_.clone(),
            }),
            (
                Negative,
                Lit {
                    lit: FloatLit { float_value },
                    type_,
                },
            ) => Rc::new(Lit {
                lit: FloatLit {
                    float_value: -float_value.clone(),
                },
                type_: type_.clone(),
            }),
            //todo: negative of expressions
            //but maybe that one is less of a big deal?
            (
                Negate,
                Lit {
                    lit: BoolLit { bool_value },
                    type_,
                },
            ) => Rc::new(Lit {
                lit: BoolLit {
                    bool_value: !bool_value.clone(),
                },
                type_: type_.clone(),
            }),
            (Negate, Typ { op, val, of, type_ }) => Rc::new(Typ {
                op: Self::flip_t(op),
                val: val.clone(),
                of: of.clone(),
                type_: type_.clone(),
            }),

            (
                Negate,
                Bin {
                    op,
                    left,
                    right,
                    type_,
                },
            ) => {
                if let Some(binop) = Self::try_invert_bool_binop(op) {
                    Rc::new(Bin {
                        op: binop,
                        left: left.clone(),
                        right: right.clone(),
                        type_: type_.clone(),
                    })
                } else {
                    Rc::new(Uno {
                        op: Negate,
                        val: expression.clone(),
                        type_: type_.clone(),
                    })
                }
            }
            (
                _,
                Con {
                    con,
                    left,
                    right,
                    type_,
                },
            ) => Rc::new(Con {
                con: con.clone(),
                left: Self::evaluate_unop(unop, left.clone()),
                right: Self::evaluate_unop(unop, right.clone()),
                type_: type_.clone(),
            }),
            (_, Uno { val, .. }) => val.clone(),
            (Negate, _) => Rc::new(Uno {
                op: Negate,
                val: expression.clone(),
                type_: RuntimeType::BoolRuntimeType,
            }),
            (Negative, _) => Rc::new(Uno {
                op: Negate,
                val: expression.clone(),
                type_: expression.get_type(),
            }),
        }
    }

    fn flip_t(ty_op: &TyOp) -> TyOp {
        match ty_op {
            TyOp::IsInstanceOf => TyOp::IsNotInstanceOf,
            TyOp::IsNotInstanceOf => TyOp::IsInstanceOf,
        }
    }

    fn try_invert_bool_binop(bin_op: &BinOp) -> Option<BinOp> {
        use crate::syntax::BinOp::*;
        match bin_op {
            Equal => Some(NotEqual),
            NotEqual => Some(Equal),
            LessThan => Some(GreaterThanEqual),
            LessThanEqual => Some(GreaterThan),
            GreaterThan => Some(LessThanEqual),
            GreaterThanEqual => Some(LessThan),
            _ => None,
        }
    }

    fn as_string(self: Rc<Self>) -> String {
        match self.as_ref() {
            RExpr::Lit { lit, type_: _ } => match lit {
                Lit::IntLit { int_value } => format!("{}", int_value),
                Lit::FloatLit { float_value } => format!("{}", float_value),
                Lit::BoolLit { bool_value } => format!("{}", bool_value),
                Lit::StringLit { string_value } => format!("\"{}\"", string_value),
                Lit::NullLit {} => format!("null"),
                Lit::CharLit { char_value } => format!("'{}'", char_value),
                Lit::UIntLit { uint_value } => format!("{}", uint_value),
            },
            RExpr::Sym { id, type_: _ } => {
                format!("${}", id)
            }
            RExpr::Ref { ptr, type_: _ } => {
                format!("&{}", ptr)
            }
            RExpr::Bin {
                op,
                left,
                right,
                type_: _,
            } => match op {
                BinOp::Implies => format!(
                    "({} => {})",
                    left.clone().as_string(),
                    right.clone().as_string()
                ),
                BinOp::And => format!(
                    "({} && {})",
                    left.clone().as_string(),
                    right.clone().as_string()
                ),
                BinOp::Or => format!(
                    "({} || {})",
                    left.clone().as_string(),
                    right.clone().as_string()
                ),
                BinOp::Equal => format!(
                    "({} == {})",
                    left.clone().as_string(),
                    right.clone().as_string()
                ),
                BinOp::NotEqual => format!(
                    "({} != {})",
                    left.clone().as_string(),
                    right.clone().as_string()
                ),
                BinOp::LessThan => format!(
                    "({} < {})",
                    left.clone().as_string(),
                    right.clone().as_string()
                ),
                BinOp::LessThanEqual => format!(
                    "({} <= {})",
                    left.clone().as_string(),
                    right.clone().as_string()
                ),
                BinOp::GreaterThan => format!(
                    "({} > {})",
                    left.clone().as_string(),
                    right.clone().as_string()
                ),
                BinOp::GreaterThanEqual => format!(
                    "({} >= {})",
                    left.clone().as_string(),
                    right.clone().as_string()
                ),
                BinOp::Plus => format!(
                    "({} + {})",
                    left.clone().as_string(),
                    right.clone().as_string()
                ),
                BinOp::Minus => format!(
                    "({} - {})",
                    left.clone().as_string(),
                    right.clone().as_string()
                ),
                BinOp::Multiply => format!(
                    "({} * {})",
                    left.clone().as_string(),
                    right.clone().as_string()
                ),
                BinOp::Divide => format!(
                    "({} / {})",
                    left.clone().as_string(),
                    right.clone().as_string()
                ),
                BinOp::Modulo => format!(
                    "({} % {})",
                    left.clone().as_string(),
                    right.clone().as_string()
                ),
            },
            RExpr::Typ {
                op,
                val,
                of,
                type_: _,
            } => match op {
                TyOp::IsInstanceOf => {
                    format!("({} instanceof {})", val.clone().as_string(), of)
                }
                TyOp::IsNotInstanceOf => {
                    format!("({} not instanceof {})", val.clone().as_string(), of)
                }
            },
            RExpr::Uno { op, val, type_: _ } => match op {
                UnOp::Negate => format!("!{}", val.clone().as_string()),
                UnOp::Negative => format!("-{}", val.clone().as_string()),
            },
            RExpr::Con {
                con,
                left,
                right,
                type_: _,
            } => {
                let con_str = con.clone().as_string();
                let left_str = left.clone().as_string();
                let right_str = right.clone().as_string();
                format!("({} ? {} : {})", con_str, left_str, right_str)
            }
        }
    }

}

struct Z3Builder<'a, F, G> {
    bmemory: HashMap<Identifier, Bool<'a>>,
    imemory: HashMap<Identifier, Int<'a>>,
    amemory: HashMap<i64, Array<'a>>,
    rmemory: HashMap<i64, Datatype<'a>>,
    get_arr: F,
    get_ref: G,
}

impl<'a, F, G> Z3Builder<'a, F, G> {
    fn new(f: F, g: G) -> Self {
        Z3Builder {
            bmemory: HashMap::new(),
            imemory: HashMap::new(),
            amemory: HashMap::new(),
            rmemory: HashMap::new(),
            get_arr: f,
            get_ref: g,
        }
    }
    fn expr_to_bool(self: &mut Self, expr: Rc<RExpr>, context: &'a Context) -> Bool<'a>
    where
        F: Clone + Fn(&i64, &'a Context) -> Array<'a>,
        G: Clone + Fn(&i64, &'a Context) -> Datatype<'a>,
    {
        match expr.as_ref() {
            RExpr::Lit { lit, type_: _ } => match lit {
                Lit::BoolLit { bool_value } => Bool::from_bool(context, *bool_value),
                _ => panic!("Expected a boolean literal, but got {:?}", lit),
            },
            RExpr::Sym { id, type_ } => {
                if let Some(ast) = self.bmemory.get(id) {
                    return ast.clone();
                } else {
                    let ast = match type_ {
                        RuntimeType::BoolRuntimeType => Bool::new_const(&context, id.as_str()),
                        _ => panic!("Expected a boolean type, but got {:?}", type_),
                    };
                    self.bmemory.insert(id.clone(), ast.clone());
                    return ast;
                }
            }
            RExpr::Ref { .. } => unreachable!("this one really should not be here"),
            RExpr::Bin {
                op,
                left,
                right,
                type_: _,
            } => match op {
                BinOp::Implies => {
                    let left = self.expr_to_bool(left.clone(), context);
                    let right = self.expr_to_bool(right.clone(), context);
                    return Bool::implies(&left, &right);
                }
                BinOp::And => {
                    let left = self.expr_to_bool(left.clone(), context);
                    let right = self.expr_to_bool(right.clone(), context);
                    return Bool::and(context, &[&left, &right]);
                }
                BinOp::Or => {
                    let left = self.expr_to_bool(left.clone(), context);
                    let right = self.expr_to_bool(right.clone(), context);
                    return Bool::or(context, &[&left, &right]);
                }
                BinOp::Equal => {
                    let ltype = left.get_type();
                    let rtype = right.get_type();
                    assert!(ltype == rtype, "Expected the same type for both sides of the equality, but got {:?} and {:?}", ltype, rtype);
                    match ltype {
                        RuntimeType::BoolRuntimeType => {
                            let left = self.expr_to_bool(left.clone(), context);
                            let right = self.expr_to_bool(right.clone(), context);
                            return left._eq(&right);
                        }
                        RuntimeType::IntRuntimeType => {
                            let left = self.expr_to_int(left.clone(), context);
                            let right = self.expr_to_int(right.clone(), context);
                            return left._eq(&right);
                        }
                        RuntimeType::ARRAYRuntimeType => {
                            let left = self.expr_to_array(left.clone(), context);
                            let right = self.expr_to_array(right.clone(), context);
                            return left._eq(&right);
                        }
                        RuntimeType::ReferenceRuntimeType { type_, .. } => {
                            let left = self.expr_to_ref(left.clone(), context);
                            let right = self.expr_to_ref(right.clone(), context);
                            return left._eq(&right);
                        }
                        _ => panic!(
                            "Expected a boolean or integer type for equality, but got {:?}",
                            ltype
                        ),
                    }
                }
                BinOp::NotEqual => {
                    let ltype = left.get_type();
                    let rtype = right.get_type();
                    assert!(ltype == rtype, "Expected the same type for both sides of the equality, but got {:?} and {:?}", ltype, rtype);
                    match ltype {
                        RuntimeType::BoolRuntimeType => {
                            let left = self.expr_to_bool(left.clone(), context);
                            let right = self.expr_to_bool(right.clone(), context);
                            return left._eq(&right).not();
                        }
                        RuntimeType::IntRuntimeType => {
                            let left = self.expr_to_int(left.clone(), context);
                            let right = self.expr_to_int(right.clone(), context);
                            return left._eq(&right).not();
                        }
                        _ => panic!(
                            "Expected a boolean or integer type for equality, but got {:?}",
                            ltype
                        ),
                    }
                }
                BinOp::LessThan => {
                    let ltype = left.get_type();
                    let rtype = right.get_type();
                    assert!(ltype == rtype, "Expected the same type for both sides of the equality, but got {:?} and {:?}", ltype, rtype);
                    match ltype {
                        RuntimeType::IntRuntimeType => {
                            let left: Int<'_> = self.expr_to_int(left.clone(), context);
                            let right: Int<'_> = self.expr_to_int(right.clone(), context);
                            return left.lt(&right);
                        }
                        _ => panic!("Expected a integer type for lt, but got {:?}", ltype),
                    }
                }
                BinOp::LessThanEqual => {
                    let ltype = left.get_type();
                    let rtype = right.get_type();
                    assert!(ltype == rtype, "Expected the same type for both sides of the equality, but got {:?} and {:?}", ltype, rtype);
                    match ltype {
                        RuntimeType::IntRuntimeType => {
                            let left: Int<'_> = self.expr_to_int(left.clone(), context);
                            let right: Int<'_> = self.expr_to_int(right.clone(), context);
                            return left.le(&right);
                        }
                        _ => panic!("Expected a integer type for lt, but got {:?}", ltype),
                    }
                }
                BinOp::GreaterThan => {
                    let ltype = left.get_type();
                    let rtype = right.get_type();
                    assert!(ltype == rtype, "Expected the same type for both sides of the equality, but got {:?} and {:?}", ltype, rtype);
                    match ltype {
                        RuntimeType::IntRuntimeType => {
                            let left: Int<'_> = self.expr_to_int(left.clone(), context);
                            let right: Int<'_> = self.expr_to_int(right.clone(), context);
                            return left.gt(&right);
                        }
                        _ => panic!("Expected a integer type for lt, but got {:?}", ltype),
                    }
                }
                BinOp::GreaterThanEqual => {
                    let ltype = left.get_type();
                    let rtype = right.get_type();
                    assert!(ltype == rtype, "Expected the same type for both sides of the equality, but got {:?} and {:?}", ltype, rtype);
                    match ltype {
                        RuntimeType::IntRuntimeType => {
                            let left: Int<'_> = self.expr_to_int(left.clone(), context);
                            let right: Int<'_> = self.expr_to_int(right.clone(), context);
                            return left.ge(&right);
                        }
                        _ => panic!("Expected a integer type for lt, but got {:?}", ltype),
                    }
                }
                _ => panic!("Expected a boolean binop, but got {:?}", op),
            },
            RExpr::Typ {
                op,
                val,
                of,
                type_: _,
            } => {
                let _type = val.get_type();
                match op {
                    TyOp::IsInstanceOf => {
                        return Bool::from_bool(context, _type == *of);
                    }
                    TyOp::IsNotInstanceOf => {
                        return Bool::from_bool(context, _type != *of);
                    }
                }
            }
            RExpr::Uno { op, val, type_: _ } => match op {
                UnOp::Negate => {
                    let val = self.expr_to_bool(val.clone(), context);
                    return val.not();
                }
                UnOp::Negative => panic!("expected a negate, but got a negative of number"),
            },
            RExpr::Con {
                con,
                left,
                right,
                type_: _,
            } => {
                let cond = self.expr_to_bool(con.clone(), context);
                let left = self.expr_to_bool(left.clone(), context);
                let right = self.expr_to_bool(right.clone(), context);
                return cond.ite(&left, &right);
            }
        }
    }

    fn expr_to_int(self: &mut Self, expr: Rc<RExpr>, context: &'a Context) -> Int<'a>
    where
        F: Clone + Fn(&i64, &'a Context) -> Array<'a>,
        G: Clone + Fn(&i64, &'a Context) -> Datatype<'a>,
    {
        match expr.as_ref() {
            RExpr::Lit { lit, type_: _ } => match lit {
                Lit::IntLit { int_value } => Int::from_i64(context, *int_value),
                _ => panic!("Expected an integer literal, but got {:?}", lit),
            },
            RExpr::Sym { id, type_ } => {
                if let Some(ast) = self.imemory.get(id) {
                    return ast.clone();
                } else {
                    let ast = match type_ {
                        RuntimeType::IntRuntimeType => Int::new_const(&context, id.as_str()),
                        _ => panic!("Expected a integer  type, but got {:?}", type_),
                    };
                    self.imemory.insert(id.clone(), ast.clone());
                    return ast;
                }
            }
            RExpr::Ref { .. } => panic!("this one really should not be here"),
            RExpr::Bin {
                op,
                left,
                right,
                type_: _,
            } => match op {
                BinOp::Plus => {
                    let left = self.expr_to_int(left.clone(), context);
                    let right = self.expr_to_int(right.clone(), context);
                    return left + right;
                }
                BinOp::Minus => {
                    let left = self.expr_to_int(left.clone(), context);
                    let right = self.expr_to_int(right.clone(), context);
                    return left - right;
                }
                BinOp::Multiply => {
                    let left = self.expr_to_int(left.clone(), context);
                    let right = self.expr_to_int(right.clone(), context);
                    return left * right;
                }
                BinOp::Divide => {
                    let left = self.expr_to_int(left.clone(), context);
                    let right = self.expr_to_int(right.clone(), context);
                    return left / right;
                }
                BinOp::Modulo => {
                    let left = self.expr_to_int(left.clone(), context);
                    let right = self.expr_to_int(right.clone(), context);
                    return left.modulo(&right);
                }
                _ => panic!("Expected a integer binop, but got {:?}", op),
            },
            RExpr::Typ { .. } => panic!("this one should not be here"),
            RExpr::Uno { op, val, type_: _ } => match op {
                UnOp::Negate => panic!("expected a negative, but got a negate of bool"),
                UnOp::Negative => {
                    let val = self.expr_to_int(val.clone(), context);
                    return Int::from_i64(context, 0) - val;
                }
            },
            RExpr::Con {
                con,
                left,
                right,
                type_: _,
            } => {
                let cond = self.expr_to_bool(con.clone(), context);
                let left = self.expr_to_int(left.clone(), context);
                let right = self.expr_to_int(right.clone(), context);
                return cond.ite(&left, &right);
            }
        }
    }

    fn expr_to_array(self: &mut Self, expr: Rc<RExpr>, context: &'a Context) -> Array<'a>
    where
        F: Clone + Fn(&i64, &'a Context) -> Array<'a>,
        G: Clone + Fn(&i64, &'a Context) -> Datatype<'a>,
    {
        todo!("thhis should def have a different return type")
    }

    fn expr_to_ref(self: &mut Self, expr: Rc<RExpr>, context: &'a Context) -> Datatype<'a>
    where
        F: Clone + Fn(&i64, &'a Context) -> Array<'a>,
        G: Clone + Fn(&i64, &'a Context) -> Datatype<'a>,
    {
        todo!("this should def have a different return type btw, one that acknowledges the possibility of a pointer and null and all that")
    }
}
//Resolved heapvalue
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Debug)]
pub(crate) enum RHeapValue<T> {
    ObjectValue {
        // if you are generated from a symbolic reference, and we need to further generate
        // referecens you keep, we need to make sure those are also generated according to
        // symbolic ref procedures
        sym: bool,
        fields: BTreeMap<Identifier, Rc<T>>,
        type_: Identifier,
    },
    ArrayValue {
        // if you are generated from a symbolic reference, and we need to further generate
        // referecens you keep, we need to make sure those are also generated according to
        // symbolic ref procedures
        sym: bool, 
        // If the size is complex, the inner element vector will be stretched as needed 
        size: Either<usize, Rc<T>>,
        // and if its symbolic, when I stretch I'll fill it with symbolic values 
        elements: Vec<Rc<T>>,
        type_: RuntimeType,
        
    },
    SymPtrIndr{
        // we can have predicates over this symbol
        symbol_ptr: Identifier,
        ptr: SymPtrIndr,
        type_ : RuntimeType,
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Debug)]
pub(crate) enum SymPtrIndr{
    //lazy initialization means we sometimes wait before initing
    Uninitialized,
    Possible{
        nullable: bool,
        possibilities: Vec<(i64, RuntimeType)>
    }

}
 


#[derive(PartialEq, Clone, Debug)]
pub(crate) enum DynamicPointer {
    //return pointer, value to assign
    Ret(u64, Option<Lhs>),
    //Whl entry, after while
    Whl(u64, u64),
    //catch entry, catch exit
    Thr(u64, u64),
}

pub(crate) struct MergeEngine<E, H> {
    _p_e: PhantomData<E>,
    _p_h: PhantomData<H>,
    supply: i64,
    config: Config,
    context: Context,
}

pub type TreeEngine = MergeEngine<Rc<RExpr>, Rc<Tree<Rc<RExpr>, RHeapValue<RExpr>>>>;
pub type SetEngine = MergeEngine<HashSet<Rc<RExpr>>, HashSet<RHeapValue<RExpr>>>; 

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Debug)]
pub(crate) enum Tree<C, T> {
    Leaf(T),
    Node {
        con: C,
        left: Rc<Tree<C, T>>,
        right: Rc<Tree<C, T>>,
    },
}

pub(crate) struct MergeState<E, H>{
    pointer: u64,
    path_length: u64,
    hed_constr: E,
    unq_constr: E,
    stack: Vec<HashMap<Identifier, E>>,
    heap:      HashMap<i64, H>,
    dynamic_cont: Vec<DynamicPointer>,
    split: Option<E>,
    left: bool
}


pub(crate) trait Mergeable: Sized + Clone{
    type MergeOn;
    fn merge(con: Self::MergeOn, left: Self, right: Self) -> Self;
    fn merge_map<I>(con: Self::MergeOn, left: HashMap<I, Self>, right: HashMap<I, Self>)  -> HashMap<I, Self>
        where I:Eq + Hash + Clone;
}
impl Mergeable for Rc<RExpr>{
    type MergeOn = Rc<RExpr>;
    fn merge(con: Self::MergeOn, left: Self, right: Self) -> Self{
        if Rc::ptr_eq(&left, &right) {
            return left;
        }

        let type_ = left.get_type();
        Rc::new(RExpr::Con {
            con,
            left,
            right,
            type_,
        })
    }
    fn merge_map<I>(con: Self::MergeOn, left: HashMap<I, Self>, right: HashMap<I, Self>)  -> HashMap<I, Self> 
        where I:Eq + Hash + Clone
    {
        union_with(
            left, 
            right, 
            |l, r|{Self::merge(con.clone(), l, r)},
            |l| { panic!("you for expressions, this one should be impossible")},
            |r| { panic!("you for expressions, this one should be impossible")}
        )
    }
}
impl Mergeable for HashSet<Rc<RExpr>> where{
    type MergeOn = HashSet<Rc<RExpr>>;

    fn merge(_: Self::MergeOn, left: Self, right: Self) -> Self {
        union(left, right)
    }        
    fn merge_map<I>(con: Self::MergeOn, left: HashMap<I, Self>, right: HashMap<I, Self>)  -> HashMap<I, Self> 
        where I:Eq + Hash + Clone
    {
        union_with(
            left, 
            right, 
            |l, r|{Self::merge(con.clone(), l, r)},
            |l| { panic!("you for expressions, this one should be impossible")},
            |r| { panic!("you for expressions, this one should be impossible")}
        )
    }
}

impl Mergeable for HashSet<RHeapValue<RExpr>> where{
    type MergeOn = HashSet<Rc<RExpr>>;

    fn merge(_: Self::MergeOn, left: Self, right: Self) -> Self {
        union(left, right)
    }        
    fn merge_map<I>(con: Self::MergeOn, left: HashMap<I, Self>, right: HashMap<I, Self>)  -> HashMap<I, Self> 
        where I:Eq + Hash + Clone
    {
        union_with(
            left, 
            right, 
            |l, r|{Self::merge(con.clone(), l, r)},
            |l| { 
                //l must be the result of lazy creation
                //which is annoying. We can extend it with a single fresh value and that should be enough
                l
            },
            |r| { 
                r
            }
        )
    }
}

impl<C, V> Mergeable for Rc<Tree<C, V>> where C: Clone{
    type MergeOn = C;

    fn merge(con: C, left: Self, right: Self) -> Self {
        // we can only hope that this is fast
        if Rc::ptr_eq(&left, &right) {
            return left;
        }

        Rc::new(Tree::Node { con, left, right })
    }  
        fn merge_map<I>(con: Self::MergeOn, left: HashMap<I, Self>, right: HashMap<I, Self>)  -> HashMap<I, Self> 
        where I:Eq + Hash + Clone
    {
    union_with(
            left, 
            right, 
            |l, r|{Self::merge(con.clone(), l, r)},
            |l| { 
                //l must be the result of lazy creation
                //which is annoying. We can extend it with a single fresh value and that should be enough
                l
            },
            |r| { 
                r
            }
        )
    }      
}

pub(crate) trait MergeExpr : Clone{
    fn mk_default(type_: &NonVoidType) -> Self;
    fn mk_lit(lit: Lit, type_: RuntimeType) -> Self;
    fn mk_sym(id: Identifier, type_: RuntimeType ) -> Self ;
    fn mk_null(type_: RuntimeType) -> Self;
    fn mk_ref(ptr: i64, type_: RuntimeType) -> Self;
    fn mk_true() -> Self;
    fn mk_false() -> Self;
    fn mk_bool(b: bool) -> Self { if b {return Self::mk_true();} else {return Self::mk_false();}}
    fn mk_int(i: i64) -> Self;
    fn mk_con(c: Self, l: Self, r: Self,  type_: RuntimeType) -> Self;
    fn mk_bin_op(op: BinOp, l: Self, r: Self, type_: RuntimeType) -> Self;
    fn mk_un_op(op: UnOp, v: Self, type_: RuntimeType) -> Self;
    fn mk_ty_op(op: TyOp, v: Self, target: RuntimeType) -> Self;
    fn and(l: Self, r: Self) -> Self;
    fn or(l: Self, r: Self) -> Self;
    fn eq(l: Self, r: Self) -> Self;
    fn not(l: Self) -> Self;
    fn lt(l: Self, r: Self) -> Self;
    fn le(l: Self, r: Self) -> Self;
    fn gt(l: Self, r: Self) -> Self;
    fn ge(l: Self, r: Self) -> Self;

    fn to_z3_bool<'a, F, G> (builder: &mut Z3Builder<'a, F, G>, expr: Self, context: &'a Context) -> Bool<'a> where
        F: Clone + Fn(&i64, &'a Context) -> Array<'a>,
        G: Clone + Fn(&i64, &'a Context) -> Datatype<'a>; 


}
impl MergeExpr for Rc<RExpr>{

    fn mk_default(type_: &NonVoidType) -> Self {
        match type_{
            NonVoidType::IntType{ .. }       => Self::mk_int(0),
            NonVoidType::BoolType{ .. }      => Self::mk_false(),
            NonVoidType::ReferenceType{ .. } => Self::mk_null(type_.clone().into()),
            NonVoidType::ArrayType { .. }    => Self::mk_null(type_.clone().into()),
            _ => panic!("type {:?} not yet supported", type_),
        }
        
    }
    fn mk_lit(lit: Lit, type_: RuntimeType) -> Self {
        return Rc::new(RExpr::Lit { lit, type_ })
    }
    fn mk_sym(id: Identifier, type_: RuntimeType ) -> Self {
        Rc::new(RExpr::Sym { id, type_ })
    }
    fn mk_null(type_: RuntimeType) -> Self { 
        Rc::new(RExpr::Lit {
            lit: Lit::NullLit,
            type_,
        })
    }
    fn mk_ref(ptr: i64, type_: RuntimeType) -> Self{
        Rc::new(RExpr::Ref { ptr, type_})
    }

    fn mk_true() -> Self {
        Rc::new(RExpr::Lit { lit: Lit::BoolLit { bool_value: true }, type_: RuntimeType::BoolRuntimeType })
    }
    fn mk_false() -> Self {
        Rc::new(RExpr::Lit {
            lit: Lit::BoolLit { bool_value: false },
            type_: RuntimeType::BoolRuntimeType,
        })
    }
    fn mk_int(i: i64) -> Self{
       return Rc::new(RExpr::Lit { lit: Lit::IntLit { int_value: i }, type_: RuntimeType::IntRuntimeType });
    }
    fn mk_con(c: Self, l: Self, r: Self,  type_:RuntimeType) -> Self{ 
        RExpr::evaluate_guard(c, l, r, type_)
    }
    fn mk_bin_op(op: BinOp, l: Self, r: Self, type_:RuntimeType) -> Self {
        RExpr::evaluate_binop(op, l, r, type_)

    }
    fn mk_un_op(op: UnOp, v: Self, type_: RuntimeType) -> Self{
        RExpr::evaluate_unop(op, v)
    }
    fn mk_ty_op(op: TyOp, v: Self, target: RuntimeType) -> Self{
        RExpr::evaluate_tyop(op, v, target)
    }

    fn and(l: Self, r: Self) -> Self {
        RExpr::evaluate_binop(
            BinOp::And,
            l,
            r,
            RuntimeType::BoolRuntimeType,
        )
    }
    fn or(l: Self, r: Self) -> Self {
        RExpr::evaluate_binop(
            BinOp::Or,
            l,
            r,
            RuntimeType::BoolRuntimeType,
        )
    }
    fn eq(l: Self, r: Self) -> Self {
        RExpr::evaluate_binop(BinOp::Equal, l, r, RuntimeType::BoolRuntimeType)
    }
    fn not(l: Self) -> Self {
        RExpr::evaluate_unop(UnOp::Negate, l)
    }
    fn lt(l: Self, r: Self) -> Self {
        RExpr::evaluate_binop(BinOp::LessThan, l, r, RuntimeType::BoolRuntimeType)
    }
    fn le(l: Self, r: Self) -> Self {
        RExpr::evaluate_binop(BinOp::LessThanEqual, l, r, RuntimeType::BoolRuntimeType)
    }
    fn gt(l: Self, r: Self) -> Self {
        RExpr::evaluate_binop(BinOp::GreaterThan, l, r, RuntimeType::BoolRuntimeType)
    }
    fn ge(l: Self, r: Self) -> Self {
        RExpr::evaluate_binop(BinOp::GreaterThanEqual, l, r, RuntimeType::BoolRuntimeType)
    }


    fn to_z3_bool<'a, F, G> (builder: &mut Z3Builder<'a, F, G>, expr: Self, context: &'a Context) -> Bool<'a> where
        F: Clone + Fn(&i64, &'a Context) -> Array<'a>,
        G: Clone + Fn(&i64, &'a Context) -> Datatype<'a>
    {
        builder.expr_to_bool(expr, context)   
    } 

}
impl<E> MergeExpr for HashSet<E> where E: MergeExpr + Eq + Hash + Clone{

    fn mk_default(type_: &NonVoidType) -> Self{ 
        hash_unit(MergeExpr::mk_default(type_))
    }
    fn mk_lit(lit: Lit, type_: RuntimeType) -> Self {
        hash_unit(MergeExpr::mk_lit(lit, type_))
    }

    fn mk_sym(id: Identifier, type_: RuntimeType ) -> Self  {
        hash_unit(MergeExpr::mk_sym(id, type_))
    }

    fn mk_null(type_: RuntimeType) -> Self{
        hash_unit(MergeExpr::mk_null(type_))
    }
    fn mk_ref(ptr: i64, type_: RuntimeType) -> Self{
        hash_unit(MergeExpr::mk_ref(ptr, type_))
    }

    fn mk_true() -> Self {
        return hash_unit(MergeExpr::mk_true());
    }

    fn mk_false() -> Self {
        return hash_unit(MergeExpr::mk_false());
    }
    fn mk_int(i: i64) -> Self{
       return hash_unit(MergeExpr::mk_int(i));
    }

    fn mk_con(c: Self, l: Self, r: Self, type_: RuntimeType) -> Self{ 
        let mut res = HashSet::new();
        for (c, l, r) in iproduct!(c.iter(), l.iter(), r.iter()){
            res.insert(MergeExpr::mk_con(c.clone(), l.clone(), r.clone(), type_.clone()));
        }
        return res; 
    }

    fn mk_bin_op(op: BinOp, l: Self, r: Self, type_: RuntimeType) -> Self {
        let mut res = HashSet::new();
        for (l, r) in iproduct!(l.iter(), r.iter()){
            res.insert(MergeExpr::mk_bin_op(op.clone(), l.clone(), r.clone(), type_.clone()));
        }
        return res; 
    }
    
    fn mk_un_op(op: UnOp, v: Self, type_: RuntimeType) -> Self {
        let mut res = HashSet::new();
        for v in iproduct!(v.iter()){
            res.insert(MergeExpr::mk_un_op(op.clone(), v.clone(), type_.clone()));
        }
        return res; 
    }
    
    fn mk_ty_op(op: TyOp, v: Self, target: RuntimeType) -> Self {
        let mut res = HashSet::new();
        for v in iproduct!(v.iter()){
            res.insert(MergeExpr::mk_ty_op(op.clone(), v.clone(), target.clone()));
        }
        return res; 
    }

    fn and(l: Self, r: Self) -> Self {
        let mut res = HashSet::new();
        for (l, r) in iproduct!(l.iter(), r.iter()){
            res.insert(MergeExpr::and(l.clone(), r.clone()));
        }
        return res; 
    }

    fn or(l: Self, r: Self) -> Self {
        let mut res = HashSet::new();
        for (l, r) in iproduct!(l.iter(), r.iter()){
            res.insert(MergeExpr::or(l.clone(), r.clone()));
        }
        return res; 
    }

    fn eq(l: Self, r: Self) -> Self {
        let mut res = HashSet::new();
        for (l, r) in iproduct!(l.iter(), r.iter()){
            res.insert(MergeExpr::eq(l.clone(), r.clone()));
        }
        return res; 
    }

    fn not(l: Self) -> Self {
        let mut res = HashSet::new();
        for l in l.iter() {
            res.insert(MergeExpr::not(l.clone()));
        }
        return res; 
    }

    fn lt(l: Self, r: Self) -> Self {
        let mut res = HashSet::new();
        for (l, r) in iproduct!(l.iter(), r.iter()){
            res.insert(MergeExpr::lt(l.clone(), r.clone()));
        }
        return res; 
    }

    fn le(l: Self, r: Self) -> Self {
        let mut res = HashSet::new();
        for (l, r) in iproduct!(l.iter(), r.iter()){
            res.insert(MergeExpr::le(l.clone(), r.clone()));
        }
        return res; 
    }

    fn gt(l: Self, r: Self) -> Self {
        let mut res = HashSet::new();
        for (l, r) in iproduct!(l.iter(), r.iter()){
            res.insert(MergeExpr::gt(l.clone(), r.clone()));
        }
        return res; 
    }

    fn ge(l: Self, r: Self) -> Self {
        let mut res = HashSet::new();
        for (l, r) in iproduct!(l.iter(), r.iter()){
            res.insert(MergeExpr::ge(l.clone(), r.clone()));
        }
        return res; 
    }

    fn to_z3_bool<'a, F, G> (builder: &mut Z3Builder<'a, F, G>, expr: Self, context: &'a Context) -> Bool<'a> where
        F: Clone + Fn(&i64, &'a Context) -> Array<'a>,
        G: Clone + Fn(&i64, &'a Context) -> Datatype<'a>
    {
        let expr : Vec<_> = expr.iter().map(|e| { MergeExpr::to_z3_bool(builder, e.clone(), context) }).collect();
        let expr = Bool::or(&context, expr.iter().collect::<Vec<_>>().as_slice());
        return expr;

    }
    

}

pub(crate) trait MergeRef: Sized 
{
    type InnerExpr; 
    fn create_obj(type_: Identifier, classes: HashMap<Identifier, Class>) -> Self;
    fn create_array_of_size(size: Self::InnerExpr,  inner_type: NonVoidType, array_type: RuntimeType) -> Self;
    fn create_sym_ptr_indr(loc: i64, type_: RuntimeType) -> Self;

    fn create_sym_obj<F>(type_: RuntimeType, classes: HashMap<Identifier, Class>, f: F) -> Self 
        where
            F: FnMut(Self) -> i64;
    fn create_sym_array<F>(size: Self::InnerExpr,  inner_type: NonVoidType, array_type: RuntimeType, f: F)
        where
            F: FnMut(Self) -> i64;

    //note the muteable fields and engines below
    //this is because we might need to initialize heap values
    fn update_ref_field_to(
        engine: &mut MergeEngine<Self::InnerExpr, Self>, 
        var: &Self::InnerExpr, 
        field: &Identifier, 
        value: Self::InnerExpr,
        heap: &mut HashMap<i64, Self>
    );  
    
    fn update_ref_index_to(
        engine: &mut MergeEngine<Self::InnerExpr, Self>, 
        var: &Self::InnerExpr, 
        index: &Self::InnerExpr, 
        value: Self::InnerExpr,
        heap: &mut HashMap<i64, Self>
    );

    fn get_ref_field(
        engine: &mut MergeEngine<Self::InnerExpr, Self>, 
        var: &Self::InnerExpr, 
        field: &Identifier, 
        heap: &mut HashMap<i64, Self>
    ) -> Self::InnerExpr;  
    
    fn get_ref_index(
        engine: &mut MergeEngine<Self::InnerExpr, Self>, 
        var: &Self::InnerExpr, 
        index: &Self::InnerExpr, 
        heap: &mut HashMap<i64, Self>
    ) -> Self::InnerExpr;

}

impl MergeRef for Rc<Tree<Rc<RExpr>, RHeapValue<RExpr>>>
{
    type InnerExpr = Rc<RExpr>;
    
    fn create_array_of_size(size: Self::InnerExpr,  inner_type: NonVoidType, array_type: RuntimeType) -> Self
    {
        let size_tree = Tree::<Self::InnerExpr, Self::InnerExpr>::from_cond(size);
        let r = Tree::map(size_tree, &mut |i|{
            match i.as_ref(){
                RExpr::Lit{ 
                    lit: Lit::IntLit { int_value }, ..
                } => {
                    let size = *int_value;
                    let mut elements = vec![];
                    for i in 0..size{
                        let elem = MergeExpr::mk_default(&inner_type);
                        elements.push(elem);
                    }
                    let size = *int_value as usize;
                    let t = RHeapValue::ArrayValue { 
                        size: Either::Left(size),
                        elements, 
                        type_: array_type.clone(),
                        sym: false, 
                    };
                    t
                }
                // I've already turned the conds into the tree I'm mapping over
                RExpr::Con{..} => unreachable!(),
                // a more complex index size, very annoying indeed.
                // when I need to insert or delete, I'll stretch you as needed
                // and whenever I read or write to it, I'll put in a condition
                // the assertions that the size are inserted into the code, or
                // can be inserted into the code, at least. 
                _ => {
                    let elements = vec![];
                    let t = RHeapValue::ArrayValue {
                        size: Either::Right(i),
                        elements, 
                        type_: array_type.clone(),
                        // when we generate elements, if sym is false, we use mk_default, 
                        // but when sym is true we go out of our way to use symbolic values
                        // and possibly symbolic references
                        sym: false
                    };
                    t
                },
            }
        });
        return r;
    }
    
    fn create_obj(type_: Identifier, classes: HashMap<Identifier, Class>) -> Self{
        let Class { members, ..} = classes.get(&type_).unwrap(); 
        let mut fields = BTreeMap::new();
        for member in members{
            match member{
                DeclarationMember::Field { type_, name, info } => {
                    let val = MergeExpr::mk_default(type_);
                    fields.insert(name.clone(), val); 
                },
                _ => {}
            }
        }
        return Rc::new(Tree::Leaf(RHeapValue::ObjectValue { sym: false, fields, type_  }))
    }

    fn create_sym_ptr_indr(loc: i64, type_: RuntimeType) -> Self {
        Rc::new(Tree::Leaf(RHeapValue::SymPtrIndr { 
            symbol_ptr: Identifier::with_unknown_pos(format!("__{}", loc.clone())), 
            ptr: SymPtrIndr::Uninitialized, 
            type_ 
        }))
    }
    
    fn create_sym_obj<F>(type_: RuntimeType, classes: HashMap<Identifier, Class>, f: F) -> Self 
        where
            F: FnMut(Self) -> i64 {
        todo!()
    }
    
    fn create_sym_array<F>(size: Self::InnerExpr,  inner_type: NonVoidType, array_type: RuntimeType, f: F)
        where
            F: FnMut(Self) -> i64 {
        todo!()
    }
    
    fn update_ref_field_to(
        engine: &mut MergeEngine<Self::InnerExpr, Self>, 
        var: &Self::InnerExpr, 
        field: &Identifier, 
        value: Self::InnerExpr,
        heap: &mut HashMap<i64, Self>
    ) {
        todo!()
    }
    
    fn update_ref_index_to(
        engine: &mut MergeEngine<Self::InnerExpr, Self>, 
        var: &Self::InnerExpr, 
        index: &Self::InnerExpr, 
        value: Self::InnerExpr,
        heap: &mut HashMap<i64, Self>
    ) {
        todo!()
    }
    
    fn get_ref_field(
        engine: &mut MergeEngine<Self::InnerExpr, Self>, 
        var: &Self::InnerExpr, 
        field: &Identifier, 
        heap: &mut HashMap<i64, Self>
    ) -> Self::InnerExpr {
        todo!()
    }
    
    fn get_ref_index(
        engine: &mut MergeEngine<Self::InnerExpr, Self>, 
        var: &Self::InnerExpr, 
        index: &Self::InnerExpr, 
        heap: &mut HashMap<i64, Self>
    ) -> Self::InnerExpr {
        todo!()
    }
}
impl MergeRef for HashSet<RHeapValue<RExpr>>{
    type InnerExpr = HashSet<Rc<RExpr>>;

    fn create_array_of_size(size: Self::InnerExpr,  inner_type: NonVoidType, array_type: RuntimeType) -> Self {
        let mut result = HashSet::new();
        for i in size.iter(){
            match i.as_ref(){
                RExpr::Lit{ 
                    lit: Lit::IntLit { int_value }, ..
                } => {
                    let size = *int_value;
                    let mut elements = vec![];
                    for i in 0..size{
                        let elem = MergeExpr::mk_default(&inner_type);
                        elements.push(elem);
                    }
                    let size = *int_value as usize;
                    let t = RHeapValue::ArrayValue { 
                        size: Either::Left(size),
                        elements, 
                        type_: array_type.clone(),
                        sym: false, 
                    };
                    result.insert(t);
                }
                // I've already turned the conds into the tree I'm mapping over
                RExpr::Con { con: _, left, right, type_: _ } => {
                    //annoying, really, but I can at least just flatten this
                    let l = Self::create_array_of_size( hash_unit(left .clone()),  inner_type.clone(), array_type.clone());
                    let r = Self::create_array_of_size( hash_unit(right.clone()), inner_type.clone(), array_type.clone());
                    for l in l {
                        result.insert(l);
                    }
                    for r in r{
                        result.insert(r);
                    }
                },

                _ => {
                    //argh, a math expression, probably
                    let elements = vec![];
                    let t = RHeapValue::ArrayValue {
                        size: Either::Right(i.clone()),
                        elements, 
                        type_: array_type.clone(),
                        sym: false
                    };
                    result.insert(t);
                },
            }
        };
        return result;
    }

    fn create_obj(type_: Identifier, classes: HashMap<Identifier, Class>) -> Self{
        let Class { members, ..} = classes.get(&type_).unwrap(); 
        let mut fields = BTreeMap::new();
        for member in members{
            match member{
                DeclarationMember::Field { type_, name, info } => {
                    let val = MergeExpr::mk_default(type_);
                    fields.insert(name.clone(), val); 
                },
                _ => {}
            }
        }
        return hash_unit(RHeapValue::ObjectValue { sym: false, fields, type_  })
    }

    fn create_sym_ptr_indr(loc: i64, type_: RuntimeType) -> Self {
        hash_unit(RHeapValue::SymPtrIndr { 
            symbol_ptr: Identifier::with_unknown_pos(format!("__{}", loc.clone())), 
            ptr: SymPtrIndr::Uninitialized, 
            type_ 
        })
    }
    
    fn create_sym_obj<F>(type_: RuntimeType, classes: HashMap<Identifier, Class>, f: F) -> Self 
        where
            F: FnMut(Self) -> i64 {
        todo!()
    }
    
    fn create_sym_array<F>(size: Self::InnerExpr,  inner_type: NonVoidType, array_type: RuntimeType, f: F)
        where
            F: FnMut(Self) -> i64 {
        todo!()
    }
    
    fn update_ref_field_to(
        engine: &mut MergeEngine<Self::InnerExpr, Self>, 
        var: &Self::InnerExpr, 
        field: &Identifier, 
        value: Self::InnerExpr,
        heap: &mut HashMap<i64, Self>
    ) {
        todo!()
    }
    
    fn update_ref_index_to(
        engine: &mut MergeEngine<Self::InnerExpr, Self>, 
        var: &Self::InnerExpr, 
        index: &Self::InnerExpr, 
        value: Self::InnerExpr,
        heap: &mut HashMap<i64, Self>
    ) {
        todo!()
    }
    
    fn get_ref_field(
        engine: &mut MergeEngine<Self::InnerExpr, Self>, 
        var: &Self::InnerExpr, 
        field: &Identifier, 
        heap: &mut HashMap<i64, Self>
    ) ->  Self::InnerExpr {
        todo!()
    }
    
    fn get_ref_index(
        engine: &mut MergeEngine<Self::InnerExpr, Self>, 
        var: &Self::InnerExpr, 
        index: &Self::InnerExpr, 
        heap: &mut HashMap<i64, Self>
    ) -> Self::InnerExpr {
        todo!()
    }

}
impl<E, H> MergeState<E,H> where{
    pub(crate) fn path_length(&self) -> u64 {
        return self.path_length;
    }

    pub(crate) fn incr_path(&mut self) -> u64 {
        self.path_length = self.path_length + 1;
        return self.path_length;
    }

    pub(crate) fn get_pointer(&self) -> u64 {
        return self.pointer;
    }

    pub(crate) fn set_pointer(&mut self, ptr: u64) -> u64 {
        self.pointer = ptr;
        return self.pointer;
    }

    pub(crate) fn pop_stack(&mut self) -> () {
        //ugly, why does it need to be like this?
        if self.stack.len() > 1 {
            self.stack.pop();
        } else if self.stack.len() == 1 {
            self.stack[0] = HashMap::new();
        } else {
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

    pub(crate) fn push_dynamic_cf(&mut self, dn: DynamicPointer) -> () {
        self.dynamic_cont.push(dn);
    }

}
impl<E, H> MergeState<E,H> where
    E: MergeExpr + Mergeable<MergeOn = E>,
    H: Mergeable<MergeOn = E> + MergeRef<InnerExpr = E>, 
{
    pub(crate) fn merge_full(&mut self, left: Self, right: Self) -> () {
        let (left, right) = if left.left {
            (left, right)
        } else {
            (right, left)
        };
        let split = self.split.clone().unwrap();
        self.split = None;
        assert_eq!(left.stack.len(), right.stack.len());
        assert_eq!(left.pointer, right.pointer);

        self.pointer = left.pointer;
        self.path_length = std::cmp::min(left.path_length, right.path_length);
        self.dynamic_cont = left.dynamic_cont;

        let lc = left.unq_constr;
        let rc = right.unq_constr;
        self.unq_constr = MergeExpr::and(
            self.unq_constr.clone(),
            MergeExpr::or(lc.clone(),rc.clone())
        );
        self.heap = Mergeable::merge_map(split.clone(), left.heap, right.heap);
        self.stack = izip!(left.stack, right.stack)
            .map(|(l,r)| {Mergeable::merge_map(split.clone(), l, r)})
            .collect();
    }

    pub(crate) fn merge_part(&mut self, left: Self) -> () {
        self.split = None;
        self.pointer = left.pointer;
        self.path_length = left.path_length;
        self.unq_constr = MergeExpr::and(
            self.unq_constr.clone(),
            left.unq_constr,
        );
        self.dynamic_cont = left.dynamic_cont;
        self.heap = left.heap;
        self.stack = left.stack;
    }
}

impl<E, H> MergeEngine<E, H> {
    pub(crate) fn new() -> Self{
        let config = Config::new();
        let context = Context::new(&config);
        return MergeEngine { supply: 0, config, context, _p_e: PhantomData, _p_h: PhantomData };
    }

    pub(crate) fn next_reference_id(&mut self) -> i64 {
        let s = self.supply.clone();
        self.supply = self.supply + 1;
        return s;
    }
    
    
}
impl<E, H> MergeEngine<E, H> where
    E: Mergeable<MergeOn = E> + MergeExpr,
    H: Mergeable<MergeOn = E> + MergeRef<InnerExpr = E> {

    pub(crate) fn make_new_state(
        self: &mut Self,
        pc: u64,
        expr: Rc<Expression>,
        symbols: Vec<(Identifier, Identifier, RuntimeType)>,
        rsymbols: Vec<(Identifier, Identifier, RuntimeType)>,
        classes: HashMap<Identifier, Declaration> //need you for default creation of references 
    ) -> MergeState<E, H> {
        let mut top_frame: HashMap<Identifier, E> = HashMap::new();
        let mut start_heap: HashMap<i64, H> = HashMap::new();
        for (k, s, t) in symbols {
            top_frame.insert(k, MergeExpr::mk_sym(s, t ));
        }        
        for (k, _, t) in rsymbols {
            let s = self.next_reference_id();
            top_frame.insert(k, MergeExpr::mk_ref( s, t.clone()));
            start_heap.insert(
                s, 
                 MergeRef::create_sym_ptr_indr(s, t)
            );
        }


        
        //we'll need you...
        let mut temp = MergeState {
            path_length: 0,
            pointer: pc,
            hed_constr: MergeExpr::mk_true(),
            unq_constr: MergeExpr::mk_true(),
            stack: vec![top_frame],
            heap: start_heap,
            dynamic_cont: vec![],
            split: None,
            left: false,
        };
        let mut stack_frame = temp.stack.last_mut().unwrap();



        let constr = self.eval_with(&mut temp, expr);

        temp.hed_constr = constr;
        return temp;
    }

    pub(crate) fn split_on(
        &mut self,
        state: &mut MergeState<E, H>,
        constr: Rc<Expression>,
    ) -> (MergeState<E, H>, MergeState<E, H>) {
        let new_top: E = MergeExpr::and(
            state.hed_constr.clone(),
            state.unq_constr.clone()
        );
        let constrs: E = self.eval_with(state, constr.clone());
        state.split = Some(constrs.clone());
        let left = MergeState {
            path_length: state.path_length,
            pointer: state.pointer,
            hed_constr: new_top.clone(),
            unq_constr: MergeExpr::mk_true(),
            stack: state.stack.clone(),
            heap: state.heap.clone(),
            dynamic_cont: state.dynamic_cont.clone(),
            split: None,
            left: true,
        };
        let right = MergeState {
            path_length: state.path_length,
            pointer: state.pointer,
            hed_constr: new_top.clone(),
            unq_constr: MergeExpr::mk_true(),
            stack: state.stack.clone(),
            heap: state.heap.clone(),
            dynamic_cont: state.dynamic_cont.clone(),
            split: None,
            left: false,
        };

        return (left, right);
    }

    pub(crate) fn decl_in(
        &mut self,
        state: &mut MergeState<E, H>,
        type_: &NonVoidType,
        var: &Identifier,
        _info: &SourcePos,
    ) -> Result {
        let val = MergeExpr::mk_default(type_);
        state
            .stack
            .last_mut()
            .map(|frame| frame.insert(var.clone(), val));
        return Result::Ok;
    }

    pub(crate) fn eval_with_r(&mut self, state: &mut MergeState<E, H>, rhs: &Rhs) -> E {
        match rhs {
            Rhs::RhsExpression {
                value,
                type_: _,
                info: _,
            } => {
                let vals = self.eval_with(state, value.clone());
                return vals;
            }
            Rhs::RhsField {
                var,
                field,
                type_: _,
                info: _,
            } => {
                let var = self.eval_with(state, var.clone());
                let field = MergeRef::get_ref_field( self, &var, field, &mut state.heap);
                return field;
            }
            Rhs::RhsElem {
                var,
                index,
                type_: _,
                info: _,
            } => {
                let var = self.eval_with(state, var.clone());
                let index = self.eval_with(state, index.clone());
                let elem = MergeRef::get_ref_index(self, &var, &index, &mut state.heap);
                return elem;
            }
            Rhs::RhsArray {
                array_type,
                sizes,
                type_,
                info: _,
            } => {
                assert!(sizes.len() == 1, "Support for only 1D arrays");
                let size = sizes[0].clone();
                let size = self.eval_with(state, size);
                let ptr = self.next_reference_id();
                let ref_: E = E::mk_ref(ptr, type_.clone());
                let heap_value   = H::create_array_of_size(
                    size, 
                    array_type.clone(), 
                    type_.clone(), 
                );
                
                state.heap.insert(ptr, heap_value);
                return ref_;
            }
            Rhs::RhsCast {
                cast_type: _,
                var: _,
                info: _,
            } => todo!("casting"),
            Rhs::RhsCall {
                invocation: _,
                type_: _,
                info: _,
            } => unreachable!("should be handled by the engine"),
        }
    }

    pub(crate) fn eval_with(&self, state: &MergeState<E, H>, expr: Rc<Expression>) -> E {
        match expr.as_ref() {
            Expression::Lit {
                lit,
                type_,
                info: _,
            } => MergeExpr::mk_lit(lit.clone(), type_.clone()),
            Expression::SymbolicVar {
                var,
                type_,
                info: _,
            } => MergeExpr::mk_sym(var.clone(), type_.clone()),
            Expression::Ref {
                ref_,
                type_,
                info: _,
            } => MergeExpr::mk_ref(ref_.clone(), type_.clone()),

            Expression::Var {
                var,
                type_: _,
                info: _,
            } => {
                let frame = state.stack.last().unwrap();
                let var = frame.get(var).unwrap().clone();
                var
            },
            Expression::Conditional {
                guard,
                true_,
                false_,
                type_,
                info: _,
            } => {
                let g = self.eval_with(state, guard.clone());
                let l = self.eval_with(state, true_.clone());
                let r = self.eval_with(state, false_.clone());

                MergeExpr::mk_con(g, l, r, type_.clone())
            }

            Expression::BinOp {
                bin_op,
                lhs,
                rhs,
                type_,
                info: _,
            } => {
                let l = self.eval_with(state, lhs.clone());
                let r = self.eval_with(state, rhs.clone());
                MergeExpr::mk_bin_op(bin_op.clone(), l, r, type_.clone())
            }

            Expression::TypeExpr { texpr } => match texpr {
                TypeExpr::InstanceOf { var, rhs, info: _ } => {
                let val = state.stack.last().unwrap().get(var).unwrap().clone();
                    MergeExpr::mk_ty_op(TyOp::IsInstanceOf, val, rhs.clone())
                }
                TypeExpr::NotInstanceOf { var, rhs, info: _ } => {
                    let val = state.stack.last().unwrap().get(var).unwrap().clone();
                    MergeExpr::mk_ty_op(TyOp::IsNotInstanceOf, val, rhs.clone())
                }
            },

            Expression::UnOp {
                un_op,
                value,
                type_,
                info: _,
            } => {
                let val = self.eval_with(state, value.clone());
                MergeExpr::mk_un_op(un_op.clone(), val, type_.clone())
            }

            //should be doable
            Expression::SizeOf {
                var: _,
                type_: _,
                info: _,
            } => todo!(),

            //shouldn't be present
            Expression::SymbolicRef {
                var: _,
                type_: _,
                info: _,
            } => todo!(),
            Expression::Forall {
                elem: _,
                range: _,
                domain: _,
                formula: _,
                type_: _,
                info: _,
            } => todo!(),
            Expression::Exists {
                elem: _,
                range: _,
                domain: _,
                formula: _,
                type_: _,
                info: _,
            } => todo!(),
        }
    }

    pub(crate) fn assign_expr(&mut self, state: &mut MergeState<E, H>, lhs: &Lhs, rhs: &Rhs) -> bool {
        let rhs = self.eval_with_r(state, rhs);
        self.assign_evaled(state, lhs, rhs);
        return true;
    }


    pub(crate) fn is_feasible(&self, _state: &MergeState<E, H>) -> bool {
        let mut config = Config::new();
        config.set_proof_generation(true);
        let context: Context = Context::new(&config);
        let get_arr = |_: &i64, _: &Context| -> Array { panic!() };
        let get_ref = |_: &i64, _: &Context| -> Datatype { panic!() };
        let mut z3_builder = Z3Builder::new(get_arr, get_ref);
        let solver = Solver::new(&context);
        solver.push();

        let constr = E::and(
            _state.hed_constr.clone(),
            _state.unq_constr.clone(),
        );

        let constr = E::to_z3_bool(&mut z3_builder, constr, &context);

        solver.assert(&constr);
        let result = solver.check();

        solver.pop(1);
        matches!(result, z3::SatResult::Sat)
    }
    pub(crate) fn is_valid_for(&self, state: &MergeState<E, H>, expr: Rc<Expression>) -> bool {
        /*
        if let Some(last_frame) = state.stack.last() {
            for (key, value) in last_frame {
            println!("Key: {:?}, value: {:?}", key, value.clone().as_string());
            }
        } else {
            println!("Stack is empty");
        }
        */
        let mut config = Config::new();
        config.set_proof_generation(true);
        let context: Context = Context::new(&config);
        let get_arr = |_: &i64, _: &Context| -> Array { panic!() };
        let get_ref = |_: &i64, _: &Context| -> Datatype { panic!() };
        let mut z3_builder = Z3Builder::new(get_arr, get_ref);
        let solver = Solver::new(&context);
        solver.push();

        let premise = MergeExpr::and(
            state.hed_constr.clone(),
            state.unq_constr.clone(),
        );
        //println!("premise: {:?}", premise.clone().as_string());
        let premise: Bool<'_> = MergeExpr::to_z3_bool(&mut  z3_builder, premise, &context);

        let conclusion = self.eval_with(state, expr);
        //println!("conclusion: {:?}", conclusion.clone().as_string());
        let conclusion: Bool<'_> = MergeExpr::to_z3_bool(&mut z3_builder, conclusion, &context);

        let constraint = premise.implies(&conclusion);
        let constraint = constraint.not();
        solver.assert(&constraint);
        let result = solver.check();
        solver.pop(1);
        matches!(result, z3::SatResult::Unsat)
    }
    pub(crate) fn add_assumption_to(
        &self,
        state: &mut MergeState<E, H>,
        assumption: Either<Rc<Expression>, TypeExpr>,
    ) {
        let expr = assumption.either(|s| s, |t| Rc::new(Expression::TypeExpr { texpr: t }));
        let cond = self.eval_with(state, expr);
        state.unq_constr = MergeExpr::and(
            state.unq_constr.clone(),
            cond
        );
    }

    pub(crate) fn assign_evaled(&mut self, state: &mut MergeState<E, H>, lhs: &Lhs, value: E) {
        match lhs{
            Lhs::LhsVar { var, type_, info } => {
                state.stack.last_mut().unwrap().insert(var.clone(), value);
            },
            Lhs::LhsField { var, var_type, field, type_, info } => {
                let var = state.stack.last_mut().unwrap().get(var).unwrap();
                MergeRef::update_ref_field_to(self,  var, field, value, &mut state.heap)
            },
            Lhs::LhsElem { var, index, type_, info } => {
                let var = state.stack.last().unwrap().get(var).unwrap();
                let index = self.eval_with(state, index.clone());
                MergeRef::update_ref_index_to(self, var, &index, value, &mut state.heap)
            },
        };
    }

    fn get_field_from_var(&self, var: E, field: Identifier, state: &mut MergeState<E, H>) -> E {
        todo!()
    }

    fn get_elem_from_var(&self, var: E, index: E, state: &mut MergeState<E, H>) -> E {
        todo!()
    }
   
}
impl<C, T> Tree<C, T> {
    fn map<F, R>(tree: Rc<Self>, f: &mut F) -> Rc<Tree<C, R>>
    where
        T: Clone,
        C: Clone,
        F: FnMut(T) -> R,
    {
        match tree.as_ref() {
            Tree::Leaf(value) => Rc::new(Tree::Leaf(f(value.clone()))),
            Tree::Node {
                con: p,
                left: l,
                right: r,
            } => Rc::new(Tree::Node {
                con: p.clone(),
                left: Self::map(l.clone(), f),
                right: Self::map(r.clone(), f),
            }),
        }
    }

    fn flat_map<F, R>(tree: Rc<Self>, f: &mut F) -> Rc<Tree<C, R>>
    where
        T: Clone,
        C: Clone,
        F: FnMut(T) -> Rc<Tree<C, R>>,
    {
        match tree.as_ref() {
            Tree::Leaf(value) => f(value.clone()),
            Tree::Node {
                con: p,
                left: l,
                right: r,
            } => Rc::new(Tree::Node {
                con: p.clone(),
                left: Self::flat_map(l.clone(), f),
                right: Self::flat_map(r.clone(), f),
            }),
        }
    }

    fn to_cond(tree: Rc<Tree<Rc<RExpr>, T>>, mut f: impl FnMut(&T) -> Rc<RExpr> + Clone) -> Rc<RExpr> {
        match tree.as_ref() {
            Tree::Leaf(value) => return f(value),
            Tree::Node { con, left, right } => {
                let left = Self::to_cond(left.clone(), f.clone());
                let right = Self::to_cond(right.clone(), f);
                return Rc::new(RExpr::Con {
                    con: con.clone(),
                    left: left.clone(),
                    right: right.clone(),
                    type_: left.get_type(),
                });
            }
        }
    }
    
    fn from_cond(cond: Rc<RExpr>) -> Rc<Tree<Rc<RExpr>, Rc<RExpr>>>{
        match cond.as_ref(){
            RExpr::Con { con, 
                left, 
                right, 
                type_ 
            } => {
                let left = Self::from_cond(left.clone());
                let right = Self::from_cond(right.clone());
                Rc::new(Tree::Node { 
                    con: con.clone(), 
                    left: left, 
                    right: right 
                })
            }
            _ => Rc::new(Tree::Leaf(cond))
        }
    }
}
