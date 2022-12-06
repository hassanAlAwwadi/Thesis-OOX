use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    ops::{Add, Mul},
    rc::Rc,
};

use z3::{
    ast::Bool,
    ast::{Ast, Int},
    Config, Context, SatResult, Solver,
};

use crate::{
    syntax::{BinOp, Expression, Identifier, Lit, RuntimeType, UnOp},
    typeable::Typeable,
};

pub fn verify(expression: &Expression) -> SatResult {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let solver = Solver::new(&ctx);
    let z3_assertion = expression_to_z3_node(&ctx, expression);
    solver.assert(&z3_assertion);
    solver.check()
}

enum IOP {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

enum IE {
    Value(i64),
    Op(IOP, Box<IE>, Box<IE>),
    Cond(BE, Box<IE>, Box<IE>),
}

enum BOP {
    And,
    Or,
    Implies,
}

enum BE {
    Value(i64),
    Op(BOP, Box<IE>, Box<IE>),
    Cond(Box<BE>, Box<BE>, Box<BE>),
}

#[derive(Clone)]
enum AstNode<'ctx> {
    Bool(Bool<'ctx>),
    Int(Int<'ctx>),
}

impl<'ctx> AstNode<'ctx> {
    fn add(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Int(Int::try_from(self)? + Int::try_from(other)?))
    }

    fn sub(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Int(Int::try_from(self)? - Int::try_from(other)?))
    }

    fn mul(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Int(Int::try_from(self)? * Int::try_from(other)?))
    }

    fn div(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Int(Int::try_from(self)? / Int::try_from(other)?))
    }

    fn _mod(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Int(Int::try_from(self)? % Int::try_from(other)?))
    }

    fn eq(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        match self {
            AstNode::Bool(b) => Ok(AstNode::Bool(b._eq(&Bool::try_from(other)?))),
            AstNode::Int(i) => Ok(AstNode::Bool(i._eq(&Int::try_from(other)?))),
        }
    }

    fn lt(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Bool(
            Int::try_from(self)?.lt(&Int::try_from(other)?),
        ))
    }

    fn gt(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Bool(
            Int::try_from(self)?.gt(&Int::try_from(other)?),
        ))
    }

    fn lte(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Bool(
            Int::try_from(self)?.le(&Int::try_from(other)?),
        ))
    }

    fn gte(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Bool(
            Int::try_from(self)?.ge(&Int::try_from(other)?),
        ))
    }

    fn and(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        let ctx = self.get_ctx();
        Ok(AstNode::Bool(Bool::and(
            &ctx,
            &[&Bool::try_from(self)?, &Bool::try_from(other)?],
        )))
    }

    fn or(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        let ctx = self.get_ctx();
        Ok(AstNode::Bool(Bool::or(
            &ctx,
            &[&Bool::try_from(self)?, &Bool::try_from(other)?],
        )))
    }

    fn implies(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Bool(
            Bool::try_from(self)?.implies(&Bool::try_from(other)?),
        ))
    }

    fn conditional(self, true_: AstNode<'ctx>, false_: AstNode<'ctx>) -> Result<AstNode, ()> {
        let guard = Bool::try_from(self)?;

        guard.ite(&guard, &guard);
        match true_ {
            AstNode::Bool(true_) => Ok(AstNode::Bool(guard.ite(&true_, &Bool::try_from(false_)? ))),
            AstNode::Int(true_) => Ok(AstNode::Int(guard.ite(&true_, &Int::try_from(false_)? ))),
        }
    }

    fn neq(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        match self {
            AstNode::Bool(b) => Ok(AstNode::Bool(!b._eq(&Bool::try_from(other)?))),
            AstNode::Int(i) => Ok(AstNode::Bool(!i._eq(&Int::try_from(other)?))),
        }
    }

    fn negate(self) -> Result<AstNode<'ctx>, ()> {
        Ok(AstNode::Bool(Bool::try_from(self)?.not()))
    }
}

impl<'ctx> AstNode<'ctx> {
    fn get_ctx(&self) -> &'ctx Context {
        match self {
            AstNode::Bool(v) => v.get_ctx(),
            AstNode::Int(v) => v.get_ctx(),
        }
    }
}

impl<'ctx> TryFrom<AstNode<'ctx>> for Bool<'ctx> {
    type Error = ();

    fn try_from(value: AstNode<'ctx>) -> Result<Self, Self::Error> {
        if let AstNode::Bool(v) = value {
            Ok(v)
        } else {
            Err(())
        }
    }
}
impl<'ctx> TryFrom<AstNode<'ctx>> for Int<'ctx> {
    type Error = ();

    fn try_from(value: AstNode<'ctx>) -> Result<Self, Self::Error> {
        if let AstNode::Int(v) = value {
            Ok(v)
        } else {
            Err(())
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
enum NodeEntry<'a> {
    Lit(Lit),
    Var(Cow<'a, Identifier>),
}

impl<'a> NodeEntry<'a> {
    fn var(s: &'a String) -> NodeEntry {
        NodeEntry::Var(Cow::Borrowed(s))
    }
}

// Assuming that expression is a boolean type
fn expression_to_z3_node<'ctx>(ctx: &'ctx Context, expression: &Expression) -> Bool<'ctx> {
    assert!(expression.type_of() == RuntimeType::BoolRuntimeType);

    // dbg!(expression);
    let (symbolic_variables, literals, symbolic_refs) = symbolic_variables(expression);
    assert!(symbolic_refs.len() == 0);
    // dbg!(&literals);
    let id_to_z3_node = symbolic_variables
        .into_iter()
        .map(|(id, type_)| match type_ {
            RuntimeType::BoolRuntimeType => (
                NodeEntry::Var(Cow::Owned(id.clone())),
                AstNode::Bool(Bool::new_const(ctx, id)),
            ),
            RuntimeType::IntRuntimeType => (
                NodeEntry::Var(Cow::Owned(id.clone())),
                AstNode::Int(Int::new_const(ctx, id)),
            ),
            _ => todo!(),
        })
        .chain(literals.into_iter().map(|lit| {
            let z3_node = match &lit {
                Lit::BoolLit { bool_value } => AstNode::Bool(Bool::from_bool(ctx, *bool_value)),
                Lit::IntLit { int_value } => AstNode::Int(Int::from_i64(ctx, *int_value)),
                Lit::NullLit => AstNode::Int(Int::from_i64(ctx, 0)),
                _ => todo!(),
            };
            (NodeEntry::Lit(lit), z3_node)
        }))
        .collect::<HashMap<_, _>>();
    

    fn helper<'ctx>(
        expression: &Expression,
        vars: &HashMap<NodeEntry, AstNode<'ctx>>,
    ) -> AstNode<'ctx> {
        match expression {
            Expression::SymbolicVar { var, type_ } => match type_ {
                RuntimeType::BoolRuntimeType => vars.get(&NodeEntry::var(&var)).unwrap().clone(),
                RuntimeType::IntRuntimeType => vars.get(&NodeEntry::var(&var)).unwrap().clone(),
                _ => todo!(),
            },
            Expression::BinOp {
                bin_op,
                lhs,
                rhs,
                type_,
            } => match bin_op {
                BinOp::And => AstNode::and(helper(lhs, vars), helper(rhs, vars)).unwrap(),
                BinOp::Or => AstNode::or(helper(lhs, vars), helper(rhs, vars)).unwrap(),
                BinOp::Equal => AstNode::eq(helper(lhs, vars), helper(rhs, vars)).unwrap(),
                BinOp::GreaterThan => AstNode::gt(helper(lhs, vars), helper(rhs, vars)).unwrap(),
                BinOp::GreaterThanEqual => {
                    AstNode::gte(helper(lhs, vars), helper(rhs, vars)).unwrap()
                }
                BinOp::LessThan => AstNode::lt(helper(lhs, vars), helper(rhs, vars)).unwrap(),
                BinOp::LessThanEqual => AstNode::lte(helper(lhs, vars), helper(rhs, vars)).unwrap(),

                BinOp::Implies => AstNode::implies(helper(lhs, vars), helper(rhs, vars)).unwrap(),
                BinOp::Minus => AstNode::sub(helper(lhs, vars), helper(rhs, vars)).unwrap(),
                BinOp::Plus => AstNode::add(helper(lhs, vars), helper(rhs, vars)).unwrap(),
                BinOp::Multiply => AstNode::mul(helper(lhs, vars), helper(rhs, vars)).unwrap(),
                BinOp::NotEqual => AstNode::neq(helper(lhs, vars), helper(rhs, vars)).unwrap(),
                BinOp::Divide => AstNode::div(helper(lhs, vars), helper(rhs, vars)).unwrap(),
                BinOp::Modulo => AstNode::_mod(helper(lhs, vars), helper(rhs, vars)).unwrap(),
            },

            Expression::UnOp {
                un_op,
                value,
                type_,
            } => match un_op {
                UnOp::Negative => todo!(),
                UnOp::Negate => AstNode::negate(helper(&value, vars)).unwrap(),
            },
            Expression::Lit { lit, .. } => vars.get(&NodeEntry::Lit(lit.clone())).unwrap().clone(),
            Expression::Ref { ref_, type_ } => {
                // dbg!(*ref_);
                vars.get(&NodeEntry::Lit(Lit::IntLit { int_value: *ref_ })).unwrap().clone()
            },
            Expression::Conditional { guard, true_, false_, type_ } => {
                AstNode::conditional(helper(guard, vars), helper(true_, vars), helper(false_, vars)).unwrap()
            }
            _ => todo!(),
        }
    }

    // generate all possible concrete expressions from symbolic references.
    

    let ast_node = helper(expression, &id_to_z3_node);

    Bool::try_from(ast_node).unwrap()
}

fn symbolic_variables(
    expression: &Expression,
) -> (HashSet<(Identifier, RuntimeType)>, HashSet<Lit>, HashSet<Identifier>) {
    let mut variables = HashSet::new();
    let mut literals = HashSet::new();
    let mut symbolic_refs = HashSet::new();

    fn helper(
        variables: &mut HashSet<(Identifier, RuntimeType)>,
        literals: &mut HashSet<Lit>,
        symbolic_refs: &mut HashSet<Identifier>,
        expression: &Expression,
    ) {
        match expression {
            Expression::BinOp { lhs, rhs, .. } => {
                helper(variables, literals, symbolic_refs, lhs);
                helper(variables, literals, symbolic_refs, rhs);
            }
            Expression::UnOp { value, .. } => {
                helper(variables, literals, symbolic_refs, &value);
            }
            Expression::Conditional { guard, true_, false_, .. } => {
                helper(variables, literals, symbolic_refs, &guard);
                helper(variables, literals, symbolic_refs, &true_);
                helper(variables, literals, symbolic_refs, &false_);
            }
            Expression::SymbolicVar { var, type_ } => {
                variables.insert((var.clone(), type_.clone()));
            }
            Expression::Lit { lit, type_ } => {
                literals.insert(lit.clone());
            } // Lits are handled elsewhere
            Expression::Ref { ref_, type_ } => {
                literals.insert(Lit::IntLit { int_value: *ref_ });
            },
            Expression::SymbolicRef { var, type_ } => {
                symbolic_refs.insert(var.to_owned());
            }
            _ => todo!("Yet to figure out: {:?}", expression),
        }
    }

    helper(&mut variables, &mut literals, &mut symbolic_refs, expression);

    (variables, literals, symbolic_refs)
}

pub fn playground() {
    println!("Hi Z3");
    demorgan();
}

fn demorgan() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let solver = Solver::new(&ctx);

    let p = Bool::new_const(&ctx, "p");
    let q = Bool::new_const(&ctx, "q");

    let demorgan = Bool::or(&ctx, &[&p, &q])._eq(&!(Bool::or(&ctx, &[&!p, &!q])));

    solver.assert(&!demorgan);

    let result = solver.check();

    //dbg!(result);
    //dbg!(solver.get_proof());
    //dbg!(solver.get_model());
}

fn form1() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let solver = Solver::new(&ctx);

    let x = Int::new_const(&ctx, "x");
    let y = Int::new_const(&ctx, "y");

    let _2 = Int::from_i64(&ctx, 2);
    let _7 = Int::from_i64(&ctx, 7);
    let _10 = Int::from_i64(&ctx, 10);

    solver.assert(&x.gt(&_2));
    solver.assert(&y.lt(&_10));

    let assertion = (x + _2 * y)._eq(&_7);

    solver.assert(&!assertion);

    let result = solver.check();
}
