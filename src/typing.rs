/// Type analysis of an OOX abstract syntax tree
///
/// The input is an abstract syntax tree (CompilationUnit) with (most) of its types set to UnknownType.
/// If the program is type correct, each type in the syntax tree (without a type) is mapped to itself with a type.
/// If type incorrect, a TypeError is returned instead.
use std::{collections::HashMap, rc::Rc};

use crate::{
    error::{self, unification_error},
    symbolic_table::SymbolicTable,
    syntax::*,
    typeable::Typeable,
};

type TypeError = String;

/// Checks whether typeable A is of type B, returning an error when this is not the case.
/// And an empty Ok result otherwise.
fn matches_type<A, B>(type1: A, type2: B) -> Result<(), TypeError>
where
    A: Typeable,
    B: Typeable,
{
    if !type1.is_of_type(type2.type_of()) {
        return Err(error::unification_error(type1.type_of(), type2.type_of()));
    }
    Ok(())
}

#[derive(Clone)]
struct TypeEnvironment {
    env: HashMap<Identifier, RuntimeType>,
}
impl TypeEnvironment {
    fn declare_var(&mut self, var: Identifier, type_: RuntimeType) -> Result<(), TypeError> {
        if let Some((previously_defined, _)) = self.env.get_key_value(&var) {
            return Err(error::shadowing(var, previously_defined.to_string()));
        }
        self.env.insert(var, type_);
        Ok(())
    }

    fn get_var_type(&self, var: &Identifier) -> Result<RuntimeType, TypeError> {
        self.env.get(var).cloned().ok_or(error::undeclared_var(var))
    }
}
fn type_compilation_unit(
    compilation_unit: CompilationUnit,
    env: TypeEnvironment,
    st: &SymbolicTable,
) -> Result<CompilationUnit, TypeError> {
    let members = compilation_unit
        .members
        .into_iter()
        .map(|member| type_declaration(member, st))
        .collect::<Result<_, _>>()?;

    Ok(CompilationUnit { members })
}

fn type_declaration(
    declaration: Declaration,
    st: &SymbolicTable,
) -> Result<Declaration, TypeError> {
    match &declaration {
        Declaration::Class(class) => {
            let mut class = class.as_ref().clone(); // bad clone
            let mut env = TypeEnvironment {
                env: HashMap::new(),
            };
            let members = class
                .members
                .into_iter()
                .map(move |member| {
                    type_member(declaration.clone(), member.as_ref().clone(), &mut env, st).map(Rc::new)
                })
                .collect::<Result<Vec<_>, _>>()?;
            class.members = members;
            Ok(Declaration::Class(class.into()))
        }
        Declaration::Interface(_) => todo!(),
    }
}

fn type_member(
    declaration: Declaration,
    declaration_member: DeclarationMember,
    env: &mut TypeEnvironment,
    st: &SymbolicTable,
) -> Result<DeclarationMember, TypeError> {
    use DeclarationMember as DM;
    match &declaration_member {
        field @ DM::Field { .. } => Ok(field.clone()),
        DM::Constructor {
            specification,
            body,
            ..
        }
        | DM::Method {
            is_static: false,
            specification,
            body,
            ..
        } => {
            let mut env = env.clone();
            env.declare_var(
                "this".to_owned(),
                RuntimeType::ReferenceRuntimeType {
                    type_: declaration.name().clone(),
                },
            )?;
            type_specification(&declaration_member, specification.clone(), &mut env)?;

            let body = type_statement(body.clone(), &declaration_member, &mut env, st)?;

            let mut declaration_member = declaration_member;
            declaration_member.set_body(body);
            Ok(declaration_member)
        }
        DM::Method {
            is_static: true,
            body,
            ..
        } => {
            let mut env = env.clone();
            let body = type_statement(body.clone(), &declaration_member, &mut env, st)?;

            let mut declaration_member = declaration_member;
            declaration_member.set_body(body);
            Ok(declaration_member)
        }
    }
}

fn type_specification(
    declaration_member: &DeclarationMember,
    mut specification: Specification,
    env: &mut TypeEnvironment,
) -> Result<Specification, TypeError> {
    if let Some(requires) = specification.requires.clone() {
        let requires = type_expression(requires, env)?;
        matches_type(&requires, RuntimeType::BoolRuntimeType)?;
        specification.requires = Some(Rc::new(requires));
    }

    if let Some(ensures) = specification.ensures.clone() {
        let method_type = declaration_member.type_of();
        if !method_type.is_of_type(RuntimeType::VoidRuntimeType) {
            let mut env = env.clone();

            env.declare_var("retval".to_owned(), method_type)?;
            let ensures = type_expression(ensures, &mut env)?;
            matches_type(&ensures, RuntimeType::BoolRuntimeType)?;
            specification.requires = Some(Rc::new(ensures));
        }
    }

    if let Some(exceptional) = specification.exceptional.clone() {
        let exceptional = type_expression(exceptional, env)?;
        matches_type(&exceptional, RuntimeType::BoolRuntimeType)?;
        specification.exceptional = Some(Rc::new(exceptional));
    }

    Ok(specification)
}

fn optional_type_expression(
    expression: Option<Rc<Expression>>,
    env: &mut TypeEnvironment,
) -> Result<Option<Rc<Expression>>, TypeError> {
    if let Some(expr) = expression {
        type_expression(expr, env).map(Rc::new).map(Some)
    } else {
        Ok(None)
    }
}

fn type_statement(
    statement: Statement,
    current_method: &DeclarationMember,
    env: &mut TypeEnvironment,
    st: &SymbolicTable,
) -> Result<Statement, TypeError> {
    match statement {
        Statement::Declare { type_, var } => {
            env.declare_var(var.clone(), type_.type_of())?;
            Ok(Statement::Declare { type_, var })
        }
        Statement::Assign { lhs, rhs } => {
            let lhs = type_lhs(lhs, env, st)?;
            let rhs = type_rhs(rhs, env, st)?;

            matches_type(&lhs, rhs.clone())?;
            Ok(Statement::Assign { lhs, rhs })
        }
        Statement::Call { invocation } => {
            let invocation = type_invocation(invocation, env, st)?;
            Ok(Statement::Call { invocation })
        }
        Statement::Skip => Ok(Statement::Skip),
        Statement::Assert { assertion } => {
            let assertion = type_expression(assertion.into(), env)?;
            Ok(Statement::Assert { assertion })
        }
        Statement::Assume { assumption } => {
            let assumption = type_expression(assumption.into(), env)?;
            Ok(Statement::Assume { assumption })
        }
        Statement::While { guard, body } => {
            let guard = type_expression(guard.into(), env)?;
            matches_type(&guard, RuntimeType::BoolRuntimeType)?;
            let mut env = env.clone();
            let body = type_statement(*body, current_method, &mut env, &st)?;
            Ok(Statement::While {
                guard,
                body: Box::new(body),
            })
        }
        Statement::Ite {
            guard,
            true_body,
            false_body,
        } => {
            let guard = type_expression(guard.into(), env)?;
            matches_type(&guard, RuntimeType::BoolRuntimeType)?;
            let mut env = env.clone();
            let true_body = type_statement(*true_body, current_method, &mut env, &st)?;
            let false_body = type_statement(*false_body, current_method, &mut env, &st)?;

            Ok(Statement::Ite {
                guard,
                true_body: true_body.into(),
                false_body: false_body.into(),
            })
        }
        Statement::Continue => Ok(Statement::Continue),
        Statement::Break => Ok(Statement::Break),
        Statement::Return { expression } => match (current_method, expression) {
            (DeclarationMember::Constructor { .. }, Some(return_value)) => {
                Err(error::unexpected_return_value(&return_value))
            }
            (DeclarationMember::Constructor { .. }, None) => {
                let this_type = current_method.type_of();
                let this = "this".to_owned();
                let this_var = Expression::Var {
                    var: this,
                    type_: this_type,
                };
                Ok(Statement::Return {
                    expression: Some(this_var),
                })
            }
            (_, Some(return_value)) => {
                matches_type(&return_value, current_method.type_of())?;
                Ok(Statement::Return {
                    expression: Some(return_value),
                })
            }
            (_, None) => {
                if !current_method.is_of_type(RuntimeType::VoidRuntimeType) {
                    Err(error::expected_return_value_error(current_method.type_of()))
                } else {
                    Ok(Statement::Return { expression: None })
                }
            }
        },
        Statement::Throw { message } => Ok(Statement::Throw { message }),
        Statement::Try {
            try_body,
            catch_body,
        } => {
            let mut try_env = env.clone();
            let try_body = type_statement(*try_body, current_method, &mut try_env, st)?;
            let mut catch_env = env.clone();
            let catch_body = type_statement(*catch_body, current_method, &mut catch_env, st)?;
            Ok(Statement::Try {
                try_body: Box::new(try_body),
                catch_body: Box::new(catch_body),
            })
        }
        Statement::Block { body } => {
            let body = type_statement(*body, current_method, env, st)?;
            Ok(Statement::Block {
                body: Box::new(body),
            })
        }
        Statement::Seq { stat1, stat2 } => {
            let stat1 = type_statement(*stat1, current_method, env, st)?;
            let stat2 = type_statement(*stat2, current_method, env, st)?;
            Ok(Statement::Seq {
                stat1: Box::new(stat1),
                stat2: Box::new(stat2),
            })
        }
    }
}

fn type_lhs(lhs: Lhs, env: &mut TypeEnvironment, st: &SymbolicTable) -> Result<Lhs, TypeError> {
    match lhs {
        Lhs::LhsVar { var, type_ } => {
            let type_ = env.get_var_type(&var)?;
            Ok(Lhs::LhsVar { var, type_ })
        }
        Lhs::LhsField {
            var,
            var_type,
            field,
            type_,
        } => {
            let var_type = env.get_var_type(&var)?;
            let class_name = var_type.get_reference_type().ok_or_else(|| {
                error::unification_error(RuntimeType::REFRuntimeType, var_type.clone())
            })?;

            // something's going to need to be changed here due to inheritance of fields
            if let Some((_, field_type)) = st.lookup_field(&class_name, &field) {
                Ok(Lhs::LhsField {
                    var,
                    var_type,
                    field: field,
                    type_: field_type.type_of(),
                })
            } else {
                Err(error::unresolved_field_error(&class_name, &field))
            }
        }
        Lhs::LhsElem { var, index, .. } => {
            let type_ = env.get_var_type(&var)?;
            let inner_type = type_.get_inner_array_type().ok_or_else(|| {
                error::unification_error(RuntimeType::ARRAYRuntimeType, type_.clone())
            })?;
            let index = type_expression(index, env)?;
            matches_type(&index, RuntimeType::IntRuntimeType)?;
            Ok(Lhs::LhsElem {
                var,
                index: index.into(),
                type_: inner_type,
            })
        }
    }
}

fn type_rhs(rhs: Rhs, env: &mut TypeEnvironment, st: &SymbolicTable) -> Result<Rhs, TypeError> {
    match rhs {
        Rhs::RhsExpression { value, .. } => {
            let expr = type_expression(value.into(), env)?;
            let type_ = expr.type_of();
            Ok(Rhs::RhsExpression { value: expr, type_ })
        }
        Rhs::RhsField { var, field, .. } => {
            let var = type_expression(var.into(), env)?;
            let var_type = var.type_of();
            let class_name = var_type.as_reference_type().ok_or_else(|| {
                error::unification_error(RuntimeType::REFRuntimeType, var_type.clone())
            })?;
            if let Some((_, field_type)) = st.lookup_field(class_name, &field) {
                Ok(Rhs::RhsField {
                    var,
                    field,
                    type_: field_type.type_of(),
                })
            } else {
                Err(error::unresolved_field_error(class_name, &field))
            }
        }
        Rhs::RhsElem { var, index, .. } => {
            let var = type_expression(var.into(), env)?;
            let var_type = var.type_of();
            let inner_type = var_type.get_inner_array_type().ok_or_else(|| {
                error::unification_error(RuntimeType::ARRAYRuntimeType, var_type.clone())
            })?;
            let index = type_expression(index.into(), env)?;
            matches_type(&index, RuntimeType::IntRuntimeType)?;
            Ok(Rhs::RhsElem {
                var,
                index,
                type_: inner_type,
            })
        }
        Rhs::RhsCall { invocation, .. } => {
            let invocation = type_invocation(invocation, env, st)?;
            let type_ = invocation.type_of();

            Ok(Rhs::RhsCall { invocation, type_ })
        }
        Rhs::RhsArray {
            array_type, sizes, ..
        } => {
            let sizes = sizes
                .into_iter()
                .map(|size_expr| type_expression(size_expr.into(), env))
                .collect::<Result<Vec<_>, _>>()?;

            for size in sizes.iter() {
                matches_type(size, RuntimeType::IntRuntimeType)?;
            }
            let type_ =
                sizes
                    .iter()
                    .fold(array_type.type_of(), |a, _| RuntimeType::ArrayRuntimeType {
                        inner_type: Box::new(a),
                    });

            Ok(Rhs::RhsArray {
                array_type,
                sizes,
                type_,
            })
        }
    }
}

// TODO: merge with resolver
fn type_invocation(
    invocation: Invocation,
    env: &mut TypeEnvironment,
    st: &SymbolicTable,
) -> Result<Invocation, TypeError> {
    match invocation {
        Invocation::InvokeMethod {
            lhs,
            rhs,
            arguments,
            resolved,
        } => {
            let arguments = arguments
                .into_iter()
                .map(|arg| type_expression(arg.into(), env))
                .collect::<Result<Vec<_>, _>>()?;
            // lhs could also be a static class name
            let lhs_type = env.get_var_type(&lhs).ok();
            // if lhs is non-static, add the class type to the argument list, due to the implicit 'this' argument.
            let argument_types = {
                let mut arg_types = lhs_type
                    .as_ref()
                    .map_or(Vec::new(), |lhs_type| vec![lhs_type.clone()]);
                arg_types.extend(arguments.iter().map(Typeable::type_of));
                arg_types
            };

            let class_name = lhs_type
                .as_ref()
                .and_then(|t| t.as_reference_type())
                .unwrap_or(&lhs);

            Ok(Invocation::InvokeMethod {
                lhs,
                rhs,
                arguments,
                resolved,
            })
        }
        Invocation::InvokeSuperMethod {
            rhs,
            arguments,
            resolved,
        } => Ok(Invocation::InvokeSuperMethod {
            rhs,
            arguments,
            resolved,
        }),
        Invocation::InvokeConstructor {
            class_name,
            arguments,
            resolved,
        } => Ok(Invocation::InvokeConstructor {
            class_name,
            arguments,
            resolved,
        }),
        Invocation::InvokeSuperConstructor {
            arguments,
            resolved,
        } => Ok(Invocation::InvokeSuperConstructor {
            arguments,
            resolved,
        }),
    }
}

/// Verifies the types in given expression, returning an expression with the types set correctly
/// or an error if the expression is type incorrect.
fn type_expression(
    expression: Rc<Expression>,
    env: &mut TypeEnvironment,
) -> Result<Expression, TypeError> {
    let expr = match expression.as_ref().clone() {
        Expression::Forall {
            elem,
            range,
            domain,
            formula,
            ..
        } => {
            let array = env.get_var_type(&domain)?;
            let inner_type = array
                .get_inner_array_type()
                .ok_or(unification_error(RuntimeType::ARRAYRuntimeType, array))?;
            let mut env = env.clone();

            env.declare_var(elem.clone(), inner_type)?;
            env.declare_var(range.clone(), RuntimeType::IntRuntimeType)?;
            let formula = type_expression(formula.into(), &mut env)?;
            matches_type(&formula, RuntimeType::BoolRuntimeType)?;

            Expression::Forall {
                type_: RuntimeType::BoolRuntimeType,
                elem,
                range,
                domain,
                formula: Box::new(formula),
            }
        }
        Expression::Exists {
            elem,
            range,
            domain,
            formula,
            type_,
        } => {
            let array = env.get_var_type(&domain)?;
            let inner_type = array
                .get_inner_array_type()
                .ok_or(unification_error(RuntimeType::ARRAYRuntimeType, array))?;
            let mut env = env.clone();

            env.declare_var(elem.clone(), inner_type)?;
            env.declare_var(range.clone(), RuntimeType::IntRuntimeType)?;
            let formula = type_expression(formula.into(), &mut env)?;
            matches_type(&formula, RuntimeType::BoolRuntimeType)?;

            Expression::Exists {
                type_: RuntimeType::BoolRuntimeType,
                elem,
                range,
                domain,
                formula: Box::new(formula),
            }
        }
        Expression::BinOp {
            bin_op, lhs, rhs, ..
        } => {
            let lhs = type_expression(lhs, env)?;
            let rhs = type_expression(rhs, env)?;
            let type_ = type_binop(bin_op, &lhs, &rhs)?;
            Expression::BinOp {
                bin_op,
                lhs: lhs.into(),
                rhs: rhs.into(),
                type_,
            }
        }
        Expression::UnOp {
            un_op,
            value,
            type_,
        } => {
            let value = type_expression(value, env)?;
            let type_ = match un_op {
                UnOp::Negative => {
                    matches_type(&value, RuntimeType::NUMRuntimeType)?;
                    value.type_of()
                }
                UnOp::Negate => {
                    matches_type(&value, RuntimeType::BoolRuntimeType)?;
                    RuntimeType::BoolRuntimeType
                }
            };
            Expression::UnOp {
                un_op,
                value: value.into(),
                type_,
            }
        }
        Expression::Var { var, .. } => {
            let type_ = env.get_var_type(&var)?;
            Expression::Var { var, type_ }
        }
        Expression::SymbolicVar { .. } => unreachable!("Symbolic variable in analysis phase"),
        Expression::Lit { lit, .. } => {
            let type_ = lit.type_of();
            Expression::Lit { lit, type_ }
        }
        Expression::SizeOf { var, .. } => Expression::SizeOf {
            var,
            type_: RuntimeType::IntRuntimeType,
        },
        Expression::Ref { ref_, .. } => Expression::Ref {
            ref_,
            type_: RuntimeType::REFRuntimeType,
        },
        Expression::SymbolicRef { .. } => unreachable!("Symbolic object in analysis phase"),
        Expression::Conditional { .. } => unreachable!("Ite in analysis phase"),
    };
    Ok(expr)
}

/// Assumes exp1 and exp2 already have been typechecked.
fn type_binop(
    binop: BinOp,
    exp1: &Expression,
    exp2: &Expression,
) -> Result<RuntimeType, TypeError> {
    use BinOp::*;
    if [Implies, And, Or].contains(&binop) {
        matches_type(exp1, RuntimeType::BoolRuntimeType)?;
        matches_type(exp2, RuntimeType::BoolRuntimeType)?;
        Ok(RuntimeType::BoolRuntimeType)
    } else if [Equal, NotEqual].contains(&binop) {
        matches_type(exp1, RuntimeType::BoolRuntimeType)?;
        matches_type(exp2, RuntimeType::BoolRuntimeType)?;
        Ok(RuntimeType::BoolRuntimeType)
    } else if [LessThan, LessThanEqual, GreaterThan, GreaterThanEqual].contains(&binop) {
        matches_type(exp1, RuntimeType::NUMRuntimeType)?;
        matches_type(exp2, RuntimeType::NUMRuntimeType)?;
        Ok(RuntimeType::BoolRuntimeType)
    } else if [Plus, Minus, Multiply, Divide, Modulo].contains(&binop) {
        let type_of = exp1.type_of();
        matches_type(exp1, RuntimeType::NUMRuntimeType)?;
        matches_type(exp2, RuntimeType::NUMRuntimeType)?;
        Ok(type_of)
    } else {
        unreachable!("missing case in type_binop")
    }
}
