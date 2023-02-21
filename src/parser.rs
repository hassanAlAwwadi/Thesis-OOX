use itertools::Itertools;
use ordered_float::NotNan;
use pom::parser::*;

use std::collections::HashSet;
use std::rc::{Rc, Weak};
use std::str::{self, FromStr};

use std::iter::Extend;

use crate::dsl::{equal, greater_than_equal, less_than, negate, ors, size_of};
use crate::exec::this_str;
use crate::positioned::{SourcePos, WithPosition};
use crate::resolver;
use crate::syntax::*;

use crate::lexer::*;

use self::interface::interface;

mod interface;

pub fn parse<'a>(tokens: &[Token<'a>]) -> Result<CompilationUnit, pom::Error> {
    (program() - end()).parse(tokens).map(|mut c| {
        let c = insert_exceptional_clauses(c);
        c
    })
}

fn program<'a>() -> Parser<'a, Token<'a>, CompilationUnit> {
    declaration().repeat(0..).map(|members| CompilationUnit {
        members: members.into_iter().collect(),
    })
}

fn declaration<'a>() -> Parser<'a, Token<'a>, Declaration> {
    let class = ((keyword("class") * identifier())
        + extends1().opt()
        + implements().opt()
        + (punct("{") * member().repeat(0..) - punct("}")))
    .map(|(((name, extends), implements), members)| {
        Declaration::Class(
            Class {
                name,
                members,
                extends,
                implements: implements.unwrap_or(Vec::new()),
                info: SourcePos::UnknownPosition,
            }
            .into(),
        )
    });

    class | interface().map(Rc::new).map(Declaration::Interface)
}

fn member<'a>() -> Parser<'a, Token<'a>, DeclarationMember> {
    field() | constructor() | method().name("method")

    // empty().map(|_| vec![])
}

fn field<'a>() -> Parser<'a, Token<'a>, DeclarationMember> {
    (nonvoidtype() + identifier() - punct(";"))
        .map(|(type_, name)| DeclarationMember::Field { type_, name, info: SourcePos::UnknownPosition })
}

fn method<'a>() -> Parser<'a, Token<'a>, DeclarationMember> {
    let is_static = keyword("static").opt().map(|x| x.is_some());

    (is_static + type_() + identifier() + parameters() + specification() + body()).map(
        |(((((is_static, return_type), name), params), specification), body)| {
            DeclarationMember::Method(Method {
                is_static,
                return_type,
                name,
                params,
                specification,
                body: body.into(),
                info: SourcePos::UnknownPosition
            }.into())
        },
    )

    // todo!()
}

fn constructor<'a>() -> Parser<'a, Token<'a>, DeclarationMember> {
    let p = identifier() + parameters();
    // let specification = todo!();
    let body = constructor_body();

    (p + specification() + body).map(|(((name, params), specification), body)| {
        DeclarationMember::Constructor(Method {
            return_type: Type { type_: Some(NonVoidType::ReferenceType { identifier: name.clone(), info: name.get_position() }) },
            is_static: false,
            info: name.get_position(),
            name,
            params,
            specification,
            body: body.into(),
        }.into())
    })
}

fn body<'a>() -> Parser<'a, Token<'a>, Statement> {
    (punct("{") * statement().opt() - punct("}")).map(|s| s.unwrap_or(Statement::Skip))
}

fn constructor_body<'a>() -> Parser<'a, Token<'a>, Statement> {
    (punct("{") * statement().opt() - punct("}")).map(|s| s.unwrap_or(Statement::Skip))
}

fn statement<'a>() -> Parser<'a, Token<'a>, Statement> {
    let declaration = (nonvoidtype() + identifier() + (punct(":=") * rhs()).opt() - punct(";"))
        .map(|((type_, var), rhs)| {
            if let Some(rhs) = rhs {
                Statement::Seq {
                    stat1: Box::new(Statement::Declare {
                        info: type_.get_position(),
                        type_,
                        var: var.clone(),
                    }),
                    stat2: Box::new(Statement::Assign {
                        info: rhs.get_position(),
                        lhs: Lhs::LhsVar {
                            info: var.get_position(),
                            var,
                            type_: RuntimeType::UnknownRuntimeType,
                        },
                        rhs,
                    }),
                }
            } else {
                Statement::Declare { info: type_.get_position(), type_, var  }
            }
        });

    // let declaration = (nonvoidtype() + identifier() - punct(";"))
    //     .map(|(type_, var)| Statement::Declare { type_, var });
    let assignment =
        (lhs() - punct(":=") + rhs() - punct(";")).map(|(lhs, rhs)| Statement::Assign { info: lhs.get_position(), lhs, rhs,  });
    let call_ = (invocation() - punct(";")).map(|invocation| Statement::Call { info: invocation.get_position(), invocation });
    let skip = punct(";").map(|_| Statement::Skip);
    let assert = (keyword("assert") + verification_expression() - punct(";"))
        .map(|(assert_token, assertion)| Statement::Assert { assertion, info: assert_token.get_position() });
    let assume = (keyword("assume") + verification_expression() - punct(";"))
        .map(|(assume_token, assumption)| Statement::Assume { assumption, info: assume_token.get_position() });

    let while_ = (keyword("while") * punct("(") * expression() - punct(")")
        + ((punct("{") * call(statement).opt() - punct("}")) | call(statement).map(Some)))
    .map(|(guard, body)| create_while(guard, body));
    let ite = (keyword("if") * punct("(") * expression() - punct(")")
        + ((punct("{") * call(statement) - punct("}")) | call(statement))
        + (keyword("else") * ((punct("{") * call(statement) - punct("}")) | call(statement)))
            .opt())
    .map(|((guard, true_body), false_body)| create_ite(guard, true_body, false_body));
    let continue_ = (keyword("continue") - punct(";")).map(|t| Statement::Continue { info: t.get_position() });
    let break_ = (keyword("break") - punct(";")).map(|t| Statement::Break { info: t.get_position()});
    let return_ = (keyword("return") + expression().opt() - punct(";"))
        .map(|(return_token, expression)| Statement::Return { expression, info: return_token.get_position() });
    let throw = (keyword("throw") * literal() - punct(";")).map(|x| {
        if let Expression::Lit {
            lit: Lit::StringLit { string_value },
            type_,
            info,
        } = x
        {
            Statement::Throw {
                message: string_value,
                info
            }
        } else {
            panic!("Currently only string literals can be thrown as exceptions")
        }
    });
    let try_ = (keyword("try") - punct("{") + call(statement)
        + punct("}") * keyword("catch") * punct("{") * call(statement)
        - punct("}"))
    .map(|((try_token, try_body), catch_body)| Statement::Try {
        try_body: Box::new(try_body),
        catch_body: Box::new(catch_body),
        info: try_token.get_position()
    });
    let block = (punct("{") * call(statement).opt() - punct("}"))
        // .map(|body| Statement::Block {
        //     body: Box::new(body),
        // });
        .map(|body| body.unwrap_or(Statement::Skip));

    // lock, fork & join are left out
    let p_statement = declaration
        | assignment
        | call_
        | skip
        | assert
        | assume
        | while_
        | ite
        | continue_
        | break_
        | return_
        | throw
        | try_
        | block;
    (p_statement + (call(statement)).opt()).map(|(stmt, other_statement)| {
        if let Some(other_statement) = other_statement {
            return match stmt {
                Statement::Seq { stat1, stat2 } => Statement::Seq {
                    stat1,
                    stat2: Box::new(Statement::Seq {
                        stat1: stat2,
                        stat2: Box::new(other_statement),
                    }),
                },
                _ => Statement::Seq {
                    stat1: Box::new(stmt),
                    stat2: Box::new(other_statement),
                },
            };
        }
        return stmt;
    })
}

fn create_ite(guard: Expression, true_body: Statement, false_body: Option<Statement>) -> Statement {
    Statement::Ite {
        guard: guard.clone(),
        true_body: Box::new(Statement::Seq {
            stat1: Box::new(Statement::Assume {
                assumption: guard.clone(),
                info: guard.get_position()
            }),
            stat2: Box::new(true_body),
        }),
        false_body: Box::new(Statement::Seq {
            stat1: Box::new(Statement::Assume {
                assumption: negate(Rc::new(guard.clone())),
                info: guard.get_position()
            }),
            stat2: Box::new(false_body.unwrap_or(Statement::Skip)),
        }),
        info: guard.get_position()
    }
}

fn create_while(guard: Expression, body: Option<Statement>) -> Statement {
    if let Some(body) = body {
        Statement::Seq {
            stat1: Box::new(Statement::While {
                guard: guard.clone(),
                body: Box::new(Statement::Seq {
                    stat1: Box::new(Statement::Assume {
                        assumption: guard.clone(),
                        info: guard.get_position()
                    }),
                    stat2: Box::new(body),
                }
            ),
                info: guard.get_position()
            }),
            stat2: Box::new(Statement::Assume {
                info: guard.get_position(),
                assumption: negate(Rc::new(guard)),
            }),
        }
    } else {
        Statement::Skip
    }
}

fn expression1<'a>() -> Parser<'a, Token<'a>, Expression> {
    verification_expression()
}

fn verification_expression<'a>() -> Parser<'a, Token<'a>, Expression> {
    let forall = (keyword("forall") * identifier() - punct(",") + identifier() - punct(":")
        + identifier()
        - punct(":")
        + call(expression1))
    .map(|(((elem, range), domain), formula)| Expression::Forall {
        info: elem.get_position(),
        elem,
        range,
        domain,
        formula: Box::new(formula),
        type_: RuntimeType::UnknownRuntimeType,
    });
    let exists = (keyword("exists") * identifier() - punct(",") + identifier() - punct(":")
        + identifier()
        - punct(":")
        + call(expression1))
    .map(|(((elem, range), domain), formula)| Expression::Exists {
        info: elem.get_position(),
        elem,
        range,
        domain,
        formula: Box::new(formula),
        type_: RuntimeType::UnknownRuntimeType,
    });

    forall | exists | expression2()
}

fn invocation<'a>() -> Parser<'a, Token<'a>, Invocation> {
    let super_method_invocation = (keyword("super") * punct(".") * identifier() - punct("(")
        + arguments()
        - punct(")"))
    .map(|(rhs, arguments)| Invocation::InvokeSuperMethod {
        info: rhs.get_position(),
        rhs,
        arguments,
        resolved: None,
    });

    let method_invocation = (identifier() - punct(".") + identifier() - punct("(") + arguments()
        - punct(")"))
    .map(|((lhs, rhs), arguments)| Invocation::InvokeMethod {
        info: lhs.get_position(),
        lhs,
        rhs,
        arguments,
        resolved: None,
    });

    let rhs_constructor_call = (keyword("new") * identifier() - punct("(") + arguments()
        - punct(")"))
    .map(|(class_name, arguments)| Invocation::InvokeConstructor {
        info: class_name.get_position(),
        class_name,
        arguments,
        resolved: None,
    });

    let super_constructor_invocation = (keyword("super") - punct("(") + arguments() - punct(")"))
        .map(|(super_token, arguments) | Invocation::InvokeSuperConstructor {
            arguments,
            resolved: None,
            info: super_token.get_position()
        });

    super_method_invocation
        | method_invocation
        | rhs_constructor_call
        | super_constructor_invocation
}

fn arguments<'a>() -> Parser<'a, Token<'a>, Vec<Expression>> {
    list(expression(), punct(","))
}

fn specification<'a>() -> Parser<'a, Token<'a>, Specification> {
    let requires = keyword("requires") * punct("(") * verification_expression() - punct(")");
    let ensures = keyword("ensures") * punct("(") * verification_expression() - punct(")");
    let exceptional = keyword("exceptional") * punct("(") * verification_expression() - punct(")");

    (requires.opt() + ensures.opt() + exceptional.opt()).map(
        |((requires, ensures), exceptional)| Specification {
            requires: requires.map(Rc::new),
            ensures: ensures.map(Rc::new),
            exceptional: exceptional.map(Rc::new),
        },
    )
}

fn expression<'a>() -> Parser<'a, Token<'a>, Expression> {
    expression1()
}

fn expression2<'a>() -> Parser<'a, Token<'a>, Expression> {
    let implies =
        (expression3() + punct("==>") * call(expression2)).map(|(lhs, rhs)| Expression::BinOp {
            info: lhs.get_position(),
            bin_op: BinOp::Implies,
            lhs: Rc::new(lhs),
            rhs: Rc::new(rhs),
            type_: RuntimeType::UnknownRuntimeType,
        });

    implies | expression3()
}

fn expression3<'a>() -> Parser<'a, Token<'a>, Expression> {
    // let and =
    //     (expression4() + punct("&&") * call(expression3)).map(|(lhs, rhs)| Expression::BinOp {
    //         bin_op: BinOp::And,
    //         lhs: Rc::new(lhs),
    //         rhs: Rc::new(rhs),
    //         type_: RuntimeType::UnknownRuntimeType,
    //     });
    // let or =
    //     (expression4() + punct("||") * call(expression3)).map(|(lhs, rhs)| Expression::BinOp {
    //         bin_op: BinOp::Or,
    //         lhs: Rc::new(lhs),
    //         rhs: Rc::new(rhs),
    //         type_: RuntimeType::UnknownRuntimeType,
    //     });

    let and = punct("&&").map(|_| BinOp::And);
    let or = punct("||").map(|_| BinOp::Or);

    (expression4() + ((and | or) + call(expression3)).opt()).map(|(lhs, rhs)| {
        if let Some((bin_op, rhs)) = rhs {
            Expression::BinOp {
                info: lhs.get_position(),
                bin_op,
                lhs: Rc::new(lhs),
                rhs: Rc::new(rhs),
                type_: RuntimeType::UnknownRuntimeType,
            }
        } else {
            lhs
        }
    })

    // and | or | expression4()
}

fn expression4<'a>() -> Parser<'a, Token<'a>, Expression> {
    // let eq =
    //     (expression5() + punct("==") * call(expression4)).map(|(lhs, rhs)| Expression::BinOp {
    //         bin_op: BinOp::Equal,
    //         lhs: Rc::new(lhs),
    //         rhs: Rc::new(rhs),
    //         type_: RuntimeType::UnknownRuntimeType,
    //     });

    // let neq =
    //     (expression5() + punct("!=") * call(expression4)).map(|(lhs, rhs)| Expression::BinOp {
    //         bin_op: BinOp::NotEqual,
    //         lhs: Rc::new(lhs),
    //         rhs: Rc::new(rhs),
    //         type_: RuntimeType::UnknownRuntimeType,
    //     });

    let eq = punct("==").map(|_| BinOp::Equal);
    let neq = punct("!=").map(|_| BinOp::NotEqual);

    (expression5() + ((eq | neq) + call(expression4)).opt()).map(|(lhs, rhs)| {
        if let Some((bin_op, rhs)) = rhs {
            Expression::BinOp {
                info: lhs.get_position(),
                bin_op,
                lhs: Rc::new(lhs),
                rhs: Rc::new(rhs),
                type_: RuntimeType::UnknownRuntimeType,
            }
        } else {
            lhs
        }
    })

    // eq | neq | expression5()
}

fn expression5<'a>() -> Parser<'a, Token<'a>, Expression> {
    // let lt = (expression6() + punct("<") * call(expression5)).map(|(lhs, rhs)| Expression::BinOp {
    //     bin_op: BinOp::LessThan,
    //     lhs: Rc::new(lhs),
    //     rhs: Rc::new(rhs),
    //     type_: RuntimeType::UnknownRuntimeType,
    // });
    // let gt = (expression6() + punct(">") * call(expression5)).map(|(lhs, rhs)| Expression::BinOp {
    //     bin_op: BinOp::GreaterThan,
    //     lhs: Rc::new(lhs),
    //     rhs: Rc::new(rhs),
    //     type_: RuntimeType::UnknownRuntimeType,
    // });
    // let lte =
    //     (expression6() + punct("<=") * call(expression5)).map(|(lhs, rhs)| Expression::BinOp {
    //         bin_op: BinOp::LessThanEqual,
    //         lhs: Rc::new(lhs),
    //         rhs: Rc::new(rhs),
    //         type_: RuntimeType::UnknownRuntimeType,
    //     });
    // let gte =
    //     (expression6() + punct(">=") * call(expression5)).map(|(lhs, rhs)| Expression::BinOp {
    //         bin_op: BinOp::GreaterThanEqual,
    //         lhs: Rc::new(lhs),
    //         rhs: Rc::new(rhs),
    //         type_: RuntimeType::UnknownRuntimeType,
    //     });

    let gte = punct(">=").map(|_| BinOp::GreaterThanEqual);
    let lte = punct("<=").map(|_| BinOp::LessThanEqual);
    let lt = punct("<").map(|_| BinOp::LessThan);
    let gt = punct(">").map(|_| BinOp::GreaterThan);

    (expression6() + ((gte | lte | lt | gt) + call(expression5)).opt()).map(|(lhs, rhs)| {
        if let Some((bin_op, rhs)) = rhs {
            Expression::BinOp {
                info: lhs.get_position(),
                bin_op,
                lhs: Rc::new(lhs),
                rhs: Rc::new(rhs),
                type_: RuntimeType::UnknownRuntimeType,
            }
        } else {
            lhs
        }
    })

    // gte | lte | lt | gt | expression6()
}

fn expression6<'a>() -> Parser<'a, Token<'a>, Expression> {
    let plus = punct("+").map(|_| BinOp::Plus);
    let minus = punct("-").map(|_| BinOp::Minus);

    (expression7() + ((plus | minus) + call(expression6)).opt()).map(|(lhs, rhs)| {
        if let Some((bin_op, rhs)) = rhs {
            Expression::BinOp {
                info: lhs.get_position(),
                bin_op,
                lhs: Rc::new(lhs),
                rhs: Rc::new(rhs),
                type_: RuntimeType::UnknownRuntimeType,
            }
        } else {
            lhs
        }
    })
}

fn expression7<'a>() -> Parser<'a, Token<'a>, Expression> {
    let multiply = punct("*").map(|_| BinOp::Multiply);
    let divide = punct("/").map(|_| BinOp::Divide);
    let modulo = punct("%").map(|_| BinOp::Modulo);

    (expression8() + ((multiply | divide | modulo) + call(expression7)).opt()).map(|(lhs, rhs)| {
        if let Some((bin_op, rhs)) = rhs {
            Expression::BinOp {
                info: lhs.get_position(),
                bin_op,
                lhs: Rc::new(lhs),
                rhs: Rc::new(rhs),
                type_: RuntimeType::UnknownRuntimeType,
            }
        } else {
            lhs
        }
    })

    // multiply | divide | modulo | expression8()
}

fn expression8<'a>() -> Parser<'a, Token<'a>, Expression> {
    let negative = (punct("-") * call(expression8)).map(|value| Expression::UnOp {
        info: value.get_position(),
        un_op: UnOp::Negative,
        value: Rc::new(value),
        type_: RuntimeType::UnknownRuntimeType,
    });

    let negate = (punct("!") * call(expression8)).map(|value| Expression::UnOp {
        info: value.get_position(),
        un_op: UnOp::Negate,
        value: Rc::new(value),
        type_: RuntimeType::UnknownRuntimeType,
    });

    negative | negate | expression9()
}

fn expression9<'a>() -> Parser<'a, Token<'a>, Expression> {
    let var = identifier().map(|var| Expression::Var {
        info: var.get_position(),
        var,
        type_: RuntimeType::UnknownRuntimeType,
    });
    let sizeof = (punct("#") * identifier()).map(|var| Expression::SizeOf {
        info: var.get_position(),
        var,
        type_: RuntimeType::UnknownRuntimeType,
    });
    let parenthesized = punct("(") * call(expression) - punct(")");

    var | sizeof | parenthesized | literal()
}

fn lhs<'a>() -> Parser<'a, Token<'a>, Lhs> {
    let lhs_var = identifier().map(|var| Lhs::LhsVar {
        info: var.get_position(),
        var,
        type_: RuntimeType::UnknownRuntimeType,
    });

    let lhs_field = (identifier() - punct(".") + identifier()).map(|(var, field)| Lhs::LhsField {
        info: var.get_position(),
        var,
        var_type: RuntimeType::UnknownRuntimeType,
        field,
        type_: RuntimeType::UnknownRuntimeType,
    });

    let lhs_elem =
        (identifier() - punct("[") + expression() - punct("]")).map(|(var, index)| Lhs::LhsElem {
            info: var.get_position(),
            var,
            index: Rc::new(index),
            type_: RuntimeType::UnknownRuntimeType,
        });

    lhs_elem | lhs_field | lhs_var
}

fn rhs<'a>() -> Parser<'a, Token<'a>, Rhs> {
    let rhs_expression = expression().map(|value| Rhs::RhsExpression {
        info: value.get_position(),
        value,
        type_: RuntimeType::UnknownRuntimeType,
    });

    let rhs_field = (expression() - punct(".") + identifier()).map(|(var, field)| Rhs::RhsField {
        info: var.get_position(),
        var,
        field,
        type_: RuntimeType::UnknownRuntimeType,
    });
    let rhs_call = invocation().map(|invocation| Rhs::RhsCall {
        info: invocation.get_position(),
        invocation,
        type_: RuntimeType::UnknownRuntimeType,
    });
    let rhs_elem =
        (expression() - punct("[") + expression() - punct("]")).map(|(var, index)| Rhs::RhsElem {
            info: var.get_position(),
            var,
            index,
            type_: RuntimeType::UnknownRuntimeType,
        });
    let rhs_array = (keyword("new") * (classtype() | primitivetype())
        + (punct("[") * (integer() | expression()) - punct("]")).repeat(1..))
    .map(|(array_type, sizes)| Rhs::RhsArray {
        info: array_type.get_position(),
        array_type,
        sizes,
        type_: RuntimeType::UnknownRuntimeType,
    });

    rhs_call | rhs_field | rhs_elem | rhs_expression | rhs_array
}

fn parameters<'a>() -> Parser<'a, Token<'a>, Vec<Parameter>> {
    let parameter = (nonvoidtype() + identifier()).map(|(type_, name)| Parameter { info: type_.get_position(), name, type_,  });

    // can it be empty?
    punct("(") * (list(parameter, punct(",")) | empty().map(|_| Vec::new())) - punct(")")
}

fn type_<'a>() -> Parser<'a, Token<'a>, Type> {
    keyword("void").map(|_| Type { type_: None })
        | nonvoidtype().map(|type_| Type { type_: Some(type_) })
}

fn nonvoidtype<'a>() -> Parser<'a, Token<'a>, NonVoidType> {
    referencetype() | primitivetype()
}

fn primitivetype<'a>() -> Parser<'a, Token<'a>, NonVoidType> {
    keyword("uint").map(|t| NonVoidType::UIntType { info: t.get_position() })
        | keyword("int").map(|t| NonVoidType::IntType{ info: t.get_position()})
        | keyword("bool").map(|t| NonVoidType::BoolType{ info: t.get_position()})
        | keyword("float").map(|t| NonVoidType::FloatType{ info: t.get_position()})
        | keyword("char").map(|t| NonVoidType::CharType{ info: t.get_position()})
}

fn referencetype<'a>() -> Parser<'a, Token<'a>, NonVoidType> {
    let arraytype = ((classtype() | primitivetype()) + (punct("[") + punct("]")).repeat(1..)).map(
        |(inner_type, n)| {
            assert!(n.len() == 1, "only allow 1D arrays for now");
            NonVoidType::ArrayType {
                info: inner_type.get_position(),
                inner_type: Box::new(inner_type),
            }
        },
    );
    arraytype | classtype()
}

fn classtype<'a>() -> Parser<'a, Token<'a>, NonVoidType> {
    identifier().map(|identifier| NonVoidType::ReferenceType { info: identifier.get_position(), identifier })
        | keyword("string").map(|t| NonVoidType::StringType { info: t.get_position() })
}

fn integer<'a>() -> Parser<'a, Token<'a>, Expression> {
    take(1)
        .convert(|tokens| {
            let token = tokens[0]; // only one taken
            if let Token::Literal(s, pos) = token {
                return Ok((s, pos));
            }
            Err(())
        })
        .convert(|(i, pos)| i64::from_str(i).map(|int_value| (int_value, pos)))
        .map(|(int_value, pos)| Expression::Lit {
            lit: Lit::IntLit { int_value },
            type_: RuntimeType::IntRuntimeType,
            info: pos,
        })
}

fn literal<'a>() -> Parser<'a, Token<'a>, Expression> {
    take(1)
        .convert(|tokens| {
            let token = tokens[0]; // only one taken
            if let Token::Literal(s, pos) = token {
                return Ok((s, pos));
            }
            Err(())
        })
        .map(|(value, pos)| Expression::Lit {
            lit: match value {
                "null" => Lit::NullLit,
                "true" => Lit::BoolLit { bool_value: true },
                "false" => Lit::BoolLit { bool_value: false },
                s => {
                    if s.starts_with("'") && s.ends_with("'") {
                        let char_value = s.chars().nth(1).unwrap();
                        Lit::CharLit { char_value }
                    } else if s.starts_with("\"") && s.ends_with("\"") {
                        let string_value = &s[1..s.len() - 1];
                        Lit::StringLit {
                            string_value: string_value.to_string(),
                        }
                    } else {
                        if let Ok(int_value) = i64::from_str(s) {
                            Lit::IntLit { int_value }
                        } else if let Ok(float_value) = f64::from_str(s) {
                            Lit::FloatLit {
                                float_value: NotNan::new(float_value).unwrap(),
                            }
                        } else {
                            unreachable!()
                        }
                    }
                }
                _ => unreachable!(),
            },
            type_: RuntimeType::ANYRuntimeType,
            info: pos
        })
}

fn identifier<'a>() -> Parser<'a, Token<'a>, Identifier> {
    take(1).convert(|tokens| {
        let token = tokens[0]; // only one taken
        if let Token::Identifier(s, pos) = token {
            Ok(Identifier::with_pos(s.to_string(), pos))
        } else {
            Err(())
        }
    })
}

fn extends1<'a>() -> Parser<'a, Token<'a>, Identifier> {
    keyword("extends") * identifier()
}

fn extends_many<'a>() -> Parser<'a, Token<'a>, Vec<Identifier>> {
    keyword("extends") * list(identifier(), punct(","))
}

fn implements<'a>() -> Parser<'a, Token<'a>, Vec<Identifier>> {
    keyword("implements") * list(identifier(), punct(","))
}

fn punct<'a>(kw: &'a str) -> Parser<'a, Token<'a>, Token> {
    is_a(move |t| match t { Token::Punctuator(p, _) => p == kw, _ => false} )
    
}

fn keyword<'a>(kw: &'a str) -> Parser<'a, Token<'a>, Token> {
    is_a(move |t| match t { Token::Keyword(p, _) => p == kw, _ => false} )
}

fn exceptional_assignment(lhs: &Lhs, rhs: &Rhs, class_names: &[Identifier]) -> HashSet<Expression> {
    let mut lhs = exceptional_lhs(lhs);
    lhs.extend(exceptional_rhs(rhs, class_names).into_iter());
    lhs
}

fn exceptional_lhs(lhs: &Lhs) -> HashSet<Expression> {
    match lhs {
        Lhs::LhsVar { .. } => HashSet::new(),
        Lhs::LhsField { var, var_type, .. } => HashSet::from([equal(
            Expression::Var {
                info: var.get_position(),
                var: var.clone(),
                type_: var_type.clone(),
            },
            Expression::NULL,
        )]),
        Lhs::LhsElem { var, index, type_, info } => union(
            HashSet::from([
                equal(
                    Expression::Var {
                        info: var.get_position(),
                        var: var.clone(),
                        type_: type_.clone(),
                    },
                    Expression::NULL,
                ),
                ors([
                    greater_than_equal(index.clone(), size_of(var.clone())),
                    less_than(index.clone(), Expression::int(0)),
                ]),
            ]),
            exceptional_expression(index),
        ),
    }
}

fn exceptional_rhs(rhs: &Rhs, class_names: &[Identifier]) -> HashSet<Expression> {
    match rhs {
        Rhs::RhsExpression { value, .. } => exceptional_expression(value),
        Rhs::RhsField { var, .. } => HashSet::from([equal(var.clone(), Expression::NULL)]),
        Rhs::RhsElem { var, index, .. } => {
            let var_name = if let Expression::Var {
                var: var_name,
                type_: _,
                info
            } = var
            {
                var_name
            } else {
                panic!("expected variable in rhs elem, found: {:?}", var)
            };

            union(
                HashSet::from([
                    equal(var.clone(), Expression::NULL),
                    ors([
                        greater_than_equal(index.clone(), size_of(var_name.clone())),
                        less_than(index.clone(), Expression::int(0)),
                    ]),
                ]),
                exceptional_expression(index),
            )
        }
        Rhs::RhsCall { invocation, type_, .. } => exceptional_invocation(invocation, class_names),
        Rhs::RhsArray {
            array_type,
            sizes,
            type_, ..
        } => HashSet::new(),
    }
}

fn exceptional_expression(expression: &Expression) -> HashSet<Expression> {
    match expression {
        Expression::BinOp {
            bin_op: BinOp::Divide | BinOp::Modulo,
            rhs,
            ..
        } => {
            // Check for divide or modulo by 0
            HashSet::from([equal(
                rhs.clone(),
                Expression::Lit {
                    lit: Lit::IntLit { int_value: 0 },
                    type_: RuntimeType::IntRuntimeType,
                    info: expression.get_position()
                },
            )])
        }
        Expression::BinOp { lhs, rhs, .. } => {
            union(exceptional_expression(lhs), exceptional_expression(rhs))
        }
        Expression::UnOp { value, .. } => exceptional_expression(value),
        Expression::Conditional {
            guard,
            true_,
            false_,
            ..
        } => union(
            union(exceptional_expression(guard), exceptional_expression(true_)),
            exceptional_expression(false_),
        ),
        Expression::Forall {
            elem,
            range,
            domain,
            formula,
            type_,
            info
        } => todo!(),
        Expression::Exists {
            elem,
            range,
            domain,
            formula,
            type_,
            info
        } => todo!(),
        Expression::SizeOf { var, type_, info } => todo!(),
        _ => HashSet::new(),
    }
}

fn exceptional_invocation(invocation: &Invocation, class_names: &[Identifier]) -> HashSet<Expression> {
    match invocation {
        Invocation::InvokeMethod { lhs, arguments, .. } => {
            exceptional_invoke_method(lhs, arguments, class_names)
        }
        Invocation::InvokeSuperMethod { arguments, .. } => {
            // "super" is not actually an object at runtime, but "this" is
            exceptional_invoke_method(&this_str(), arguments, class_names)
        }
        Invocation::InvokeConstructor { .. } => HashSet::new(),
        Invocation::InvokeSuperConstructor { .. } => HashSet::new(),
    }
}
fn exceptional_invoke_method(
    lhs: &Identifier,
    arguments: &Vec<Expression>,
    class_names: &[Identifier],
) -> HashSet<Expression> {
    let exceptional_args: HashSet<_> = arguments
        .into_iter()
        .flat_map(|arg| exceptional_expression(arg).into_iter())
        .collect();

    let is_static_method = class_names.iter().any(|s| s.as_str() == *lhs);

    if !is_static_method {
        let exp = ors(std::iter::once(equal(
            Expression::Var {
                var: lhs.to_owned(),
                type_: RuntimeType::REFRuntimeType,
                info: lhs.get_position(),
            },
            Expression::NULL,
        ))
        .chain(exceptional_args.into_iter()));
        HashSet::from([exp])
    } else {
        exceptional_args
    }
}

fn create_exceptional_ites(conditions: HashSet<Expression>, body: Statement, pos: SourcePos) -> Statement {
    if conditions.len() == 0 {
        return body;
    }
    let cond = ors(conditions);
    // In the original OOX, a nested ITE is made if there are multiple exception conditions, not sure why so I will do it like this for now.
    create_ite(
        cond,
        Statement::Throw {
            message: "exception".into(),
            info: pos
        },
        Some(body),
    )
}

// Inserts if-then-else statements for OOX statements that may throw nullpointer exceptions.
//
// for example:
// `int x := o.y;`
//
// becomes:
//
// `if (o == null) {
//  throw "exception";
// } else {
//  int x := o.y;
// }`
pub fn insert_exceptional_clauses(mut compilation_unit: CompilationUnit) -> CompilationUnit {
    // used to check if an invocation is a static call.
    let decl_names = compilation_unit
        .members
        .iter()
        .map(|declaration| match declaration {
            Declaration::Class(class) => class.name.clone(),
            Declaration::Interface(interface) => interface.name.clone(),
        })
        .collect_vec();

    for decl in compilation_unit.members.iter_mut() {
        match decl {
            Declaration::Class(class) => {
                let class = Rc::get_mut(class).expect(
                    "Rc<Class> are not referred to yet when exception clauses are inserted",
                );
                class.members =
                    insert_exceptional_clauses_class_members(&class.members, &decl_names);
            }
            Declaration::Interface(interface) => {
                let interface = Rc::get_mut(interface).expect(
                    "Rc<Interface> are not referred to yet when exception clauses are inserted",
                );
                interface.members =
                    insert_exceptional_clauses_interface_members(&interface.members, &decl_names);
            }
        }
    }

    fn insert_exceptional_clauses_class_members(
        members: &Vec<DeclarationMember>,
        decl_names: &[Identifier],
    ) -> Vec<DeclarationMember> {
        members
            .iter()
            .map(|dcl| match dcl.clone() {
                DeclarationMember::Method(method) => {
                    let new_body =
                        insert_exceptional_in_body(method.body.borrow().clone(), &decl_names);
                    *method.body.borrow_mut() = new_body;
                    DeclarationMember::Method(method)
                }
                DeclarationMember::Constructor(method) => {
                    let new_body =
                        insert_exceptional_in_body(method.body.borrow().clone(), &decl_names);
                        *method.body.borrow_mut() = new_body;
                    DeclarationMember::Constructor(method)
                }
                field @ DeclarationMember::Field { .. } => field,
            })
            .collect_vec()
    }

    fn insert_exceptional_clauses_interface_members(
        members: &Vec<InterfaceMember>,
        decl_names: &[Identifier],
    ) -> Vec<InterfaceMember> {
        members
            .iter()
            .map(|dcl| match dcl {
                InterfaceMember::DefaultMethod(method) => {
                    let new_body = insert_exceptional_in_body(method.body.borrow().clone(), &decl_names);
                    *method.body.borrow_mut() = new_body;
                    InterfaceMember::DefaultMethod(method.clone())
                },
                InterfaceMember::AbstractMethod(_) => dcl.clone(),
            })
            .collect()
    }

    fn insert_exceptional_in_body(statement: Statement, class_names: &[Identifier]) -> Statement {
        match statement {
            Statement::Assign { lhs, rhs, info } => {
                let conditions = exceptional_assignment(&lhs, &rhs, class_names);

                create_exceptional_ites(conditions, Statement::Assign { lhs, rhs, info }, info )
            }
            Statement::Call { invocation, info } => {
                let conditions = exceptional_invocation(&invocation, class_names);

                create_exceptional_ites(conditions, Statement::Call { invocation, info }, info)
            }
            Statement::Ite {
                guard,
                true_body,
                false_body,
                info
            } => Statement::Ite {
                guard,
                true_body: Box::new(insert_exceptional_in_body(*true_body, class_names)),
                false_body: Box::new(insert_exceptional_in_body(*false_body, class_names)),
                info
            },

            Statement::Seq { stat1, stat2 } => Statement::Seq {
                stat1: Box::new(insert_exceptional_in_body(*stat1, class_names,)),
                stat2: Box::new(insert_exceptional_in_body(*stat2, class_names)),
            },
            Statement::While { guard, body, info } => Statement::While {
                guard,
                body: Box::new(insert_exceptional_in_body(*body, class_names)),
                info
            },
            Statement::Try {
                try_body,
                catch_body,
                info
            } => Statement::Try {
                try_body: Box::new(insert_exceptional_in_body(*try_body, class_names)),
                catch_body: Box::new(insert_exceptional_in_body(*catch_body, class_names)),
                info
            },

            Statement::Block { body } => Statement::Block {
                body: Box::new(insert_exceptional_in_body(*body, class_names)),
            },
            Statement::Return { expression, info } => {
                if let Some(e) = expression {
                    create_exceptional_ites(
                        exceptional_expression(&e),
                        Statement::Return {
                            expression: Some(e),
                            info
                        },
                        info
                    )
                } else {
                    Statement::Return { expression: None, info }
                }
            }

            statement => statement,
        }
    }
    compilation_unit
}

fn union<T>(mut set1: HashSet<T>, set2: HashSet<T>) -> HashSet<T>
where
    HashSet<T>: Extend<T>,
{
    set1.extend(set2);
    set1
}

#[test]
fn class_with_constructor() {
    let file_content = include_str!("../examples/class_with_constructor.oox");

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    //dbg!(as_ref);
    let c = program().parse(&as_ref).unwrap(); // should not panic;
                                               //dbg!(c);
}

#[test]
fn test_statement() {
    let file_content = "int p; p := 0;";

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    //dbg!(as_ref);
    let c = (statement() - end()).parse(&as_ref).unwrap(); // should not panic;
                                                           //dbg!(c);
}

#[test]
fn class_with_methods() {
    let file_content = include_str!("../examples/class_with_methods.oox");

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    // //dbg!(as_ref);
    let c = (program() - end()).parse(&as_ref);
    // //dbg!(&c);
    c.unwrap(); // should not panic;

    // //dbg!(c);
    // assert!(false);
}

#[test]
fn bsort_test() {
    let file_content = include_str!("../examples/bsort.oox");

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    // //dbg!(as_ref);
    let c = (program() - end()).parse(&as_ref);
    // //dbg!(&c);
    c.unwrap(); // should not panic;

    // //dbg!(c);
    // assert!(false);
}

#[test]
fn this_dot() {
    let file_content = "p := this.value;";

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    //dbg!(as_ref);
    let c = (statement() - end()).parse(&as_ref).unwrap(); // should not panic;
                                                           //dbg!(c);
}

#[test]
fn ite() {
    let file_content = "
    int v := this.value ;
    if(x==v) { return true; }
    else {
        Node n := this.next ;
        bool b := n.member(x) ;
        return b ;
    }";
    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    //dbg!(&as_ref);
    let c = (statement() - end()).parse(&as_ref).unwrap(); // should not panic;
                                                           //dbg!(c);
}

#[test]
fn boolean() {
    let file_content = "true";
    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    //dbg!(as_ref);
    let c = (expression() - end()).parse(&as_ref).unwrap(); // should not panic;
                                                            //dbg!(c);
}

#[test]
fn test_statement2() {
    let file_content = "Node n; n := this.next ;
    bool b;
    b := n.member(x) ;
    return b;";
    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    //dbg!(as_ref);
    let c = (statement() - end()).parse(&as_ref).unwrap(); // should not panic;
                                                           //dbg!(c);
}

#[test]
fn forall() {
    let file_content = "(forall x, i : a : i<k ==> (forall x, i : a : i<k ==> true))";
    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    // //dbg!(as_ref);
    let c = (expression() - end()).parse(&as_ref).unwrap(); // should not panic;
                                                            //dbg!(c);
}
#[test]
fn absolute_simplest() {
    let file_content = include_str!("../examples/absolute_simplest.oox");

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    // //dbg!(as_ref);
    let c = (program() - end()).parse(&as_ref);
    // //dbg!(&c);
    c.unwrap(); // should not panic;
}

#[test]
fn parsing_empty_function() {
    let file_content = "class X { static int fib(int n) {  } }";

    let tokens = tokens(&file_content);
    let as_ref = tokens.as_slice();
    // //dbg!(as_ref);
    let c = (program() - end()).parse(&as_ref);
    // //dbg!(&c);
    c.unwrap(); // should not panic;
}

fn pite<'a>() -> Parser<'a, Token<'a>, Statement> {
    (keyword("if") * punct("(") * expression() - punct(")")
    + ((punct("{") * call(statement) - punct("}")) | call(statement))
    + (keyword("else") * ((punct("{") * call(statement) - punct("}")) | call(statement)))
        .opt())
        .map(|((guard, true_body), false_body)| create_ite(guard, true_body, false_body))

}

#[test]
fn parsing_else_if() {
    let file_content = "if (n == 0) return 0;
    else if (n == 1) return 1;
    else {
        ;
    }
    ";


    let tokens = tokens(&file_content);
    let as_ref = tokens.as_slice();
    // //dbg!(as_ref);
    // let c = (pite() - end()).parse(&as_ref);
    let c = (statement() - end()).parse(&as_ref);
    // //dbg!(&c);
    c.unwrap(); // should not panic;
}

#[test]
fn parsing_while() {
    let file_content = "while (t<n) {
        int newborn := mature ;
        mature := total ;
        total := total ;
       }";

    let tokens = tokens(&file_content);
    //dbg!(&tokens);
    let as_ref = tokens.as_slice();
    // //dbg!(as_ref);
    let c = (statement() - end()).parse(&as_ref);
    // //dbg!(&c);
    c.unwrap(); // should not panic;
}

#[test]
fn parsing_fib() {
    let file_content = std::fs::read_to_string("./examples/psv/fib.oox").unwrap();

    let tokens = tokens(&file_content);
    let as_ref = tokens.as_slice();
    // //dbg!(as_ref);
    let c = (program() - end()).parse(&as_ref);
    // //dbg!(&c);
    c.unwrap(); // should not panic;
}

#[test]
fn parse_capital_variable() {
    let file_content = "int N := 10;";

    let tokens = tokens(&file_content);
    dbg!(&tokens);
    let as_ref = tokens.as_slice();
    // //dbg!(as_ref);
    let c = (statement() - end()).parse(&as_ref);
    // //dbg!(&c);
    c.unwrap(); // should not panic;
}

#[test]
fn parse_while_loop() {
    let file_content = "
    while (i<N)
        i := i+1 ;";

    let tokens = tokens(&file_content);
    dbg!(&tokens);
    let as_ref = tokens.as_slice();
    // //dbg!(as_ref);
    let c = (statement() - end()).parse(&as_ref);
    // //dbg!(&c);
    c.unwrap(); // should not panic;
}

#[test]
fn parsing_linked_list() {
    let file_content = std::fs::read_to_string("./examples/intLinkedList.oox").unwrap();

    let tokens = tokens(&file_content);
    let as_ref = tokens.as_slice();
    // //dbg!(as_ref);
    let c = (program() - end()).parse(&as_ref);
    // //dbg!(&c);
    c.unwrap(); // should not panic;
}

#[test]
fn parsing_exceptions() {
    let file_content = std::fs::read_to_string("./examples/exceptions.oox").unwrap();

    let tokens = tokens(&file_content);
    let as_ref = tokens.as_slice();
    dbg!(as_ref);
    let c = parse(&as_ref).unwrap();
    dbg!(&c);
}

#[test]
fn parse_array_elem_assign() {
    let file_content = "a[0] := 1;";

    let tokens = tokens(&file_content);
    dbg!(&tokens);
    let as_ref = tokens.as_slice();
    // //dbg!(as_ref);
    let c = (statement() - end()).parse(&as_ref);
    // //dbg!(&c);
    c.unwrap(); // should not panic;
}

#[test]
fn parsing_array1() {
    let file_content = std::fs::read_to_string("./examples/array/array1.oox").unwrap();

    let tokens = tokens(&file_content);
    let as_ref = tokens.as_slice();
    dbg!(as_ref);
    let c = parse(&as_ref).unwrap();
    dbg!(&c);
}
