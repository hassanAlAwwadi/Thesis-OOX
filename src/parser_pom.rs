use nom::Slice;
use ordered_float::NotNan;
use pom::parser::*;

use std::cell::RefCell;
use std::collections::btree_set::Union;
use std::collections::{HashMap, HashSet};
use std::ops::Deref;
use std::rc::Rc;
use std::str::{self, FromStr};

use crate::dsl::{equal, negate, ors};
use crate::resolver;
use crate::syntax::*;

use crate::lexer::*;

pub fn parse<'a>(tokens: &[Token<'a>]) -> Result<CompilationUnit, pom::Error> {
    (program() - end()).parse(tokens).map(|mut c| {
        resolver::set_resolvers(&mut c); // set the resolvers in Invocations
        c
    })
}

fn program<'a>() -> Parser<'a, Token<'a>, CompilationUnit> {
    class()
        .repeat(0..)
        .map(|members| CompilationUnit { members })
}

fn class<'a>() -> Parser<'a, Token<'a>, Declaration> {
    let identifier_and_members =
        (keyword("class") * identifier()) + (punct("{") * member().repeat(0..) - punct("}"));
    identifier_and_members.map(|(name, members)| Declaration::Class { name, members })
}

fn member<'a>() -> Parser<'a, Token<'a>, DeclarationMember> {
    field() | constructor() | method().name("method")

    // empty().map(|_| vec![])
}

fn field<'a>() -> Parser<'a, Token<'a>, DeclarationMember> {
    (nonvoidtype() + identifier() - punct(";"))
        .map(|(type_, name)| DeclarationMember::Field { type_, name })
}

fn method<'a>() -> Parser<'a, Token<'a>, DeclarationMember> {
    let is_static = keyword("static").opt().map(|x| x.is_some());

    let parameters = punct("(") * parameters() - punct(")");

    (is_static + type_() + identifier() + parameters + specification() + body()).map(
        |(((((is_static, return_type), name), params), specification), body)| {
            DeclarationMember::Method {
                is_static,
                return_type,
                name,
                params,
                specification,
                body,
            }
        },
    )

    // todo!()
}

fn constructor<'a>() -> Parser<'a, Token<'a>, DeclarationMember> {
    let p = identifier() - punct("(") + parameters() - punct(")");
    // let specification = todo!();
    let body = punct("{") * statement() - punct("}");

    (p + specification() + body).map(|(((name, params), specification), body)| {
        DeclarationMember::Constructor {
            name,
            params,
            specification,
            body,
        }
    })
}

fn body<'a>() -> Parser<'a, Token<'a>, Statement> {
    (punct("{") * statement().opt() - punct("}")).map(|s| s.unwrap_or(Statement::Skip))
}

fn statement<'a>() -> Parser<'a, Token<'a>, Statement> {
    let declaration = (nonvoidtype() + identifier() + (punct(":=") * rhs()).opt() - punct(";"))
        .map(|((type_, var), rhs)| {
            if let Some(rhs) = rhs {
                Statement::Seq {
                    stat1: Box::new(Statement::Declare {
                        type_,
                        var: var.clone(),
                    }),
                    stat2: Box::new(Statement::Assign {
                        lhs: Lhs::LhsVar {
                            var,
                            type_: RuntimeType::UnknownRuntimeType,
                        },
                        rhs,
                    }),
                }
            } else {
                Statement::Declare { type_, var }
            }
        });

    // let declaration = (nonvoidtype() + identifier() - punct(";"))
    //     .map(|(type_, var)| Statement::Declare { type_, var });
    let assignment =
        (lhs() - punct(":=") + rhs() - punct(";")).map(|(lhs, rhs)| Statement::Assign { lhs, rhs });
    let call_ = (invocation() - punct(";")).map(|invocation| Statement::Call { invocation });
    let skip = punct(";").map(|_| Statement::Skip);
    let assert = (keyword("assert") * verification_expression() - punct(";"))
        .map(|assertion| Statement::Assert { assertion });
    let assume = (keyword("assume") * verification_expression() - punct(";"))
        .map(|assumption| Statement::Assume { assumption });

    let while_ = (keyword("while") * punct("(") * expression() - punct(")")
        + ((punct("{") * call(statement).opt() - punct("}")) | call(statement).map(Some)))
    .map(|(guard, body)| create_while(guard, body));
    let ite = (keyword("if") * punct("(") * expression() - punct(")")
        + ((punct("{") * call(statement) - punct("}")) | call(statement))
        + (keyword("else") * ((punct("{") * call(statement) - punct("}")) | call(statement)))
            .opt())
    .map(|((guard, true_body), false_body)| create_ite(guard, true_body, false_body));
    let continue_ = (keyword("continue") * punct(";")).map(|_| Statement::Continue);
    let break_ = (keyword("break") * punct(";")).map(|_| Statement::Break);
    let return_ = (keyword("return") * expression().opt() - punct(";"))
        .map(|expression| Statement::Return { expression });
    let throw = (keyword("throw") * literal() - punct(";")).map(|x| {
        if let Expression::Lit { lit: Lit::StringLit { string_value }, type_ } = x {
            Statement::Throw {
                message: string_value,
            }
        } else {
            panic!("Currently only string literals can be thrown as exceptions")
        }
        });
    let try_ = (keyword("try") * punct("{") * call(statement)
        + punct("}") * keyword("catch") * punct("{") * call(statement)
        - punct("}"))
    .map(|(try_body, catch_body)| Statement::Try {
        try_body: Box::new(try_body),
        catch_body: Box::new(catch_body),
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
            }),
            stat2: Box::new(true_body),
        }),
        false_body: if let Some(false_body) = false_body {
            Box::new(Statement::Seq {
                stat1: Box::new(Statement::Assume {
                    assumption: negate(Rc::new(guard.clone())),
                }),
                stat2: Box::new(false_body),
            })
        } else {
            Box::new(Statement::Skip)
        },
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
                    }),
                    stat2: Box::new(body),
                }),
            }),
            stat2: Box::new(Statement::Assume {
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
        elem,
        range,
        domain,
        formula: Box::new(formula),
        type_: RuntimeType::UnknownRuntimeType,
    });

    forall | exists | expression2()
}

fn invocation<'a>() -> Parser<'a, Token<'a>, Invocation> {
    (identifier() - punct(".") + identifier() - punct("(") + arguments() - punct(")")).map(
        |((lhs, rhs), arguments)| Invocation::InvokeMethod {
            lhs,
            rhs,
            arguments,
            resolved: None,
        },
    )
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
        un_op: UnOp::Negative,
        value: Rc::new(value),
        type_: RuntimeType::UnknownRuntimeType,
    });

    let negate = (punct("!") * call(expression8)).map(|value| Expression::UnOp {
        un_op: UnOp::Negate,
        value: Rc::new(value),
        type_: RuntimeType::UnknownRuntimeType,
    });

    negative | negate | expression9()
}

fn expression9<'a>() -> Parser<'a, Token<'a>, Expression> {
    let var = identifier().map(|var| Expression::Var {
        var,
        type_: RuntimeType::UnknownRuntimeType,
    });
    let sizeof = (punct("#") * identifier()).map(|var| Expression::SizeOf {
        var,
        type_: RuntimeType::UnknownRuntimeType,
    });
    let parenthesized = punct("(") * call(expression) - punct(")");

    var | sizeof | parenthesized | literal()
}

fn lhs<'a>() -> Parser<'a, Token<'a>, Lhs> {
    let lhs_var = identifier().map(|var| Lhs::LhsVar {
        var,
        type_: RuntimeType::UnknownRuntimeType,
    });

    let lhs_field = (identifier() - punct(".") + identifier()).map(|(var, field)| Lhs::LhsField {
        var,
        var_type: RuntimeType::UnknownRuntimeType,
        field,
        type_: RuntimeType::UnknownRuntimeType,
    });

    let lhs_elem =
        (identifier() - punct("[") + expression() - punct("]")).map(|(var, index)| Lhs::LhsElem {
            var,
            index,
            type_: RuntimeType::UnknownRuntimeType,
        });

    lhs_var | lhs_field | lhs_elem
}

fn rhs<'a>() -> Parser<'a, Token<'a>, Rhs> {
    let rhs_expression = expression().map(|value| Rhs::RhsExpression {
        value,
        type_: RuntimeType::UnknownRuntimeType,
    });

    let rhs_field = (expression() - punct(".") + identifier()).map(|(var, field)| Rhs::RhsField {
        var,
        field,
        type_: RuntimeType::UnknownRuntimeType,
    });
    let rhs_call = invocation().map(|invocation| Rhs::RhsCall {
        invocation,
        type_: RuntimeType::UnknownRuntimeType,
    });
    let rhs_elem =
        (expression() - punct("[") + expression() - punct("]")).map(|(var, index)| Rhs::RhsElem {
            var,
            index,
            type_: RuntimeType::UnknownRuntimeType,
        });
    let rhs_constructor_call = (keyword("new") * identifier() - punct("(") + arguments()
        - punct(")"))
    .map(|(class_name, arguments)| Rhs::RhsCall {
        invocation: Invocation::InvokeConstructor {
            class_name,
            arguments,
            resolved: None,
        },
        type_: RuntimeType::UnknownRuntimeType,
    });
    let rhs_array = (keyword("new") * (classtype() | primitivetype())
        + (punct("[") * integer() - punct("]")).repeat(1..))
    .map(|(array_type, sizes)| Rhs::RhsArray {
        array_type,
        sizes,
        type_: RuntimeType::UnknownRuntimeType,
    });

    rhs_call | rhs_field | rhs_elem | rhs_expression | rhs_constructor_call | rhs_array
}

fn parameters<'a>() -> Parser<'a, Token<'a>, Vec<Parameter>> {
    let parameter = (nonvoidtype() + identifier()).map(|(type_, name)| Parameter { name, type_ });

    // can it be empty?
    list(parameter, punct(",")) | empty().map(|_| Vec::new())
}

fn type_<'a>() -> Parser<'a, Token<'a>, Type> {
    keyword("void").map(|_| Type { type_: None })
        | nonvoidtype().map(|type_| Type { type_: Some(type_) })
}

fn nonvoidtype<'a>() -> Parser<'a, Token<'a>, NonVoidType> {
    referencetype() | primitivetype()
}

fn primitivetype<'a>() -> Parser<'a, Token<'a>, NonVoidType> {
    keyword("uint").map(|_| NonVoidType::UIntType)
        | keyword("int").map(|_| NonVoidType::IntType)
        | keyword("bool").map(|_| NonVoidType::BoolType)
        | keyword("float").map(|_| NonVoidType::FloatType)
        | keyword("char").map(|_| NonVoidType::CharType)
}

fn referencetype<'a>() -> Parser<'a, Token<'a>, NonVoidType> {
    let arraytype = (classtype() | primitivetype()) - (punct("[") + punct("]")).repeat(1..);
    classtype() | arraytype
}

fn classtype<'a>() -> Parser<'a, Token<'a>, NonVoidType> {
    identifier().map(|identifier| NonVoidType::ReferenceType { identifier })
        | keyword("string").map(|_| NonVoidType::StringType)
}

fn integer<'a>() -> Parser<'a, Token<'a>, Expression> {
    take(1)
        .convert(|tokens| {
            let token = tokens[0]; // only one taken
            if let Token::Literal(s) = token {
                return Ok(s);
            }
            Err(())
        })
        .convert(i64::from_str)
        .map(|int_value| Expression::Lit {
            lit: Lit::IntLit { int_value },
            type_: RuntimeType::ANYRuntimeType,
        })
}

fn literal<'a>() -> Parser<'a, Token<'a>, Expression> {
    take(1)
        .convert(|tokens| {
            let token = tokens[0]; // only one taken
            if let Token::Literal(s) = token {
                return Ok(s);
            }
            Err(())
        })
        .map(|value| Expression::Lit {
            lit: match value {
                "null" => Lit::NullLit,
                "true" => Lit::BoolLit { bool_value: true },
                "false" => Lit::BoolLit { bool_value: false },
                s => {
                    if s.starts_with("'") && s.ends_with("'") {
                        let char_value = s.chars().nth(1).unwrap();
                        Lit::CharLit { char_value }
                    } else if s.starts_with("\"") && s.ends_with("\"") {
                        let string_value = s.slice(1..s.len() - 1);
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
        })
}

fn identifier<'a>() -> Parser<'a, Token<'a>, Identifier> {
    take(1).convert(|tokens| {
        let token = tokens[0]; // only one taken
        if let Token::Identifier(s) = token {
            Ok(s.to_string())
        } else {
            Err(())
        }
    })
}

// fn identifier_or_this<'a>() -> Parser<'a, Token<'a>, Identifier> {
//     take(1).convert(|tokens| {
//         let token = tokens[0]; // only one taken
//         if let Token::Identifier(s) = token {
//             Ok(s.to_string())
//         } else {
//             Err(())
//         }
//     }) | keyword("this").map(|_| "this".to_string())
// }

fn punct<'a>(p: &'a str) -> Parser<'a, Token<'a>, Token> {
    sym(Token::Punctuator(p))
}

fn keyword<'a>(kw: &'a str) -> Parser<'a, Token<'a>, Token> {
    sym(Token::Keyword(kw))
}

fn exceptional_assignment(lhs: &Lhs, rhs: &Rhs) -> HashSet<Expression> {
    let mut lhs = exceptional_lhs(lhs);
    lhs.extend(exceptional_rhs(rhs).into_iter());
    lhs
}

fn exceptional_lhs(lhs: &Lhs) -> HashSet<Expression> {
    match lhs {
        Lhs::LhsVar { .. } => HashSet::new(),
        Lhs::LhsField { var, var_type, .. } => HashSet::from([equal(
            Expression::Var {
                var: var.clone(),
                type_: var_type.clone(),
            },
            Expression::NULL,
        )]),
        Lhs::LhsElem { .. } => todo!(),
    }
}

fn exceptional_rhs(rhs: &Rhs) -> HashSet<Expression> {
    match rhs {
        Rhs::RhsExpression { value, .. } => exceptional_expression(value),
        Rhs::RhsField { var, .. } => HashSet::from([equal(var.clone(), Expression::NULL)]),
        Rhs::RhsElem { .. } => todo!(),
        Rhs::RhsCall { invocation, type_ } => exceptional_invocation(invocation),
        Rhs::RhsArray { .. } => todo!(),
    }
}

fn exceptional_expression(expression: &Expression) -> HashSet<Expression> {
    // TODO: div or mod by 0
    HashSet::new()
}

fn exceptional_invocation(invocation: &Invocation) -> HashSet<Expression> {
    match invocation {
        Invocation::InvokeMethod {
            lhs,
            arguments,
            resolved,
            ..
        } => {
            let exceptional_args: HashSet<_> = arguments
                .into_iter()
                .flat_map(|arg| exceptional_expression(arg).into_iter())
                .collect();
            if let DeclarationMember::Method {
                is_static: false, ..
            } = resolved.as_ref().unwrap().1
            {
                let exp = ors(std::iter::once(equal(
                    Expression::Var {
                        var: lhs.clone(),
                        type_: RuntimeType::REFRuntimeType,
                    },
                    Expression::NULL,
                ))
                .chain(exceptional_args.into_iter()));
                HashSet::from([exp])
            } else {
                exceptional_args
            }
        }
        Invocation::InvokeConstructor {
            class_name,
            arguments,
            resolved,
        } => todo!(),
    }
}

fn create_exceptional_ites(conditions: HashSet<Expression>, body: Statement) -> Statement {
    if conditions.len() == 0 {
        return body;
    }
    let cond = ors(conditions);
    // In the original OOX, a nested ITE is made if there are multiple exception conditions, not sure why so I will do it like this for now.
    Statement::Ite {
        guard: cond,
        true_body: Box::new(Statement::Throw {
            message: "exception".into(),
        }),
        false_body: Box::new(body),
    }
}

pub fn insert_exceptional_clauses(mut compilation_unit: CompilationUnit) -> CompilationUnit {
    let members = compilation_unit.members.iter_mut().filter_map(|m| match m {
        Declaration::Class { members, name } => Some((name, members)),
    });

    for (_, class) in members {
        let method_bodies = class.iter_mut().filter_map(|dcl| match dcl {
            DeclarationMember::Method { body, .. } => Some(body),
            _ => None,
        });
        for body in method_bodies {
            *body = helper(body.clone());
        }
    }

    fn helper(statement: Statement) -> Statement {
        match statement {
            Statement::Assign { lhs, rhs } => {
                let conditions = exceptional_assignment(&lhs, &rhs);

                create_exceptional_ites(conditions, Statement::Assign { lhs, rhs })
            }
            Statement::Call { invocation } => {
                let conditions = exceptional_invocation(&invocation);

                create_exceptional_ites(conditions, Statement::Call { invocation })
            }
            Statement::Ite {
                guard,
                true_body,
                false_body,
            } => Statement::Ite {
                guard,
                true_body: Box::new(helper(*true_body)),
                false_body: Box::new(helper(*false_body)),
            },

            Statement::Seq { stat1, stat2 } => {
                Statement::Seq { stat1: Box::new(helper(*stat1)), stat2: Box::new(helper(*stat2)) }
            },
            Statement::While { guard, body } => {
                Statement::While { guard, body: Box::new(helper(*body)) }
            },
            Statement::Try { try_body, catch_body } => {
                Statement::Try { try_body: Box::new(helper(*try_body)), catch_body: Box::new(helper(*catch_body))}
            },

            Statement::Block { body } => {
                Statement::Block { body: Box::new(helper(*body)) }
            }

            statement => statement,
        }
    }
    compilation_unit
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

    let c = insert_exceptional_clauses(c);
    dbg!(&c);
}
