use nom::Slice;
use pom::parser::*;

use std::str::{self, FromStr};

use crate::syntax::*;

use crate::lexer::*;

pub fn parse<'a>(tokens: &[Token<'a>]) -> Result<CompilationUnit, pom::Error> {
    (program() - end()).parse(tokens)
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
        |(((((is_static, return_type), name), params), specification), body)| DeclarationMember::Method {
            is_static,
            return_type,
            name,
            params,
            specification,
            body,
        },
    )

    // todo!()
}


fn constructor<'a>() -> Parser<'a, Token<'a>, DeclarationMember> {
    let p = identifier() - punct("(") + parameters() - punct(")");
    // let specification = todo!();
    let body = punct("{") * statement() - punct("}");

    (p + specification() + body).map(|(((name, params), specification), body)| DeclarationMember::Constructor {
        name,
        params,
        specification,
        body,
    })
}

fn body<'a>() -> Parser<'a, Token<'a>, Statement> {
    punct("{") * statement() - punct("}")
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

    let while_ = (keyword("while") * punct("(") * expression() - punct(")") + call(statement)).map(
        |(guard, body)| Statement::While {
            guard,
            body: Box::new(body),
        },
    );
    let ite = (keyword("if") * punct("(") * expression() - punct(")")
        + call(statement)
        + (keyword("else") * call(statement)).opt())
    .map(|((guard, true_body), false_body)| Statement::Ite {
        guard,
        true_body: Box::new(true_body),
        false_body: Box::new(false_body.unwrap_or(Statement::Skip)),
    });
    let continue_ = (keyword("continue") * punct(";")).map(|_| Statement::Continue);
    let break_ = (keyword("break") * punct(";")).map(|_| Statement::Break);
    let return_ = (keyword("return") * expression().opt() - punct(";"))
        .map(|expression| Statement::Return { expression });
    let throw = (keyword("throw") * punct(";")).map(|_| Statement::Throw {
        message: String::new(),
    });
    let try_ = (keyword("try") * punct("{") * call(statement)
        + punct("}") * keyword("catch") * punct("{") * call(statement)
        - punct("}"))
    .map(|(try_body, catch_body)| Statement::Try {
        try_body: Box::new(try_body),
        catch_body: Box::new(catch_body),
    });
    let block = (punct("{") * call(statement) - punct("}")).map(|body| Statement::Block {
        body: Box::new(body),
    });

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
            return Statement::Seq {
                stat1: Box::new(stmt),
                stat2: Box::new(other_statement),
            };
        }
        return stmt;
    })
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

    (requires.opt() + ensures.opt() + exceptional.opt()).map(|((requires, ensures), exceptional)| Specification{ requires, ensures, exceptional })
}

fn expression<'a>() -> Parser<'a, Token<'a>, Expression> {
    expression1()
}

fn expression2<'a>() -> Parser<'a, Token<'a>, Expression> {
    let implies =
        (expression3() + punct("==>") * call(expression2)).map(|(lhs, rhs)| Expression::BinOp {
            bin_op: BinOp::Implies,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
            type_: RuntimeType::UnknownRuntimeType,
        });

    implies | expression3()
}

fn expression3<'a>() -> Parser<'a, Token<'a>, Expression> {
    // let and =
    //     (expression4() + punct("&&") * call(expression3)).map(|(lhs, rhs)| Expression::BinOp {
    //         bin_op: BinOp::And,
    //         lhs: Box::new(lhs),
    //         rhs: Box::new(rhs),
    //         type_: RuntimeType::UnknownRuntimeType,
    //     });
    // let or =
    //     (expression4() + punct("||") * call(expression3)).map(|(lhs, rhs)| Expression::BinOp {
    //         bin_op: BinOp::Or,
    //         lhs: Box::new(lhs),
    //         rhs: Box::new(rhs),
    //         type_: RuntimeType::UnknownRuntimeType,
    //     });

    let and = punct("&&").map(|_| BinOp::And);
    let or = punct("||").map(|_| BinOp::Or);

    (expression4() + ((and | or) + call(expression3)).opt()).map(|(lhs, rhs)| {
        if let Some((bin_op, rhs)) = rhs {
            Expression::BinOp {
                bin_op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
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
    //         lhs: Box::new(lhs),
    //         rhs: Box::new(rhs),
    //         type_: RuntimeType::UnknownRuntimeType,
    //     });

    // let neq =
    //     (expression5() + punct("!=") * call(expression4)).map(|(lhs, rhs)| Expression::BinOp {
    //         bin_op: BinOp::NotEqual,
    //         lhs: Box::new(lhs),
    //         rhs: Box::new(rhs),
    //         type_: RuntimeType::UnknownRuntimeType,
    //     });

    let eq = punct("==").map(|_| BinOp::Equal);
    let neq = punct("!=").map(|_| BinOp::NotEqual);

    (expression5() + ((eq | neq) + call(expression4)).opt()).map(|(lhs, rhs)| {
        if let Some((bin_op, rhs)) = rhs {
            Expression::BinOp {
                bin_op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
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
    //     lhs: Box::new(lhs),
    //     rhs: Box::new(rhs),
    //     type_: RuntimeType::UnknownRuntimeType,
    // });
    // let gt = (expression6() + punct(">") * call(expression5)).map(|(lhs, rhs)| Expression::BinOp {
    //     bin_op: BinOp::GreaterThan,
    //     lhs: Box::new(lhs),
    //     rhs: Box::new(rhs),
    //     type_: RuntimeType::UnknownRuntimeType,
    // });
    // let lte =
    //     (expression6() + punct("<=") * call(expression5)).map(|(lhs, rhs)| Expression::BinOp {
    //         bin_op: BinOp::LessThanEqual,
    //         lhs: Box::new(lhs),
    //         rhs: Box::new(rhs),
    //         type_: RuntimeType::UnknownRuntimeType,
    //     });
    // let gte =
    //     (expression6() + punct(">=") * call(expression5)).map(|(lhs, rhs)| Expression::BinOp {
    //         bin_op: BinOp::GreaterThanEqual,
    //         lhs: Box::new(lhs),
    //         rhs: Box::new(rhs),
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
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
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
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                type_: RuntimeType::UnknownRuntimeType,
            }  
        } else {
            lhs
        }
    })
}

fn expression7<'a>() -> Parser<'a, Token<'a>, Expression> {
    // let multiply =
    //     (expression8() + punct("*") * call(expression7)).map(|(lhs, rhs)| Expression::BinOp {
    //         bin_op: BinOp::Multiply,
    //         lhs: Box::new(lhs),
    //         rhs: Box::new(rhs),
    //         type_: RuntimeType::UnknownRuntimeType,
    //     });
    // let divide =
    //     (expression8() + punct("/") * call(expression7)).map(|(lhs, rhs)| Expression::BinOp {
    //         bin_op: BinOp::Divide,
    //         lhs: Box::new(lhs),
    //         rhs: Box::new(rhs),
    //         type_: RuntimeType::UnknownRuntimeType,
    //     });
    // let modulo =
    //     (expression8() + punct("%") * call(expression7)).map(|(lhs, rhs)| Expression::BinOp {
    //         bin_op: BinOp::Modulo,
    //         lhs: Box::new(lhs),
    //         rhs: Box::new(rhs),
    //         type_: RuntimeType::UnknownRuntimeType,
    //     });

    let multiply = punct("*").map(|_| BinOp::Multiply);
    let divide = punct("/").map(|_| BinOp::Divide);
    let modulo = punct("%").map(|_| BinOp::Modulo);

    (expression8() + ((multiply | divide | modulo) + call(expression7)).opt()).map(|(lhs, rhs)| {
        if let Some((bin_op, rhs)) = rhs {
            Expression::BinOp {
                bin_op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
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
        value: Box::new(value),
        type_: RuntimeType::UnknownRuntimeType,
    });

    let negate = (punct("!") * call(expression8)).map(|value| Expression::UnOp {
        un_op: UnOp::Negate,
        value: Box::new(value),
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
                            Lit::FloatLit { float_value }
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

fn punct<'a>(p: &'a str) -> Parser<'a, Token<'a>, Token> {
    sym(Token::Punctuator(p))
}

fn keyword<'a>(kw: &'a str) -> Parser<'a, Token<'a>, Token> {
    sym(Token::Keyword(kw))
}

#[test]
fn class_with_constructor() {
    let file_content = include_str!("../examples/class_with_constructor.oox");

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    dbg!(as_ref);
    let c = program().parse(&as_ref).unwrap(); // should not panic;
    dbg!(c);
}

#[test]
fn test_statement() {
    let file_content = "int p; p := 0;";

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    dbg!(as_ref);
    let c = (statement() - end()).parse(&as_ref).unwrap(); // should not panic;
    dbg!(c);
    assert!(false);
}

#[test]
fn class_with_methods() {
    let file_content = include_str!("../examples/class_with_methods.oox");

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    // dbg!(as_ref);
    let c = (program() - end()).parse(&as_ref);
    // dbg!(&c);
    c.unwrap(); // should not panic;

    // dbg!(c);
    // assert!(false);
}

#[test]
fn bsort_test() {
    let file_content = include_str!("../examples/bsort.oox");

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    // dbg!(as_ref);
    let c = (program() - end()).parse(&as_ref);
    // dbg!(&c);
    c.unwrap(); // should not panic;

    // dbg!(c);
    // assert!(false);
}

#[test]
fn this_dot() {
    let file_content = "p := this.value;";

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    dbg!(as_ref);
    let c = (statement() - end()).parse(&as_ref).unwrap(); // should not panic;
    dbg!(c);
    assert!(false);
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
    dbg!(&as_ref);
    let c = (statement() - end()).parse(&as_ref).unwrap(); // should not panic;
    dbg!(c);
    assert!(false);
}

#[test]
fn boolean() {
    let file_content = "true";
    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    dbg!(as_ref);
    let c = (expression() - end()).parse(&as_ref).unwrap(); // should not panic;
    dbg!(c);
    assert!(false);
}

#[test]
fn test_statement2() {
    let file_content = "Node n; n := this.next ;
    bool b;
    b := n.member(x) ;
    return b;";
    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    dbg!(as_ref);
    let c = (statement() - end()).parse(&as_ref).unwrap(); // should not panic;
    dbg!(c);
    assert!(false);
}

#[test]
fn forall() {
    let file_content = "(forall x, i : a : i<k ==> (forall x, i : a : i<k ==> true))";
    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    // dbg!(as_ref);
    let c = (expression() - end()).parse(&as_ref).unwrap(); // should not panic;
    dbg!(c);
    assert!(false);
}

// fn is_literal<'a>() -> Parser<'a, Token<'a>, Token<'a>> {
// 	is_a(|t: Token<'a>| match t {
//         Token::Literal(_s) => true,
//         _ => false,
//     })
// }
