use pom::parser::*;

use std::str::{self, FromStr};

use crate::syntax::*;

use crate::lexer::*;


fn program<'a>() -> Parser<'a, Token<'a>, CompilationUnit> {
    class()
        .repeat(1)
        .map(|members| CompilationUnit { members })
}

fn class<'a>() -> Parser<'a, Token<'a>, Declaration> {
    let identifier_and_members =
        (keyword("class") * identifier()) + (punct("{") * members() - punct("}"));
    identifier_and_members.map(|(name, members)| Declaration::Class { name, members })
}

fn members<'a>() -> Parser<'a, Token<'a>, Vec<DeclarationMember>> {
    constructor().repeat(0..)
    // empty().map(|_| vec![])
}

fn constructor<'a>() -> Parser<'a, Token<'a>, DeclarationMember> {
    let p = identifier() - punct("(") + parameters() - punct(")");
    // let specification = todo!();
    let body = punct("{") * statement() - punct("}");

    (p + body).map(|((name, params), body)| DeclarationMember::Constructor {
        name,
        params,
        specification: Specification { requires: None, ensures: None, exceptional: None },
        body,
    })
}

fn statement<'a>() -> Parser<'a, Token<'a>, Statement> {
    let declaration =
        (nonvoidtype() + identifier()).map(|(type_, var)| Statement::Declare { type_, var });
    let assignment = (lhs() - punct(":=") + rhs()).map(|(lhs, rhs)| Statement::Assign { lhs, rhs });
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
    let ite = (keyword("if") * punct("(") * expression() - punct(")") + punct("{") * call(statement)
        - punct("}")
        + punct("{") * call(statement)
        - punct("}"))
    .map(|((guard, true_body), false_body)| Statement::Ite {
        guard,
        true_body: Box::new(true_body),
        false_body: Box::new(false_body),
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
    let p_statement =
    declaration
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
    (p_statement + (punct(";") * call(statement)).opt()).map(|(stmt, other_statement)| {
        if let Some(other_statement) = other_statement {
            return Statement::Seq { stat1: Box::new(stmt), stat2: Box::new(other_statement) }
        }
        return stmt
    })
}

fn verification_expression<'a>() -> Parser<'a, Token<'a>, Expression> {
    // todo
    (!empty()).map(|_| Expression::Var {
        var: "".to_owned(),
        type_: RuntimeType::UnknownRuntimeType,
    })
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

fn expression<'a>() -> Parser<'a, Token<'a>, Expression> {
    // todo!()
    take(1).map(|_| Expression::Lit { lit: Lit::NullLit, type_: RuntimeType::ANYRuntimeType })
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


    rhs_expression | rhs_field | rhs_call | rhs_elem | rhs_constructor_call | rhs_array
}

fn parameters<'a>() -> Parser<'a, Token<'a>, Vec<Parameter>> {
    let parameter = (nonvoidtype() + identifier()).map(|(type_, name)| Parameter { name, type_ });

    // can it be empty?
    list(parameter, punct(",")) | empty().map(|_| Vec::new())
}

fn nonvoidtype<'a>() -> Parser<'a, Token<'a>, NonVoidType> {
    primitivetype() | referencetype()
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
    take(1).convert(|tokens| {
        let token = tokens[0]; // only one taken
        if let Token::Literal(s) = token {
            return Ok(s)
        } 
        Err(())
    }).convert(i64::from_str).map(|int_value| Expression::Lit { lit: Lit::IntLit{ int_value}, type_: RuntimeType::ANYRuntimeType })
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

    assert!(false);
}

#[test]
fn test_statement() {
    let file_content = "int p; p := 0";

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    dbg!(as_ref);
    let c = (statement() - end()) .parse(&as_ref).unwrap(); // should not panic;
    dbg!(c);

    assert!(false);
}


// fn is_literal<'a>() -> Parser<'a, Token<'a>, Token<'a>> {
// 	is_a(|t: Token<'a>| match t {
//         Token::Literal(_s) => true,
//         _ => false,
//     })
// }
