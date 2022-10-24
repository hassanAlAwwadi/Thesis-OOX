use std::fs;

use nom::{
    bytes::complete::{tag, take_till, take_till1, take_until, take_while, take_while_m_n, take_while1},
    character::{
        complete::{alpha1, anychar, char, line_ending},
        is_alphabetic, is_newline, is_space,
    },
    combinator::{map, map_res, not, opt},
    error::{Error, ParseError},
    multi::{count, many0, many_till},
    sequence::{delimited, preceded, terminated, tuple},
    Err, IResult, InputTakeAtPosition, Parser, branch::alt,
};

use crate::lexer::{tokens, Token};

use crate::syntax::*;

fn is_newline_char(c: char) -> bool {
    is_newline(c as u8)
}

fn spacing(input: &[u8]) -> IResult<&[u8], &[u8]> {
    take_while(|c| is_space(c) || is_newline(c))(input)
}

// fn

pub fn take_till_and<F, Input, Error: ParseError<Input>>(
    cond: F,
) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
    Input: InputTakeAtPosition,
    F: Fn(<Input as InputTakeAtPosition>::Item) -> bool + Copy,
{
    move |i: Input| take_till(cond)(i)
}

// fn comment(input: &str) -> IResult<&str, ()> {
//     let (input, _) = count(char('/'), 2)(input)?;

//     dbg!(input);
//     // let (input, _) = terminated(many0(anychar), line_ending)(input)?;
//     let (input, _) = many_till(anychar, line_ending)(input)?;
//     dbg!(input);
//     // char::from_digi
//     Ok((input, ()))
// }

// fn compilation_unit(input: &[Token]) -> IResult<&[Token], CompilationUnit> {
//     let (input, members) = many0(declaration)(input)?;

//     Ok((input, CompilationUnit { members }))
// }

// fn declaration(input: &[Token]) -> IResult<&[Token], Declaration> {
//     let (input, _) = tag()(input)?;
//     let (input, (identifier)) = tuple((take_while(space_char), alpha1))(input)?;
//     // preceded(take_while(space_char), delimited(tag("{"), members, tag("}")))(input)?;

//     todo!()
// }

// fn members(input: &str) -> IResult<&str, Vec<DeclarationMember>> {
//     let (input, type_) = preceded(take_while(space_char), alpha1)(input)?;

//     todo!()
// }

fn nonVoidType(input: &str) -> IResult<&[&str], NonVoidType> {
    todo!()
}

fn parse(bs: &str) -> Option<CompilationUnit> {
    unimplemented!()
}

// fn expression1(input: &[u8]) -> IResult<&[u8], NonVoidType> {
//     let (input, (method, _, url, _, version, _)) =
//     tuple((method, spacing, url, spacing, http_version, line_ending))(i)?;
// }

fn identifier(input: &[u8]) -> IResult<&[u8], String> {
    map(take_while1(is_alphabetic), |x: &[u8]| {
        String::from_utf8_lossy(x).to_string()
    })(input)
}

fn expression1<'a>(input: &[u8]) -> IResult<&[u8], Expression> {
    let punct = |s: &'a str| tuple((spacing, tag(s), spacing));

    let ver_expr = map(tuple((
        spacing,
        alt((tag("forall"), tag("exists"))),
        spacing,
        identifier,
        punct(","),
        identifier,
        punct(":"),
        identifier,
        punct(":"),
        spacing,
        expression2,
    )), |(_, ver_type, _, elem, _, range, _, domain, _, _, formula)| match ver_type {
        b"forall" => Expression::Forall {
            elem,
            range,
            domain,
            formula: Box::new(formula),
            type_: RuntimeType::UnknownRuntimeType,
        },
        b"exists" => Expression::Exists {
            elem,
            range,
            domain,
            formula: Box::new(formula),
            type_: RuntimeType::UnknownRuntimeType,
        },
        _ => unreachable!()
    });

    alt((ver_expr, expression2))(input)
}

fn expression(input: &[u8]) -> IResult<&[u8], Expression> {
    expression1(input)
}

fn verification_expression(input: &[u8]) -> IResult<&[u8], Expression> {
    expression1(input)
}

fn expression2(input: &[u8]) -> IResult<&[u8], Expression> {
    let implies = map(tuple((
        spacing,
        expression3,
        spacing,
        tag("==>"),
        spacing,
        expression2,
    )), |(_, lhs, _, _, _, rhs)| Expression::BinOp { bin_op: BinOp::Implies, lhs: Box::new(lhs), rhs: Box::new(rhs), type_: RuntimeType::UnknownRuntimeType });

    alt((implies, expression3))(input)
}

fn expression3(input: &[u8]) -> IResult<&[u8], Expression> {
    let and = map(tuple((spacing, expression4, spacing, tag("&&"), spacing, expression3)), |(_, lhs, _, _, _, rhs)| Expression::BinOp {
        bin_op: BinOp::And,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
        type_: RuntimeType::UnknownRuntimeType,
    });

    let or = map(tuple((spacing, expression4, spacing, tag("||"), spacing, expression3)), |(_, lhs, _, _, _, rhs)| Expression::BinOp {
        bin_op: BinOp::And,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
        type_: RuntimeType::UnknownRuntimeType,
    });

    alt((and, or, expression4))(input)
}
fn expression4(input: &[u8]) -> IResult<&[u8], Expression> {
    let equals = map(tuple((spacing, expression5, spacing, tag("=="), spacing, expression4)), |(_, lhs, _, _, _, rhs)| Expression::BinOp {
        bin_op: BinOp::Equal,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
        type_: RuntimeType::UnknownRuntimeType,
    });

    let neq = map(tuple((spacing, expression5, spacing, tag("!="), spacing, expression4)), |(_, lhs, _, _, _, rhs)| Expression::BinOp {
        bin_op: BinOp::NotEqual,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
        type_: RuntimeType::UnknownRuntimeType,
    });

    alt((equals, neq, expression5))(input)
}
fn expression5(input: &[u8]) -> IResult<&[u8], Expression> {
    let lte = map(tuple((spacing, expression6, spacing, tag("<="), spacing, expression5)), |(_, lhs, _, _, _, rhs)| Expression::BinOp {
        bin_op: BinOp::LessThanEqual,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
        type_: RuntimeType::UnknownRuntimeType,
    });

    let gte = map(tuple((spacing, expression6, spacing, tag(">="), spacing, expression5)), |(_, lhs, _, _, _, rhs)| Expression::BinOp {
        bin_op: BinOp::GreaterThanEqual,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
        type_: RuntimeType::UnknownRuntimeType,
    });

    let gt = map(tuple((spacing, expression6, spacing, tag(">"), spacing, expression5)), |(_, lhs, _, _, _, rhs)| Expression::BinOp {
        bin_op: BinOp::GreaterThan,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
        type_: RuntimeType::UnknownRuntimeType,
    });

    let lt = map(tuple((spacing, expression6, spacing, tag("<"), spacing, expression5)), |(_, lhs, _, _, _, rhs)| Expression::BinOp {
        bin_op: BinOp::LessThan,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
        type_: RuntimeType::UnknownRuntimeType,
    });

    alt((lte, gte, lt, gt, expression6))(input)
}

fn expression6(input: &[u8]) -> IResult<&[u8], Expression> {
    let (input, (_, lhs, _)) = tuple((spacing, expression7, spacing))(input)?;

    let plus = tuple((map(tag("+"), |_| BinOp::Plus), spacing, expression6));

    let minus = tuple((map(tag("-"), |_| BinOp::Minus), spacing, expression6));
    
    let plus_or_minus = map(alt((plus, minus)), move |(bin_op, _, rhs)| {
        Expression::BinOp {
            bin_op,
            lhs: Box::new(lhs.clone()),
            rhs: Box::new(rhs),
            type_: RuntimeType::UnknownRuntimeType,
        }
    });



    alt((plus_or_minus, expression7))(input)
}

fn expression7(input: &[u8]) -> IResult<&[u8], Expression> {
    let (input, (_, lhs, _)) = tuple((spacing, expression8, spacing))(input)?;

    let multiply = tuple((map(tag("*"), |_| BinOp::Multiply), spacing, expression7));
    let divide = tuple((map(tag("/"), |_| BinOp::Divide), spacing, expression7));
    let modulo = tuple((map(tag("%"), |_| BinOp::Modulo), spacing, expression7));

    map(opt(alt((multiply, divide, modulo))), move |rhs| {
        if let Some((bin_op, _, rhs)) = rhs {
            Expression::BinOp {
                bin_op,
                lhs: Box::new(lhs.clone()),
                rhs: Box::new(rhs),
                type_: RuntimeType::UnknownRuntimeType,
            }
        } else {
            lhs.clone()
        }
    })(input)
}

fn expression8(input: &[u8]) -> IResult<&[u8], Expression> {
    let (input, _) = spacing(input)?;

    let negative = tuple((map(tag("-"), |_| UnOp::Negative), expression8));
    let negate = tuple((map(tag("!"), |_| UnOp::Negate), expression8));

    let negate_or_negative = map(alt((negative, negate)), |(un_op, value)| {
        Expression::UnOp {
            un_op,
            value: Box::new(value),
            type_: RuntimeType::UnknownRuntimeType,
        }
    });
    
    alt((negate_or_negative, expression9))(input)

}

fn expression9(input: &[u8]) -> IResult<&[u8], Expression> {
    let (input, _) = spacing(input)?;

    let var = map(identifier, |var| Expression::Var { var, type_: RuntimeType::UnknownRuntimeType });

    let sizeof = map(tuple((tag("#"), identifier)), |(_, var)| Expression::SizeOf {
        var,
        type_: RuntimeType::UnknownRuntimeType,
    });
    let parenthesized = map(tuple((tag("("), expression, spacing, tag(")"))), |(_, exp, _, _)| exp);

    let bool = map(tag("true"), |x| Expression::Lit { lit: Lit::BoolLit { bool_value: true }, type_: RuntimeType::UnknownRuntimeType });

    alt((var, sizeof, parenthesized, bool))(input)
}


#[test]
fn does_this_Even_work() {
    let unparsed_file = fs::read_to_string("examples/comments.oox").expect("cannot read file");

    let tokens = crate::lexer::tokens(&unparsed_file);
}


#[test]
fn parse_boolean() {
    let file_content = b"(forall x, i : a : i<k ==> (forall x, i : a : i<k ==> true))";
    let compilation_unit = expression9(file_content);
    // compilation_unit;
    dbg!(compilation_unit.unwrap());
    assert!(false);

}
// #[test]
// fn parse_linkedlist() {
//     let compilation_unit = parse(include_str!("../examples/linkedlist.oox"));
//     assert!(compilation_unit.is_some());
// }

// #[test]
// fn parse_comment() {
//     let input = include_str!("../examples/comments.oox");

//     assert_eq!(
//         nom::combinator::map(many0(preceded(take_while(space_char), comment)), |_| ())(input),
//         Ok(("class X {}", ()))
//     );
// }
