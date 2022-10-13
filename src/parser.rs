// use std::fs;

// use nom::{
//     bytes::complete::{tag, take_till, take_till1, take_until, take_while, take_while_m_n},
//     character::{
//         complete::{alpha1, anychar, char, line_ending},
//         is_newline, is_space,
//     },
//     combinator::{map_res, not},
//     error::{Error, ParseError},
//     multi::{count, many0, many_till},
//     sequence::{preceded, terminated, tuple, delimited},
//     Err, IResult, InputTakeAtPosition,
// };

// use crate::lexer::{tokens, Token};

// use crate::syntax::*;

// fn is_newline_char(c: char) -> bool {
//     is_newline(c as u8)
// }

// fn space_char(c: char) -> bool {
//     is_space(c as u8) || is_newline(c as u8)
// }

// // type Token<'a> = &'a str;
// // type Tokens<'a> = &'a [Token<'a>];

// // impl<'a> InputTake for Token<'a> {
// //     #[inline]
// //     fn take(&self, count: usize) -> Self {
// //       &self[0..count]
// //     }
// //     #[inline]
// //     fn take_split(&self, count: usize) -> (Self, Self) {
// //       let (prefix, suffix) = self.split_at(count);
// //       (suffix, prefix)
// //     }
// //   }


// // fn

// pub fn take_till_and<F, Input, Error: ParseError<Input>>(
//     cond: F,
// ) -> impl Fn(Input) -> IResult<Input, Input, Error>
// where
//     Input: InputTakeAtPosition,
//     F: Fn(<Input as InputTakeAtPosition>::Item) -> bool + Copy,
// {
//     move |i: Input| take_till(cond)(i)
// }

// // fn comment(input: &str) -> IResult<&str, ()> {
// //     let (input, _) = count(char('/'), 2)(input)?;

// //     dbg!(input);
// //     // let (input, _) = terminated(many0(anychar), line_ending)(input)?;
// //     let (input, _) = many_till(anychar, line_ending)(input)?;
// //     dbg!(input);
// //     // char::from_digi
// //     Ok((input, ()))
// // }

// // fn compilation_unit(input: &[Token]) -> IResult<&[Token], CompilationUnit> {
// //     let (input, members) = many0(declaration)(input)?;

// //     Ok((input, CompilationUnit { members }))
// // }

// // fn declaration(input: &[Token]) -> IResult<&[Token], Declaration> {
// //     let (input, _) = tag()(input)?;
// //     let (input, (identifier)) = tuple((take_while(space_char), alpha1))(input)?;
// //     // preceded(take_while(space_char), delimited(tag("{"), members, tag("}")))(input)?;
    
// //     todo!()
// // }

// fn members(input: &str) -> IResult<&str, Vec<DeclarationMember>> {
//     let (input, type_) = preceded(take_while(space_char), alpha1)(input)?;

//     todo!()
// }

// fn nonVoidType(input: &str) -> IResult<&[&str], NonVoidType> {
    
//     todo!()
// }

// fn parse(bs: &str) -> Option<CompilationUnit> {
//     unimplemented!()
// }

// #[test]
// fn does_this_Even_work() {
//     let unparsed_file = fs::read_to_string("examples/comments.oox").expect("cannot read file");

//     let tokens = crate::lexer::tokens(&unparsed_file);

    

// }


// // #[test]
// // fn parse_linkedlist() {
// //     let compilation_unit = parse(include_str!("../examples/linkedlist.oox"));
// //     assert!(compilation_unit.is_some());
// // }

// // #[test]
// // fn parse_comment() {
// //     let input = include_str!("../examples/comments.oox");

// //     assert_eq!(
// //         nom::combinator::map(many0(preceded(take_while(space_char), comment)), |_| ())(input),
// //         Ok(("class X {}", ()))
// //     );
// // }
