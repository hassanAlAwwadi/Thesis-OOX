use std::{fmt::{Display}};

use pest::{Parser};

use crate::positioned::{SourcePos, WithPosition};

#[derive(Parser)]
#[grammar = "oox.pest"]
struct OOXLexer;

// pub struct Token {
//     pub token: String,
//     pub position: (usize, usize),
// }

#[derive(Debug, Copy, Clone)]
pub enum Token<'a> {
    Identifier(&'a str, SourcePos),
    Keyword(&'a str, SourcePos),
    Punctuator(&'a str, SourcePos),
    Literal(&'a str, SourcePos),
}

impl PartialEq for Token<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Identifier(l0, _), Self::Identifier(r0, _)) => l0 == r0,
            (Self::Keyword(l0, _), Self::Keyword(r0, _)) => l0 == r0,
            (Self::Punctuator(l0, _), Self::Punctuator(r0, _)) => l0 == r0,
            (Self::Literal(l0, _), Self::Literal(r0, _)) => l0 == r0 ,
            _ => false,
        }
    }
}

impl WithPosition for Token<'_> {
    fn get_position(&self) -> SourcePos {
        *match self {
            Token::Identifier(_, pos) => pos,
            Token::Keyword(_, pos) => pos,
            Token::Punctuator(_, pos) => pos,
            Token::Literal(_, pos) => pos,
        }
    }
}

impl<'a> Display for Token<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:?}", self))
    }
}


// pub fn tokens(file: &str) -> Vec<(Token, (usize, usize))> {
pub fn tokens<'a>(file: &'a str) -> Vec<Token<'a>> {
    let file = OOXLexer::parse(Rule::input, file)
        .expect("unsuccessful parse") // unwrap the parse result
        .next()
        .unwrap(); // get and unwrap the `file` rule; never fails

    // //dbg!(&file);

    file.into_inner()
        .filter_map(|record| {
            if record.as_rule() == Rule::section {
                Some(record)
            } else {
                None
            }
        })
        .flat_map(|record| {
            record
                .into_inner()
                .filter(|record| record.as_rule() == Rule::token)
                .map(|token_pair| {
                    let (line, col) = token_pair.as_span().start_pos().line_col();
                    let token_str = token_pair.as_str();
                    let token_rule = token_pair.into_inner().next().unwrap().as_rule();
                    // a token always is one of four, see grammar
                    let token = match token_rule {
                        Rule::identifier => Token::Identifier,
                        Rule::keyword => Token::Keyword,
                        Rule::punctuator => Token::Punctuator,
                        Rule::literal => Token::Literal,
                        _ => unreachable!(),
                    }(&token_str, SourcePos::SourcePos { line, col });
                    // (token, token_pair.as_span().start_pos().line_col())
                    token
                })
        })
        .collect::<Vec<_>>()
}
