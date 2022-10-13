use std::{fs, fmt::{Display, Arguments}};

use pest::{Parser, Span};

#[derive(Parser)]
#[grammar = "oox.pest"]
struct OOXLexer;

// pub struct Token {
//     pub token: String,
//     pub position: (usize, usize),
// }

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Token<'a> {
    Identifier(&'a str),
    Keyword(&'a str),
    Punctuator(&'a str),
    Literal(&'a str),
}

impl<'a> Display for Token<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:?}", self))
    }
}


pub fn tokens(file: &str) -> Vec<(Token, (usize, usize))> {
    let file = OOXLexer::parse(Rule::input, file)
        .expect("unsuccessful parse") // unwrap the parse result
        .next()
        .unwrap(); // get and unwrap the `file` rule; never fails

    dbg!(&file);

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
                    let token_rule = token_pair.into_inner().next().unwrap().as_rule();
                    let token_str = token_pair.as_str().to_owned();
                    // a token always is one of four, see grammar
                    let token = match token_rule {
                        Rule::identifier => Token::Identifier,
                        Rule::keyword => Token::Keyword,
                        Rule::punctuator => Token::Punctuator,
                        Rule::literal => Token::Literal,
                        _ => unreachable!(),
                    }(token_str);
                    (token, token_pair.as_span().start_pos().line_col())
                })
        })
        .collect::<Vec<_>>()
}
