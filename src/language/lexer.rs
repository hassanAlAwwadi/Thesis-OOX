use std::fmt::Display;

use pest::Parser;

use crate::positioned::{SourcePos, WithPosition};

#[derive(Parser)]
#[grammar = "oox.pest"]
struct OOXLexer;

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
            (Self::Literal(l0, _), Self::Literal(r0, _)) => l0 == r0,
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

/// Create a list of tokens from the file, or return the lexer error position.
pub(crate) fn tokens(file: &str, file_number: usize) -> Result<Vec<Token>, (usize, usize)> {
    let file = OOXLexer::parse(Rule::input, file)
        .map_err(|error| match error.line_col {
            pest::error::LineColLocation::Pos((line, col)) => (line, col),
            pest::error::LineColLocation::Span((start_line, start_col), _) => {
                (start_line, start_col)
            }
        })? // unwrap the parse result
        .next()
        .unwrap(); // get and unwrap the `file` rule; never fails

    // //dbg!(&file);

    let tokens = file
        .into_inner()
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
                    let token_fn = match token_rule {
                        Rule::identifier => Token::Identifier,
                        Rule::keyword => Token::Keyword,
                        Rule::punctuator => Token::Punctuator,
                        Rule::literal => Token::Literal,
                        _ => unreachable!(),
                    };
                    token_fn(
                        token_str,
                        SourcePos::SourcePos {
                            line,
                            col,
                            file_number,
                        },
                    )
                })
        })
        .collect::<Vec<_>>();
    Ok(tokens)
}
