pub mod prettyprint;

pub mod parser;

pub use parser::*;

pub mod syntax;


mod lexer;

pub use syntax::*;

pub(crate) use lexer::tokens;

#[derive(Debug)]
pub enum Error {
    ParseError(pom::Error),
    LexerError((usize, usize))
}

pub fn parse_program(file_content: &str, with_exceptional_clauses: bool) -> Result<CompilationUnit, Error> {
    let tokens = tokens(file_content).map_err(Error::LexerError)?;

    parse(&tokens, with_exceptional_clauses).map_err(Error::ParseError)
}