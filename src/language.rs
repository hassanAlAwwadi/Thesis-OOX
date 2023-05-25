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
    LexerError((usize, usize)),
}

pub fn parse_program(file_content: &str, file_number: usize) -> Result<CompilationUnit, Error> {
    let tokens = tokens(file_content, file_number).map_err(Error::LexerError)?;

    parse(&tokens).map_err(Error::ParseError)
}
