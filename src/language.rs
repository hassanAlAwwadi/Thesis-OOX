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

/// Parses the program.
///
/// `without_assumptions` will not insert assumptions at if and while statements, which is useful for generating mutations.
pub fn parse_program(
    file_content: &str,
    file_number: usize,
    without_assumptions: bool,
) -> Result<CompilationUnit, Error> {
    let tokens = tokens(file_content, file_number).map_err(Error::LexerError)?;

    parse(&tokens, without_assumptions).map_err(Error::ParseError)
}
