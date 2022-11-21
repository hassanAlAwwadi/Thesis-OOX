#![allow(dead_code)]

use z3_checker::playground;
mod syntax;
mod lexer;
mod parser_pom;
mod stack;

mod cfg;
mod exec;

mod typeable;
mod eval;

mod dsl;
mod z3_checker;

mod resolver;

mod pretty_print;

mod utils;

#[macro_use]
extern crate pest_derive;

fn main() {
    playground();
}
