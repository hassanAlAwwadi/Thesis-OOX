#![allow(dead_code)]

use z3_checker::playground;
mod lexer;
mod parser_pom;
mod stack;
mod syntax;

mod cfg;
mod exec;

mod eval;
mod typeable;

mod dsl;
mod z3_checker;

mod resolver;

mod pretty_print;

mod utils;

mod concretization;
mod symbolic_table;
mod fold;
mod exception_handler;

#[macro_use]
extern crate pest_derive;

fn main() {
    playground();
}
