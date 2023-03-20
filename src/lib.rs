#![allow(dead_code)]

mod lexer;
mod parser;
mod stack;
pub mod syntax;

mod cfg;
mod exec;

mod eval;
mod typeable;

pub mod dsl;
mod z3_checker;

mod resolver;

mod pretty_print;

mod utils;

mod concretization;
mod error;
mod exception_handler;
mod fold;
mod positioned;
mod symbol_table;
mod typing;

mod statistics;
mod mutation;

#[macro_use]
extern crate pest_derive;

use std::sync::Mutex;

pub use z3_checker::playground;

pub use exec::verify;

static FILE_NAMES: Mutex<String> = Mutex::new(String::new());
