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
mod symbol_table;
mod fold;
mod exception_handler;
mod typing;
mod error;
mod positioned;

#[macro_use]
extern crate pest_derive;


use std::sync::Mutex;



pub use z3_checker::playground;

static FILE_NAMES: Mutex<String> = Mutex::new(String::new());
