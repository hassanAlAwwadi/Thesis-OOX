#![allow(dead_code)]

mod stack;

mod cfg;
mod exec;
mod reachability;

mod typeable;

pub mod dsl;
mod z3_checker;

mod resolver;

mod language;

mod utils;

mod concretization;
mod error;
mod exception_handler;
mod fold;
mod positioned;
mod symbol_table;
mod typing;

mod merge;
mod mutation;
mod state;
mod statistics;
mod unique_supply;
pub use language::*;

#[macro_use]
extern crate pest_derive;

use std::sync::Mutex;

pub use exec::{execute_verify_thrice, set_up_verify, verify, Heuristic, Options, SymResult};

pub use positioned::SourcePos;

pub use typing::type_compilation_unit;

pub use symbol_table::SymbolTable;

pub use mutation::mutate_program;

pub static FILE_NAMES: Mutex<Vec<String>> = Mutex::new(vec![]);
