#![allow(dead_code)]
mod syntax;
mod parser_example;
mod parser;
mod lexer;
mod parser_pom;

mod cfg;

#[macro_use]
extern crate pest_derive;

fn main() {
    println!("Hello, world!");
}
