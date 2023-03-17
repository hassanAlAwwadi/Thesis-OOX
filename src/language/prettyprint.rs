use pretty::{docs, Arena, DocAllocator, DocBuilder, BoxAllocator};

// use super::{BinOp, Expression};

use crate::{syntax::Identifier, parser::expression, lexer::tokens, BinOp, Expression};

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &Expression {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        // todo!()

        match self {
            Expression::Var { var, .. } => allocator.text(var.to_string()),
            Expression::BinOp {
                bin_op, lhs, rhs, ..
            } => lhs
                .pretty(allocator)
                .append(allocator.space())
                .append(bin_op_to_str(bin_op))
                .append(allocator.space())
                .append(rhs.pretty(allocator)),
            _ => todo!(),
        }
    }
}

#[test]
fn test() {
    let arena = &Arena::<()>::new();
    let doc = docs![
        arena,
        "let",
        arena.softline(),
        "x",
        arena.softline(),
        "=",
        arena.softline(),
        Some("123"),
    ];
    assert_eq!(doc.1.pretty(80).to_string(), "let x = 123");
}

#[test]
fn feature() {
    let tokens = tokens("x && y").unwrap();
    let exp = expression().parse(&tokens).unwrap();
    let allocator = BoxAllocator;
    println!("{}", pretty::Pretty::pretty(&exp, &allocator).1.pretty(10));
}

fn bin_op_to_str(bin_op: &BinOp) -> &'static str {
    match bin_op {
        BinOp::Implies => "==>",
        BinOp::And => "&&",
        BinOp::Or => "||",
        BinOp::Equal => "==",
        BinOp::NotEqual => "!=",
        BinOp::LessThan => "<",
        BinOp::LessThanEqual => "<=",
        BinOp::GreaterThan => ">",
        BinOp::GreaterThanEqual => ">=",
        BinOp::Plus => "+",
        BinOp::Minus => "-",
        BinOp::Multiply => "*",
        BinOp::Divide => "/",
        BinOp::Modulo => "%",
    }
}