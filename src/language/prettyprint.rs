use pretty::{docs, Arena, BoxAllocator, DocAllocator, DocBuilder};

// use super::{BinOp, Expression};

use crate::{lexer::tokens, parser::expression, syntax::Identifier, typeable::Typeable};

use super::syntax::*;

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &Expression {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        let comma = || allocator.text(",");
        let colon = || allocator.text(":");

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
            Expression::UnOp { un_op, value, .. } => {
                let un_op_str = match un_op {
                    UnOp::Negative => "-",
                    UnOp::Negate => "!",
                };
                allocator.text(un_op_str).append(value.pretty(allocator))
            }
            Expression::SymbolicVar { var, .. } => allocator.text(var.to_string()),
            Expression::Lit { lit, .. } => match lit {
                Lit::NullLit => allocator.text("null"),
                Lit::BoolLit { bool_value } => allocator.text(bool_value.to_string()),
                Lit::UIntLit { uint_value } => allocator.text(uint_value.to_string()),
                Lit::IntLit { int_value } => allocator.text(int_value.to_string()),
                Lit::FloatLit { float_value } => allocator.text(float_value.to_string()),
                Lit::StringLit { string_value } => allocator.text(string_value.to_string()),
                Lit::CharLit { char_value } => allocator.text(char_value.to_string()),
            },
            Expression::SizeOf { var, .. } => allocator.text(format!("#{}", var)),
            Expression::Ref { ref_, .. } => allocator
                .text("ref")
                .append(allocator.text(ref_.to_string()).parens()),

            Expression::Conditional {
                guard,
                true_,
                false_,
                ..
            } => allocator.text("ite").append(
                guard
                    .pretty(allocator)
                    .append(comma())
                    .append(true_.pretty(allocator))
                    .append(comma())
                    .append(false_.pretty(allocator))
                    .parens(),
            ),
            Expression::Forall {
                elem,
                range,
                domain,
                formula,
                ..
            } => allocator
                .text("forall")
                .append(elem.to_string())
                .append(comma())
                .append(range.to_string())
                .append(colon())
                .append(domain.to_string())
                .append(colon())
                .append(formula.pretty(allocator)),
            Expression::Exists {
                elem,
                range,
                domain,
                formula,
                ..
            } => allocator
                .text("exists")
                .append(elem.to_string())
                .append(comma())
                .append(range.to_string())
                .append(colon())
                .append(domain.to_string())
                .append(colon())
                .append(formula.pretty(allocator)),
            Expression::SymbolicRef { var, .. } => allocator.text(var.to_string()),
        }
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &Statement {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        let semicolon = || allocator.text(";");
        match self {
            Statement::Declare { type_, var, .. } => allocator
                .text(type_.type_of().to_string())
                .append(allocator.space())
                .append(var.to_string())
                .append(semicolon()),
            Statement::Assign { lhs, rhs, .. } => lhs
                .pretty(allocator)
                .append(allocator.space())
                .append(allocator.text(":="))
                .append(allocator.space())
                .append(rhs.pretty(allocator))
                .append(allocator.text(";")),
            Statement::Call { invocation, .. } => invocation.pretty(allocator).append(semicolon()),
            Statement::Skip => allocator.text(";"),
            Statement::Assert { assertion, .. } => allocator
                .text("assert")
                .append(assertion.pretty(allocator))
                .append(semicolon()),
            Statement::Assume { assumption, .. } => allocator
                .text("assume")
                .append(assumption.pretty(allocator))
                .append(semicolon()),
            Statement::While { guard, body, .. } => allocator
                .text("while")
                .append(allocator.space())
                .append(guard.pretty(allocator).parens())
                .append(body.pretty(allocator).braces()),
            Statement::Ite {
                guard,
                true_body,
                false_body,
                ..
            } => allocator.text("if").append(allocator.space()).append(guard.pretty(allocator).parens())
            .append(allocator.space())
            .append(
                allocator.text("{")
            ).append(allocator.line())
            .append(allocator.)
            Statement::Continue { info } => todo!(),
            Statement::Break { info } => todo!(),
            Statement::Return { expression, info } => todo!(),
            Statement::Throw { message, info } => todo!(),
            Statement::Try {
                try_body,
                catch_body,
                info,
            } => todo!(),
            Statement::Block { body } => todo!(),
            Statement::Seq { stat1, stat2 } => todo!(),
        }
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &Lhs {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        todo!()
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &Rhs {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        todo!()
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &Invocation {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        todo!()
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
