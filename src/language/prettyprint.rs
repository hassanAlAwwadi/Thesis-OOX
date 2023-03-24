use std::rc::Rc;

use pom::set::Set;
use pretty::{docs, Arena, BoxAllocator, DocAllocator, DocBuilder};

// use super::{BinOp, Expression};

use crate::{lexer::tokens, parser::expression, syntax::Identifier, typeable::Typeable};

use super::syntax::*;


impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &'a CompilationUnit {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        todo!()
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &'a DeclarationMember {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        match self {
            DeclarationMember::Constructor(method) => pretty_constructor(method, allocator),
            DeclarationMember::Method(method) => method.pretty(allocator),
            DeclarationMember::Field { type_, name, info } => {
                docs![
                    allocator,
                    type_.type_of().pretty(allocator),
                    " ",
                    name.to_string(),
                    ";"
                ]
            },
        }
    }
}

fn pretty_constructor<'a, D: DocAllocator<'a>>(method: &'a Method, allocator: &'a D) -> DocBuilder<'a, D, ()> {
    use pretty::Pretty;
    let body = method.body.borrow();
    docs![
        allocator,
        method.name.to_string(),
        " ",
        pretty_parameters(&method.params, allocator),
        " {",
        allocator.hardline(),
        body.pretty(allocator),
        allocator.hardline(),
        "}"

    ]
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &'a Method {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        let body = self.body.borrow();
        docs![
            allocator,
            if self.is_static { "static" } else { "" },
            " ",
            self.name.to_string(),
            " ",
            pretty_parameters(&self.params, allocator),
            " {",
            allocator.hardline(),
            body.pretty(allocator),
            allocator.hardline(),
            "}"

        ]
    }
}

fn pretty_parameters<'a, D: DocAllocator<'a>>(parameters: &'a Vec<Parameter>, allocator: &'a D) -> DocBuilder<'a, D, ()> {
    use pretty::Pretty;
    let mut parameters = parameters.iter();
    if let Some(parameter) = parameters.next() {
        let mut parameters_text = parameter.pretty(allocator);
        for parameter in parameters {
            parameters_text = parameters_text.append(", ").append(parameter.pretty(allocator));
        }
        return parameters_text.parens();
    }
    allocator.nil().parens()

}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &'a Parameter {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        docs![
            allocator,
            self.type_of(),
            " ",
            self.name.to_string()
        ]
    }
}

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
            } => allocator
                .text("if")
                .append(allocator.space())
                .append(guard.pretty(allocator).parens())
                .append(allocator.space())
                .append(allocator.text("{"))
                .append(allocator.line())
                .append(true_body.pretty(allocator))
                .append(allocator.line())
                .append(allocator.text("}")),
            Statement::Continue { .. } => allocator.text("continue;"),
            Statement::Break { .. } => allocator.text("break;"),
            Statement::Return { expression, .. } => {
                if let Some(expression) = expression {
                    allocator
                        .text("return")
                        .append(allocator.space())
                        .append(expression.pretty(allocator))
                        .append(semicolon())
                } else {
                    allocator.text("return;")
                }
            }
            Statement::Throw { message, .. } => allocator
                .text("throw")
                .append(allocator.text(message.to_string()).double_quotes())
                .append(semicolon()),
            Statement::Try {
                try_body,
                catch_body,
                ..
            } => allocator
                .text("try")
                .append(allocator.space())
                .append(try_body.pretty(allocator).braces())
                .append(allocator.space())
                .append(allocator.text("catch"))
                .append(allocator.space())
                .append(catch_body.pretty(allocator).braces()),
            Statement::Block { body } => body.pretty(allocator),
            Statement::Seq { stat1, stat2 } => stat1
                .pretty(allocator)
                .append(allocator.text(";"))
                .append(allocator.hardline())
                .append(stat2.pretty(allocator)),
        }
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &Lhs {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        match self {
            Lhs::LhsVar { var, .. } => allocator.text(var.to_string()),
            Lhs::LhsField {
                var,
                field,..
            } => allocator.text(format!("{}.{}", var, field)),
            Lhs::LhsElem {
                var,
                index, ..
            } => allocator
                .text(var.to_string())
                .append(index.pretty(allocator).brackets()),
        }
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &Rhs {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        match self {
            Rhs::RhsExpression { value, type_, info } => value.pretty(allocator),
            Rhs::RhsField {
                var,
                field,
                type_,
                info,
            } => var.pretty(allocator),
            Rhs::RhsElem {
                var,
                index,
                type_,
                info,
            } => var
                .pretty(allocator)
                .append(index.pretty(allocator).brackets()),
            Rhs::RhsCall {
                invocation,
                type_,
                info,
            } => invocation.pretty(allocator),
            Rhs::RhsArray {
                array_type,
                sizes,
                type_,
                info,
            } => {
                let mut result = type_.pretty(allocator);
                for size in sizes {
                    result = result.append(size.pretty(allocator).brackets());
                }
                result
            }
        }
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &Invocation {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        match self {
            Invocation::InvokeMethod {
                lhs,
                rhs,
                arguments,
                resolved,
                info,
            } => {
                let mut result = allocator
                    .text(lhs.to_string())
                    .append(allocator.text("."))
                    .append(allocator.text(rhs.to_string()));
                result.append(pretty_arguments(arguments, allocator))
            }
            Invocation::InvokeSuperMethod {
                rhs,
                arguments,
                resolved,
                info,
            } => {
                let mut result = allocator
                    .text("super")
                    .append(allocator.text("."))
                    .append(allocator.text(rhs.to_string()));
                
                    result.append(pretty_arguments(arguments, allocator))
            },
            Invocation::InvokeConstructor {
                class_name,
                arguments,
                resolved,
                info,
            } => {
                let mut result = allocator
                    .text(class_name.to_string());
                result.append(pretty_arguments(arguments, allocator))
            },
            Invocation::InvokeSuperConstructor {
                arguments,
                resolved,
                info,
            } => {
                let mut result = allocator
                    .text("super");
                result.append(pretty_arguments(arguments, allocator))
            },
        }
    }
}

fn pretty_arguments<'a, D: DocAllocator<'a>>(arguments: &Vec<Rc<Expression>>, allocator: &'a D) -> DocBuilder<'a, D, ()> {
    use pretty::Pretty;
    let mut arguments = arguments.iter();
    if let Some(arg) = arguments.next() {
        
        let mut arguments_text = arg.pretty(allocator);
        for arg in arguments {
            arguments_text = arguments_text.append(", ").append(arg.pretty(allocator));
        }
        return arguments_text.parens();
    }
    allocator.nil().parens()
}


impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for RuntimeType {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        (&self).pretty(allocator)
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &RuntimeType {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        allocator.text(self.to_string())
    }
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
