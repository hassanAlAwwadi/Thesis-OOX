use std::{fs::read_to_string, rc::Rc};

use itertools::Itertools;
use pom::set::Set;
use pretty::{docs, Arena, BoxAllocator, DocAllocator, DocBuilder};

// use super::{BinOp, Expression};

use crate::{ syntax::Identifier, typeable::Typeable};

use super::syntax::*;

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &'a CompilationUnit {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        docs![
            allocator,
            allocator.concat(self.members.iter().map(|decl| decl.pretty(allocator)))
        ]
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &'a Declaration {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        match self {
            Declaration::Class(class) => {
                docs![
                    allocator,
                    "class ",
                    class.name.to_string(),
                    " ",
                    class
                        .extends
                        .clone()
                        .map(|extends| format!("extends {}", extends)),
                    if class.implements.len() > 0 {
                        if class.extends.is_some() {
                            format!(
                                ", implements {}",
                                class
                                    .implements
                                    .iter()
                                    .map(Identifier::to_string)
                                    .join(", ")
                            )
                        } else {
                            String::new()
                        }
                    } else {
                        String::new()
                    },
                    allocator.softline_(),
                    "{",
                    docs![
                        allocator,
                        allocator.hardline(),
                        allocator.concat(
                            class.members.iter().map(|member| member
                                .pretty(allocator)
                                .append(allocator.hardline()))
                        )
                    ]
                    .nest(2),
                    allocator.hardline(),
                    "}"
                ]
            }
            Declaration::Interface(_) => todo!(),
        }
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
            }
        }
    }
}

fn pretty_constructor<'a, D: DocAllocator<'a>>(
    method: &'a Method,
    allocator: &'a D,
) -> DocBuilder<'a, D, ()> {
    use pretty::Pretty;
    let body = method.body.borrow();
    docs![
        allocator,
        allocator.hardline(),
        method.name.to_string(),
        " ",
        pretty_parameters(&method.params, allocator),
        " {",
        docs![allocator, allocator.hardline(), body.pretty(allocator),].nest(2),
        allocator.hardline(),
        "}"
    ]
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &'a Method {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        let body = self.body.borrow();
        docs![
            allocator,
            allocator.hardline(),
            if self.is_static { "static " } else { "" },
            self.return_type.type_of(),
            " ",
            self.name.to_string(),
            pretty_parameters(&self.params, allocator),
            allocator.space(),
            specifications(&self.specification, allocator),
            "{",
            docs![allocator, allocator.hardline(), body.pretty(allocator),].nest(2),
            allocator.hardline(),
            "}"
        ]
    }
}

fn specifications<'a, D: DocAllocator<'a>>(
    specification: &'a Specification,
    allocator: &'a D,
) -> DocBuilder<'a, D, ()> {
    use pretty::Pretty;
    if !(specification.requires.is_some() || specification.ensures.is_some() || specification.exceptional.is_some()) {
        return allocator.nil();
    }
    
    docs![ // specifications
        allocator,
        specification.requires.clone().map(|requires| 
            docs![
                allocator,
                allocator.hardline(),
                "requires", 
                requires.pretty(allocator).parens(),
            ]
        ),
        specification.ensures.clone().map(|requires| 
            docs![
                allocator,
                allocator.hardline(),
                "ensures", 
                requires.pretty(allocator).parens(),
            ]
        ),
        
        specification.exceptional.clone().map(|requires| 
            docs![
                allocator,
                allocator.hardline(),
                "exceptional", 
                requires.pretty(allocator).parens(),
            ]
        )
    ].nest(2)
    .append(allocator.hardline())
}

fn pretty_parameters<'a, D: DocAllocator<'a>>(
    parameters: &'a Vec<Parameter>,
    allocator: &'a D,
) -> DocBuilder<'a, D, ()> {
    use pretty::Pretty;
    let mut parameters = parameters.iter();
    if let Some(parameter) = parameters.next() {
        let mut parameters_text = parameter.pretty(allocator);
        for parameter in parameters {
            parameters_text = parameters_text
                .append(", ")
                .append(parameter.pretty(allocator));
        }
        return parameters_text.parens();
    }
    allocator.nil().parens()
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &'a Parameter {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        docs![allocator, self.type_of(), " ", self.name.to_string()]
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
            } => docs![
                allocator,
                lhs.pretty(allocator),
                allocator.space(),
                bin_op_to_str(bin_op),
                allocator.space(),
                rhs.pretty(allocator)
            ],

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
            } => docs![
                allocator,
                "ite",
                guard.pretty(allocator).append(comma()),
                true_.pretty(allocator).append(comma()),
                false_.pretty(allocator)
            ]
            .parens(),
            Expression::Forall {
                elem,
                range,
                domain,
                formula,
                ..
            } => docs![
                allocator,
                "forall ",
                elem.to_string(),
                ", ",
                range.to_string(),
                ": ",
                domain.to_string(),
                ": ",
                formula.pretty(allocator)
            ],

            Expression::Exists {
                elem,
                range,
                domain,
                formula,
                ..
            } => docs![
                allocator,
                "exists ",
                elem.to_string(),
                ", ",
                range.to_string(),
                ": ",
                domain.to_string(),
                ": ",
                formula.pretty(allocator)
            ],

            Expression::SymbolicRef { var, .. } => allocator.text(var.to_string()),
        }
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &Statement {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        let semicolon = || allocator.text(";");
        match self {
            Statement::Declare { type_, var, .. } => docs![
                allocator,
                type_.type_of().to_string(),
                " ",
                var.to_string(),
                semicolon()
            ],

            Statement::Assign { lhs, rhs, .. } => docs![
                allocator,
                lhs.pretty(allocator),
                " ",
                ":=",
                " ",
                rhs.pretty(allocator),
                semicolon()
            ],

            Statement::Call { invocation, .. } => invocation.pretty(allocator).append(semicolon()),
            Statement::Skip => allocator.text(";"),
            Statement::Assert { assertion, .. } => docs![
                allocator,
                "assert",
                " ",
                assertion.pretty(allocator),
                semicolon()
            ],

            Statement::Assume { assumption, .. } => docs![
                allocator,
                "assume",
                " ",
                assumption.pretty(allocator),
                semicolon()
            ],
            Statement::While { guard, body, .. } => {
                docs![
                    allocator,
                    "while",
                    " ",
                    guard.pretty(allocator).parens(),
                    " ",
                    "{",
                    docs![allocator, allocator.hardline(), body.pretty(allocator),].nest(2),
                    allocator.hardline(),
                    "}"
                ]
            }

            Statement::Ite {
                guard,
                true_body,
                false_body,
                ..
            } => docs![
                allocator,
                "if",
                " ",
                guard.pretty(allocator).parens(),
                " ",
                "{",
                docs![allocator, allocator.hardline(), true_body.pretty(allocator)].nest(2),
                allocator.hardline(),
                "}"
            ],
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
                .text("throw ")
                .append(allocator.text(message.to_string()).double_quotes())
                .append(semicolon()),
            Statement::Try {
                try_body,
                catch_body,
                ..
            } => docs![
                allocator,
                "try",
                " ",
                try_body.pretty(allocator).braces(),
                " ",
                "catch",
                " ",
                catch_body.pretty(allocator).braces()
            ],

            Statement::Block { body } => body.pretty(allocator),
            Statement::Seq { stat1, stat2 } => docs![
                allocator,
                stat1.as_ref(),
                allocator.hardline(),
                stat2.as_ref()
            ],
        }
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &Lhs {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        match self {
            Lhs::LhsVar { var, .. } => allocator.text(var.to_string()),
            Lhs::LhsField { var, field, .. } => allocator.text(format!("{}.{}", var, field)),
            Lhs::LhsElem { var, index, .. } => allocator
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
            }
            Invocation::InvokeConstructor {
                class_name,
                arguments,
                resolved,
                info,
            } => {
                let mut result = allocator.text(class_name.to_string());
                result.append(pretty_arguments(arguments, allocator))
            }
            Invocation::InvokeSuperConstructor {
                arguments,
                resolved,
                info,
            } => {
                let mut result = allocator.text("super");
                result.append(pretty_arguments(arguments, allocator))
            }
        }
    }
}

fn pretty_arguments<'a, D: DocAllocator<'a>>(
    arguments: &Vec<Rc<Expression>>,
    allocator: &'a D,
) -> DocBuilder<'a, D, ()> {
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
    use crate::{lexer::tokens, parser::expression };
    let tokens = tokens("x && y").unwrap();
    let exp = expression().parse(&tokens).unwrap();
    let allocator = BoxAllocator;
    println!("{}", pretty::Pretty::pretty(&exp, &allocator).1.pretty(10));
}

#[test]
fn pretty_class() {
    use crate::{lexer::tokens, parse };
    let path = "./examples/intLinkedList.oox";
    let file_content = std::fs::read_to_string(path).unwrap();
    let tokens = tokens(&file_content).unwrap();
    let class = parse(&tokens).unwrap();

    let allocator = BoxAllocator;
    println!(
        "{}",
        pretty::Pretty::pretty(&class, &allocator).1.pretty(50)
    );
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
