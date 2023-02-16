use crate::syntax::{Identifier, RuntimeType, Expression};


pub fn shadowing(var1: Identifier, var2: Identifier) -> String {
    format!("Variable '{}' shadows variable '{}'", var1, var2)
}

pub fn undeclared_var(var: &Identifier) -> String {
    format!("Undeclared variable: {}", var)
}

pub fn unification_error(expected: RuntimeType, actual: RuntimeType) -> String {
    format!("Expected type {} but is of type {}", expected, actual)
}

pub fn unresolved_field_error(class_name: &str, field: &str) -> String {
    format!("Unable to resolve field '{}' of class '{}'", class_name, field)
}

pub fn unexpected_return_value(expression: &Expression) -> String {
    format!("Expected a return statement without an expression, instead 'return {:?}'", expression)
}

pub fn expected_return_value_error(expected_type: RuntimeType) -> String {
    format!("Expected a return statement with an expression of type '{}', instead no expression was given", expected_type)
}