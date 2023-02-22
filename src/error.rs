use crate::{syntax::{Expression, Identifier, RuntimeType}, positioned::SourcePos};

pub fn shadowing(var1: &Identifier, var2: &Identifier, info: SourcePos) -> String {
    format!("Variable '{}' shadows variable '{}', {}", var1, var2, info)
}

pub fn undeclared_var(var: &Identifier, info: SourcePos) -> String {
    format!("Undeclared variable: {}, {}", var, info)
}

pub fn unification_error(expected: RuntimeType, actual: RuntimeType, info: SourcePos) -> String {
    format!("Expected type {} but is of type {}, {}", expected, actual, info)
}

pub fn unresolved_field_error(class_name: &Identifier, field: &str, info: SourcePos) -> String {
    format!(
        "Unable to resolve field '{}' of class '{}', {}",
        field, class_name, info
    )
}

pub fn unexpected_return_value(expression: &Expression, info: SourcePos) -> String {
    format!(
        "Expected a return statement without an expression, instead 'return {:?}', {}",
        expression, info
    )
}

pub fn expected_return_value_error(expected_type: RuntimeType, info: SourcePos) -> String {
    format!("Expected a return statement with an expression of type '{}', instead no expression was given, {}", expected_type, info)
}

// Symbol table
pub fn class_does_not_exist(expected_class: &Identifier, info: SourcePos) -> String {
    format!("Cannot find class {}, {}", expected_class, info)
}

pub fn expected_class_found_interface(expected_class: &Identifier, info: SourcePos) -> String {
    format!(
        "Expected declaration {} to be a class, but found an interface. {}",
        expected_class, info
    )
}

pub fn expected_interface_found_class(expected_interface: &Identifier, info: SourcePos) -> String {
    format!(
        "Expected declaration {} to be an interface, but found a class. {}",
        expected_interface, info
    )
}
