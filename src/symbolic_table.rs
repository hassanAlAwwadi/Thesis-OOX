use std::collections::HashMap;

use crate::syntax::{Identifier, NonVoidType, CompilationUnit, Declaration, DeclarationMember};

pub type Fields = Vec<(Identifier, NonVoidType)>;

pub struct SymbolicTable {
    pub class_to_fields: HashMap<String, Fields>
}

impl SymbolicTable {
    pub fn from_ast(compilation_unit: &CompilationUnit) -> SymbolicTable {
        let mut class_to_fields = HashMap::new();
        for member in &compilation_unit.members {
            let Declaration::Class {name: class_name, members, .. } = member.as_ref();
            let mut fields = Vec::new();
            for declaration_member in  members {
                match declaration_member {
                    DeclarationMember::Field { type_, name } => fields.push((name.to_owned(), type_.to_owned())),
                    _ => ()
                };
            }
            class_to_fields.insert(class_name.clone(), fields);
        }
        
        SymbolicTable { class_to_fields }
    }


    pub fn get_all_fields(&self, class_name: &str) -> &Fields {
        &self.class_to_fields[class_name]
    }
}
