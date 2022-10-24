use crate::{syntax::*, lexer::tokens, parser_pom::parse};

#[derive(Debug)]
enum CFGStatement {
    Statement(Statement), // without Seq
    FunctionEntry(String),
    FunctionExit(String),
}


fn init(compilation_unit: CompilationUnit, i: &mut u64) -> Vec<(u64, CFGStatement)> {
    let mut labelled_statements: Vec<(u64, CFGStatement)> = vec![];

    for Declaration::Class { name, members } in compilation_unit.members {
        for member in members {
            labelled_statements.append(&mut memberCFG(member, i));
        }
    }

    return labelled_statements;
}


fn memberCFG(member: DeclarationMember, i: &mut u64) -> Vec<(u64, CFGStatement)> {
    let mut labelled_statements: Vec<(u64, CFGStatement)> = vec![];
    match member {
        DeclarationMember::Constructor { name, params, specification, body } => {
            labelled_statements.push((*i, CFGStatement::FunctionEntry(name)));
            *i += 1;
            labelled_statements.append(&mut statementCFG(&body, i));
        },
        DeclarationMember::Method { is_static, return_type, name, params, specification, body } => {
            labelled_statements.push((*i, CFGStatement::FunctionEntry(name)));
            *i += 1;
            labelled_statements.append(&mut statementCFG(&body, i));
        },
        DeclarationMember::Field { type_, name } => (),
    }
    return labelled_statements;
}

fn statementCFG(statement: &Statement, i: &mut u64) -> Vec<(u64, CFGStatement)> {
    let mut labelled_statements: Vec<(u64, CFGStatement)> = vec![];
    match statement {
        
        Statement::Seq { stat1, stat2 } => {
            labelled_statements.append(&mut statementCFG(stat1.as_ref(), i));
            labelled_statements.append(&mut statementCFG(stat2.as_ref(), i));
        },
        Statement::
        _ => {
            labelled_statements.push((*i, CFGStatement::Statement(statement.clone())));
            *i += 1;
        }
    }

    labelled_statements
}



#[test]
fn feature() {
    let file_content = include_str!("../examples/simpleclass.oox");

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    // dbg!(as_ref);
    let c = parse(&tokens);
    let c = c.unwrap();

    let mut i = 0;
    let result = init(c, &mut i);

    dbg!(&result);

    // assert!(false);
}