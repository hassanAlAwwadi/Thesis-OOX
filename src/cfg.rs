// use std::intrinsics::unreachable;

use std::collections::HashMap;

use itertools::Itertools;
use std::hash::Hash;

use crate::{lexer::tokens, parser_pom::parse, syntax::*};

const EXCEPTIONAL_STATE_LABEL: u64 = u64::MAX;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CFGStatement {
    Statement(Statement), // without Seq
    Ite(Expression, u64, u64),
    While(Expression, u64),
    TryCatch(u64, u64, u64, u64), // l1: entry try body, l2: exit try body, l3: entry catch body, l4: exit catch body
    Seq(u64, u64),
    FunctionEntry(String),
    FunctionExit(String),
}

pub fn labelled_statements(
    compilation_unit: CompilationUnit,
    i: &mut u64,
) -> (Vec<(u64, CFGStatement)>, Vec<(u64, u64)>) {
    let mut labelled_statements: Vec<(u64, CFGStatement)> = vec![];
    let mut flow: Vec<(u64, u64)> = vec![];

    for Declaration::Class { name, members } in compilation_unit.members {
        for member in members {
            let (mut member_statements, mut member_flow) = memberCFG(member, i);
            labelled_statements.append(&mut member_statements);
            flow.append(&mut member_flow);
        }
    }

    return (labelled_statements, flow);
}

fn memberCFG(
    member: DeclarationMember,
    i: &mut u64,
) -> (Vec<(u64, CFGStatement)>, Vec<(u64, u64)>) {
    let mut labelled_statements: Vec<(u64, CFGStatement)> = vec![];
    match member {
        DeclarationMember::Constructor {
            name,
            params,
            specification,
            body,
        } => {
            labelled_statements.push((*i, CFGStatement::FunctionEntry(name.clone())));
            *i += 1;
            labelled_statements.append(&mut statementCFG(&body, i));
            labelled_statements.push((*i, CFGStatement::FunctionExit(name)));
            *i += 1;
            (Vec::new(), Vec::new())
        }
        DeclarationMember::Method {
            is_static,
            return_type,
            name,
            params,
            specification,
            body,
        } => {
            let mut v = Vec::new();
            v.push((*i, CFGStatement::FunctionEntry(name.clone())));
            let entry_label = *i;
            *i += 1;
            v.append(&mut statementCFG(&body, i));
            v.push((*i, CFGStatement::FunctionExit(name)));
            let exit_label = *i;
            *i += 1;

            let init_l = init(&v[1]);
            let init = (init_l, lookup(init(&v[1]), &v));
            let mut flw = flow(&v[1], &v);

            flw.push((entry_label, init.0));

            // //dbg!(&v[1]);
            // final(S)
            for l in r#final(&v[1], &v) {
                flw.push((l, exit_label));
            }
            // fallthrough(S)
            // //dbg!(&fallthrough(&v[1], &v));
            for (l, _s) in fallthrough(&v[1], &v) {
                flw.push((l, exit_label));
            }

            labelled_statements.append(&mut v);
            (labelled_statements, flw)
        }
        DeclarationMember::Field { type_, name } => (Vec::new(), Vec::new()),
    }
}

fn statementCFG(statement: &Statement, i: &mut u64) -> Vec<(u64, CFGStatement)> {
    let mut labelled_statements: Vec<(u64, CFGStatement)> = vec![];
    match statement {
        Statement::Seq { stat1, stat2 } => {
            let mut v = vec![];
            let seq_l = *i;
            *i += 1;
            let s1_l = *i;
            v.append(&mut statementCFG(stat1.as_ref(), i));
            *i += 1;
            let s2_l = *i;
            v.append(&mut statementCFG(stat2.as_ref(), i));

            labelled_statements.push((seq_l, CFGStatement::Seq(s1_l, s2_l)));
            labelled_statements.append(&mut v);
        }
        Statement::Ite {
            guard,
            true_body,
            false_body,
        } => {
            let mut v = vec![];
            let ite_l = *i;
            *i += 1;
            let i_true = *i;
            v.append(&mut statementCFG(true_body.as_ref(), i));
            let i_false = *i;
            v.append(&mut statementCFG(false_body.as_ref(), i));
            labelled_statements.push((ite_l, CFGStatement::Ite(guard.clone(), i_true, i_false)));
            labelled_statements.append(&mut v);
        }
        Statement::While { guard, body } => {
            let ite_l = *i;
            *i += 1;
            let i_body = *i;

            labelled_statements.push((ite_l, CFGStatement::While(guard.clone(), i_body)));
            labelled_statements.append(&mut statementCFG(body.as_ref(), i));
        }
        Statement::Block { body } => {
            labelled_statements.append(&mut statementCFG(body.as_ref(), i));
        },
        Statement::Try { try_body, catch_body } => {
            let try_catch_l = *i;
            *i += 1;
            let l1 = *i;
            let mut s_1 = statementCFG(&try_body, i);
            *i += 1;
            let l2 = *i;
            *i += 1;

            let l3 = *i;
            let mut s_2 = statementCFG(&catch_body, i);
            *i += 1;
            let l4 = *i;
            *i += 1;

            labelled_statements.push((try_catch_l, CFGStatement::TryCatch(l1, l2, l3, l4))); // make sure this is first
            labelled_statements.append(&mut s_1);
            labelled_statements.append(&mut s_2);

        }
        // Statement::Call { invocation: Invocation::InvokeMethod { lhs, rhs, arguments, resolved } }
        _ => {
            labelled_statements.push((*i, CFGStatement::Statement(statement.clone())));
            *i += 1;
        }
    }

    labelled_statements
}

fn init((l, stmt): &(u64, CFGStatement)) -> u64 {
    *match stmt {
        CFGStatement::Statement(Statement::Declare { .. }) => l,
        CFGStatement::Statement(Statement::Assign { .. }) => l,
        CFGStatement::Statement(Statement::Call { .. }) => l,
        CFGStatement::Statement(Statement::Skip { .. }) => l,
        CFGStatement::Statement(Statement::Assert { .. }) => l,
        CFGStatement::Statement(Statement::Assume { .. }) => l,
        CFGStatement::Statement(Statement::Continue { .. }) => l,
        CFGStatement::Statement(Statement::Break { .. }) => l,
        CFGStatement::Statement(Statement::Return { .. }) => l,
        CFGStatement::Statement(Statement::Throw { .. }) => l,
        CFGStatement::Statement(Statement::Ite { .. }) => unreachable!(),
        CFGStatement::Statement(Statement::Block { .. }) => {
            unreachable!("Block is not a CFGStatement")
        }
        CFGStatement::Statement(Statement::Seq { .. }) => {
            unreachable!("Block is not a CFGStatement")
        }
        CFGStatement::Statement(s) => unreachable!("{:?} is not a CFGStatement", s),
        CFGStatement::Ite(_, _, _) => l,
        CFGStatement::Seq(l1, _) => l1, // could technically be a seq too but nah
        CFGStatement::While(_, _) => l,
        CFGStatement::TryCatch(_, _, _, _) => l,
        CFGStatement::FunctionEntry(_) => unreachable!(),
        CFGStatement::FunctionExit(_) => unreachable!(),
    }
}

fn fallthrough(
    s_l @ (_l, stmt): &(u64, CFGStatement),
    all_smts: &Vec<(u64, CFGStatement)>,
) -> Vec<(u64, CFGStatement)> {
    // //dbg!(&s_l);
    match stmt {
        CFGStatement::Statement(Statement::Break { .. }) => vec![s_l.clone()],
        CFGStatement::Statement(Statement::Continue { .. }) => vec![s_l.clone()],
        CFGStatement::Statement(Statement::Return { .. }) => vec![s_l.clone()],
        CFGStatement::Statement(_) => vec![],
        CFGStatement::Ite(_, l1, l2) => {
            let final_s1 = fallthrough(&(*l1, lookup(*l1, all_smts)), all_smts);
            let mut final_s2 = fallthrough(&(*l2, lookup(*l2, all_smts)), all_smts);

            let mut v = final_s1;
            v.append(&mut final_s2);

            v
        }
        CFGStatement::Seq(l1, l2) => {
            let s1 = lookup(*l1, all_smts);
            let s2 = lookup(*l2, all_smts);
            // if let
            let final_s1 = fallthrough(&(*l1, s1), all_smts);
            let mut final_s2 = fallthrough(&(*l2, s2), all_smts);

            let mut v = final_s1;
            v.append(&mut final_s2);

            v
        }
        CFGStatement::While(_, l_body) => {
            let fallthrough_body = fallthrough(&(*l_body, lookup(*l_body, all_smts)), all_smts);

            fallthrough_body
                .into_iter()
                .filter(|(l, s)| match s {
                    CFGStatement::Statement(Statement::Continue) => false,
                    CFGStatement::Statement(Statement::Break) => false,
                    _ => true,
                })
                .collect()
        },
        CFGStatement::TryCatch(_, _, _, _) => Vec::new(),
        CFGStatement::FunctionEntry(_) => todo!(),
        CFGStatement::FunctionExit(_) => todo!(),
    }
}

fn lookup(i: u64, stmts: &Vec<(u64, CFGStatement)>) -> CFGStatement {
    stmts
        .iter()
        .find_map(|(idx, s)| if *idx == i { Some(s.clone()) } else { None })
        .unwrap()
    // let x = stmts.iter().find(|(idx, s)| *idx == i);

    // todo!()
}

fn r#final((l, stmt): &(u64, CFGStatement), all_smts: &Vec<(u64, CFGStatement)>) -> Vec<u64> {
    match stmt {
        CFGStatement::Statement(Statement::Declare { .. }) => vec![*l],
        CFGStatement::Statement(Statement::Assign { .. }) => vec![*l], //note
        CFGStatement::Statement(Statement::Call { .. }) => vec![*l],   //note
        CFGStatement::Statement(Statement::Skip { .. }) => vec![*l],
        CFGStatement::Statement(Statement::Assert { .. }) => vec![*l],
        CFGStatement::Statement(Statement::Assume { .. }) => vec![*l],
        CFGStatement::Statement(Statement::Continue { .. }) => Vec::new(),
        CFGStatement::Statement(Statement::Break { .. }) => Vec::new(),
        CFGStatement::Statement(Statement::Return { .. }) => Vec::new(),
        CFGStatement::Statement(Statement::Throw { .. }) => Vec::new(),
        CFGStatement::Statement(Statement::Ite { .. }) => unreachable!(),
        CFGStatement::Statement(Statement::Block { .. }) => {
            unreachable!("Block is not a CFGStatement")
        }
        CFGStatement::Statement(Statement::Seq { .. }) => {
            unreachable!("Seq is not a CFGStatement")
        }
        CFGStatement::Statement(s) => unreachable!("{:?} is not a CFGStatement", s),
        CFGStatement::Ite(_, s1, s2) => {
            let mut final_s1 = r#final(&(*s1, lookup(*s1, all_smts)), all_smts);
            let mut final_s2 = r#final(&(*s2, lookup(*s2, all_smts)), all_smts);
            final_s1.append(&mut final_s2);

            //dbg!(s1, s2, &final_s1);
            final_s1
        }
        CFGStatement::Seq(l1, l2) => {
            let s1 = lookup(*l1, all_smts);
            let final_s2 = r#final(&(*l2, lookup(*l2, all_smts)), all_smts);
            match s1 {
                CFGStatement::Statement(Statement::Continue) => Vec::new(),
                CFGStatement::Statement(Statement::Break) => Vec::new(),
                CFGStatement::Statement(Statement::Return { .. }) => Vec::new(),
                CFGStatement::Statement(Statement::Throw { .. }) => Vec::new(),
                CFGStatement::Statement(_) => final_s2,
                CFGStatement::FunctionEntry(_) => unreachable!(),
                CFGStatement::FunctionExit(_) => unreachable!(),
                CFGStatement::Ite(_, _, _) => final_s2,
                CFGStatement::While(_, _) => final_s2,
                CFGStatement::TryCatch(_, _, _, _) => final_s2,
                CFGStatement::Seq(_, _) => unreachable!("No seq in l1"),
            }
        }
        CFGStatement::While(_, l_body) => {
            let mut v = fallthrough(&(*l_body, lookup(*l_body, all_smts)), all_smts)
                .into_iter()
                .filter_map(|(l, s)| match s {
                    CFGStatement::Statement(Statement::Break) => Some(l),
                    _ => None,
                })
                .collect::<Vec<_>>();
            v.push(*l);
            //dbg!(&v);
            v
        },
        CFGStatement::TryCatch(_, l2, _, l4) => {
            vec![*l2, *l4]
        }, // could lookup finals of l1 and l3 instead of having l3 & l4?
        CFGStatement::FunctionEntry(_) => unreachable!(),
        CFGStatement::FunctionExit(_) => unreachable!(),
    }
}

fn flow((l, stmt): &(u64, CFGStatement), all_smts: &Vec<(u64, CFGStatement)>) -> Vec<(u64, u64)> {
    match stmt {
        CFGStatement::Statement(Statement::Declare { .. }) => Vec::new(),
        CFGStatement::Statement(Statement::Assign { .. }) => Vec::new(), // to be fixed?
        CFGStatement::Statement(Statement::Call { .. }) => Vec::new(),   // to be fixed?
        CFGStatement::Statement(Statement::Skip { .. }) => Vec::new(),
        CFGStatement::Statement(Statement::Assert { .. }) => Vec::new(),
        CFGStatement::Statement(Statement::Assume { .. }) => Vec::new(),
        CFGStatement::Statement(Statement::Continue) => Vec::new(),
        CFGStatement::Statement(Statement::Break) => Vec::new(),
        CFGStatement::Statement(Statement::Return { .. }) => Vec::new(),
        CFGStatement::Statement(Statement::Throw { .. }) => Vec::new(),
        CFGStatement::Statement(Statement::Try { .. }) => Vec::new(), // to be fixed
        CFGStatement::Statement(_) => unreachable!("block, ite and seq and while are not covered"),
        CFGStatement::Ite(_, l1, l2) => {
            let s1 = (*l1, lookup(*l1, all_smts));
            let s2 = (*l2, lookup(*l2, all_smts));
            let flow_s1 = flow(&s1, all_smts);
            let mut flow_s2 = flow(&s2, all_smts);
            let mut v = flow_s1;
            v.append(&mut flow_s2);
            v.push((*l, init(&s1)));
            v.push((*l, init(&s2)));

            v
        }
        CFGStatement::Seq(l1, l2) => {
            let s1 = (*l1, lookup(*l1, all_smts));
            let s2 = (*l2, lookup(*l2, all_smts));

            let mut v = flow(&s1, all_smts);
            v.append(&mut flow(&s2, all_smts));

            let init_s2 = init(&s2);
            for l_f in r#final(&s1, all_smts) {
                v.push((l_f, init_s2));
            }

            v
        }
        CFGStatement::While(_, l_body) => {
            let s_l = (*l_body, lookup(*l_body, all_smts));
            let mut v = flow(&s_l, all_smts);
            v.push((*l, init(&s_l)));

            for l_f in r#final(&s_l, all_smts) {
                v.push((l_f, *l));
            }

            for (l_continue, _) in
                fallthrough(&s_l, all_smts)
                    .into_iter()
                    .filter(|(_, s)| match s {
                        CFGStatement::Statement(Statement::Continue) => true,
                        _ => false,
                    })
            {
                v.push((l_continue, *l));
            }

            v
        },
        CFGStatement::TryCatch(l1, l2, l3, l4) => {
            let s1_l = (*l1, lookup(*l1, all_smts)); // starting labelled statement in try { .. }
            let mut v = vec![(*l, init(&s1_l))];  // from try statement to try body
            v.append(&mut flow(&s1_l, all_smts));

            let s2_l = (*l3, lookup(*l3, all_smts));
            v.append(&mut flow(&s2_l, all_smts));

            v.push((*l3, init(&s2_l))); // from catch statement to catch body

            for l_f in r#final(&s1_l, all_smts) { // why can't i just make the 
                v.push((l_f, *l2));
            }

            for l_f in r#final(&s2_l, all_smts) {
                v.push((l_f, *l4));
            }
            v
        }
        CFGStatement::FunctionEntry(_) => todo!(),
        CFGStatement::FunctionExit(_) => todo!(), // to be fixed?
    }
}

#[test]
fn cfg_for_simpleclass() {
    let file_content = include_str!("../examples/simpleclass.oox");

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();
    // //dbg!(as_ref);
    let c = parse(&tokens);
    let c = c.unwrap();
    // //dbg!(&c);

    let mut i = 0;
    let (result, flw) = labelled_statements(c, &mut i);
    // //dbg!(&result);

    // //dbg!(&flw);

    let expected = vec![
        (9, 11),
        (25, 27),
        (22, 25),
        (19, 22),
        (16, 19),
        (13, 16),
        (7, 9),
        (7, 13),
        (5, 7),
        (2, 5),
        (0, 2),
        (11, 28),
        (27, 28),
    ];

    assert_eq!(expected, flw);
}

#[test]
fn cfg_for_simpleclass2() {
    let file_content = include_str!("../examples/simpleclass2.oox");

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();

    let c = parse(&tokens);
    let c = c.unwrap();

    // //dbg!(&c);

    let mut i = 0;
    let (result, flw) = labelled_statements(c, &mut i);

    //dbg!(&result);

    //dbg!(&flw);
    let expected = vec![
        (36, 38),
        (33, 36),
        (31, 33),
        (31, 39),
        (38, 41),
        (39, 41),
        (28, 31),
        (25, 28),
        (22, 25),
        (20, 22),
        (41, 20),
        (44, 46),
        (20, 44),
        (17, 20),
        (14, 17),
        (11, 14),
        (8, 11),
        (5, 8),
        (2, 5),
        (0, 2),
        (46, 47),
    ];

    assert_eq!(expected, flw);
}

#[test]
fn cfg_for_simpleclass3() {
    let file_content = include_str!("../examples/simpleclass3.oox");

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();

    let c = parse(&tokens);
    let c = c.unwrap();

    // //dbg!(&c);

    let mut i = 0;
    let (result, flw) = labelled_statements(c, &mut i);

    //dbg!(&result);

    //dbg!(&flw);
    let expected = vec![
        (39, 41),
        (36, 39),
        (33, 36),
        (31, 33),
        (31, 42),
        (42, 44),
        (28, 31),
        (25, 28),
        (22, 25),
        (20, 22),
        (44, 20),
        (47, 49),
        (41, 47),
        (20, 47),
        (17, 20),
        (14, 17),
        (11, 14),
        (8, 11),
        (5, 8),
        (2, 5),
        (0, 2),
        (49, 50),
    ];

    assert_eq!(expected, flw);
}

#[test]
fn cfg_for_simpleclass4() {
    let file_content = include_str!("../examples/simpleclass4.oox");

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();

    let c = parse(&tokens);
    let c = c.unwrap();

    // //dbg!(&c);

    let mut i = 0;
    let (result, flw) = labelled_statements(c, &mut i);

    //dbg!(&result);

    //dbg!(&flw);
    let expected = vec![
        (39, 41),
        (36, 39),
        (33, 36),
        (31, 33),
        (31, 42),
        (42, 44),
        (28, 31),
        (25, 28),
        (22, 25),
        (20, 22),
        (44, 20),
        (41, 20),
        (47, 49),
        (20, 47),
        (17, 20),
        (14, 17),
        (11, 14),
        (8, 11),
        (5, 8),
        (2, 5),
        (0, 2),
        (49, 50),
    ];

    assert_eq!(expected, flw);
}

#[test]
fn cfg_for_min() {
    let file_content = include_str!("../examples/psv/min.oox");

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();

    let c = parse(&tokens);
    let c = c.unwrap();

    // //dbg!(&c);

    let mut i = 0;
    let (result, flw) = labelled_statements(c, &mut i);

    // //dbg!(&result);

    // //dbg!(&flw);
    let expected = vec![
        (10, 12),
        (14, 16),
        (8, 10),
        (8, 14),
        (12, 18),
        (16, 18),
        (5, 8),
        (2, 5),
        (0, 2),
        (18, 19),
    ];

    assert_eq!(expected, flw);
}

#[test]
fn cfg_for_test() {
    let file_content = include_str!("../examples/psv/test.oox");

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();

    let c = parse(&tokens);
    let c = c.unwrap();

    // //dbg!(&c);

    let mut i = 0;
    let (result, flw) = labelled_statements(c, &mut i);

    // //dbg!(&result);

    // //dbg!(&flw);
    let expected = vec![
        (17, 19),
        (15, 17),
        (15, 20),
        (13, 15),
        (10, 13),
        (8, 10),
        (19, 8),
        (20, 8),
        (23, 25),
        (8, 23),
        (5, 8),
        (2, 5),
        (0, 2),
        (25, 26),
    ];

    assert_eq!(expected, flw);
}


#[test]
fn cfg_for_try_catch() {
    let file_content = include_str!("../examples/simple_try_catch.oox");

    let tokens = tokens(file_content);
    let as_ref = tokens.as_slice();

    let c = parse(&tokens);
    let c = c.unwrap();

    // dbg!(&c);

    let mut i = 0;
    let (result, flw) = labelled_statements(c, &mut i);

    dbg!(&result);

    // //dbg!(&flw);
    let expected = vec![
        (17, 19),
        (15, 17),
        (15, 20),
        (13, 15),
        (10, 13),
        (8, 10),
        (19, 8),
        (20, 8),
        (23, 25),
        (8, 23),
        (5, 8),
        (2, 5),
        (0, 2),
        (25, 26),
    ];

    assert_eq!(expected, flw);
}
