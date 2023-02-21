// use std::intrinsics::unreachable;

use crate::{lexer::tokens, parser::parse, syntax::*, typeable::Typeable, exec::this_str, positioned::SourcePos};

const EXCEPTIONAL_STATE_LABEL: u64 = u64::MAX;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CFGStatement {
    Statement(Statement), // without Seq
    Ite(Expression, u64, u64),
    While(Expression, u64),
    TryCatch(u64, u64, u64, u64), // l1: entry try body, l2: exit try body, l3: entry catch body, l4: exit catch body
    TryEntry(u64),
    TryExit,
    CatchEntry(u64),
    CatchExit,
    Seq(u64, u64),
    FunctionEntry {
        decl_name: Identifier,
        method_name: Identifier,
    },
    FunctionExit {
        decl_name: Identifier,
        method_name: Identifier,
    },
}

pub fn labelled_statements(
    compilation_unit: CompilationUnit,
    i: &mut u64,
) -> (Vec<(u64, CFGStatement)>, Vec<(u64, u64)>) {
    let mut labelled_statements: Vec<(u64, CFGStatement)> = vec![];
    let mut flow: Vec<(u64, u64)> = vec![];

    for declaration in compilation_unit.members {
        match declaration {
            Declaration::Class(class) => {
                for member in &class.members {
                    let (mut member_statements, mut member_flow) =
                        memberCFG(class.name.clone(), &member, i);
                    labelled_statements.append(&mut member_statements);
                    flow.append(&mut member_flow);
                }
            }
            Declaration::Interface(interface) => {
                for member in &interface.members {
                    let (mut member_statements, mut member_flow) =
                        interface_member_cfg(interface.name.clone(), &member, i);
                    labelled_statements.append(&mut member_statements);
                    flow.append(&mut member_flow);
                }
            }
        }
    }

    return (labelled_statements, flow);
}

fn memberCFG(
    class_name: Identifier,
    member: &DeclarationMember,
    i: &mut u64,
) -> (Vec<(u64, CFGStatement)>, Vec<(u64, u64)>) {
    match member {
        DeclarationMember::Method(method) => label_method(class_name, &method.name, &method.body.borrow(), i),
        DeclarationMember::Constructor(method) => {
            let mut labelled_statements: Vec<(u64, CFGStatement)> = vec![];
            let mut v = Vec::new();
            v.push((
                *i,
                CFGStatement::FunctionEntry {
                    decl_name: class_name.clone(),
                    method_name: method.name.clone(),
                },
            ));
            let entry_label = *i;
            *i += 1;
            v.append(&mut statementCFG(&method.body.borrow(), i));
            // insert `return this;` at the end of the constructor flow.
            v.push((
                *i,
                CFGStatement::Statement(Statement::Return {
                    expression: Expression::Var {
                        var: this_str(),
                        type_: member.type_of(),
                        info: SourcePos::UnknownPosition 
                    }
                    .into(),
                    info: SourcePos::UnknownPosition 
                }),
            ));
            let return_this_label = *i;
            *i += 1;
            v.push((
                *i,
                CFGStatement::FunctionExit {
                    decl_name: class_name,
                    method_name: method.name.clone(),
                },
            ));
            let exit_label = *i;
            *i += 1;

            let init_l = init(&v[1]);
            let init = (init_l, lookup(init(&v[1]), &v));
            let mut flw = flow(&v[1], &v);

            flw.push((entry_label, init.0));

            // //dbg!(&v[1]);
            // final(S)
            for l in r#final(&v[1], &v) {
                flw.push((l, return_this_label));
            }
            // fallthrough(S)
            // //dbg!(&fallthrough(&v[1], &v));
            for (l, _s) in fallthrough(&v[1], &v) {
                flw.push((l, return_this_label));
            }

            // from `return this;` to function exit.
            flw.push((return_this_label, exit_label));

            labelled_statements.append(&mut v);
            (labelled_statements, flw)
        }
        DeclarationMember::Field { .. } => (Vec::new(), Vec::new()),
    }
}

fn interface_member_cfg(
    class_name: Identifier,
    member: &InterfaceMember,
    i: &mut u64,
) -> (Vec<(u64, CFGStatement)>, Vec<(u64, u64)>) {
    match member {
        InterfaceMember::DefaultMethod(method) => {
            label_method(class_name, &method.name, &method.body.borrow(), i)
        }
        InterfaceMember::AbstractMethod(_) => (Vec::new(), Vec::new()),
    }
}

fn label_method(
    class_name: Identifier,
    name: &Identifier,
    body: &Statement,
    i: &mut u64,
) -> (Vec<(u64, CFGStatement)>, Vec<(u64, u64)>) {
    let mut labelled_statements: Vec<(u64, CFGStatement)> = vec![];
    let mut v = Vec::new();
    v.push((
        *i,
        CFGStatement::FunctionEntry {
            decl_name: class_name.clone(),
            method_name: name.clone(),
        },
    ));
    let entry_label = *i;
    *i += 1;
    v.append(&mut statementCFG(&body, i));
    v.push((
        *i,
        CFGStatement::FunctionExit {
            decl_name: class_name,
            method_name: name.clone(),
        },
    ));
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
            info,
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
        Statement::While { guard, body , info } => {
            let ite_l = *i;
            *i += 1;
            let i_body = *i;

            labelled_statements.push((ite_l, CFGStatement::While(guard.clone(), i_body)));
            labelled_statements.append(&mut statementCFG(body.as_ref(), i));
        }
        Statement::Block { body } => {
            labelled_statements.append(&mut statementCFG(body.as_ref(), i));
        }
        Statement::Try {
            try_body,
            catch_body,
            info
        } => {
            let try_catch_l = *i;
            *i += 1;
            let l1 = *i;
            *i += 1;
            let s1_l = *i;
            let mut s_1 = statementCFG(&try_body, i);
            *i += 1;
            let l2 = *i;
            *i += 1;

            let l3 = *i;
            *i += 1;
            let s2_l = *i;
            let mut s_2 = statementCFG(&catch_body, i);
            *i += 1;
            let l4 = *i;
            *i += 1;

            labelled_statements.push((try_catch_l, CFGStatement::TryCatch(l1, l2, l3, l4))); // make sure this is first
            labelled_statements.push((l1, CFGStatement::TryEntry(s1_l))); // make sure this is first
            labelled_statements.push((l2, CFGStatement::TryExit)); // make sure this is first
            labelled_statements.push((l3, CFGStatement::CatchEntry(s2_l))); // make sure this is first
            labelled_statements.push((l4, CFGStatement::CatchExit)); // make sure this is first
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
        CFGStatement::TryEntry(_) => l,
        CFGStatement::TryExit => l,
        CFGStatement::CatchEntry(_) => l,
        CFGStatement::CatchExit => l,
        CFGStatement::FunctionEntry { .. } => unreachable!(),
        CFGStatement::FunctionExit { .. } => unreachable!(),
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
                    CFGStatement::Statement(Statement::Continue { .. }) => false,
                    CFGStatement::Statement(Statement::Break { .. }) => false,
                    _ => true,
                })
                .collect()
        }
        CFGStatement::TryCatch(_, _, _, _) => Vec::new(),
        CFGStatement::TryEntry(_) => Vec::new(),
        CFGStatement::TryExit => Vec::new(),
        CFGStatement::CatchEntry(_) => Vec::new(),
        CFGStatement::CatchExit => Vec::new(),
        CFGStatement::FunctionEntry { .. } => todo!(),
        CFGStatement::FunctionExit { .. } => todo!(),
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
                CFGStatement::Statement(Statement::Continue { .. }) => Vec::new(),
                CFGStatement::Statement(Statement::Break { .. }) => Vec::new(),
                CFGStatement::Statement(Statement::Return { .. }) => Vec::new(),
                CFGStatement::Statement(Statement::Throw { .. }) => Vec::new(),
                CFGStatement::Statement(_) => final_s2,
                CFGStatement::FunctionEntry { .. } => unreachable!(),
                CFGStatement::FunctionExit { .. } => unreachable!(),
                CFGStatement::Ite(_, _, _) => final_s2,
                CFGStatement::While(_, _) => final_s2,
                CFGStatement::TryCatch(_, _, _, _) => final_s2,
                CFGStatement::Seq(_, _) => unreachable!("No seq in l1"),
                CFGStatement::TryEntry(_) => final_s2,
                CFGStatement::TryExit => final_s2,
                CFGStatement::CatchEntry(_) => final_s2,
                CFGStatement::CatchExit => final_s2,
            }
        }
        CFGStatement::While(_, l_body) => {
            let mut v = fallthrough(&(*l_body, lookup(*l_body, all_smts)), all_smts)
                .into_iter()
                .filter_map(|(l, s)| match s {
                    CFGStatement::Statement(Statement::Break { .. }) => Some(l),
                    _ => None,
                })
                .collect::<Vec<_>>();
            v.push(*l);
            //dbg!(&v);
            v
        }
        CFGStatement::TryCatch(_l1, l2, _l3, l4) => vec![*l2, *l4],
        CFGStatement::TryEntry(sl) => {
            let s_l = &(*sl, lookup(*sl, all_smts));
            let final_s_l = r#final(s_l, all_smts);
            final_s_l
        }
        CFGStatement::TryExit => vec![*l],
        CFGStatement::CatchEntry(sl) => {
            let s_l = &(*sl, lookup(*sl, all_smts));
            let final_s_l = r#final(s_l, all_smts);
            final_s_l
        }
        CFGStatement::CatchExit => vec![*l],
        CFGStatement::FunctionEntry { .. } => unreachable!(),
        CFGStatement::FunctionExit { .. } => unreachable!(),
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
        CFGStatement::Statement(Statement::Continue { .. }) => Vec::new(),
        CFGStatement::Statement(Statement::Break { .. }) => Vec::new(),
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
                        CFGStatement::Statement(Statement::Continue { .. }) => true,
                        _ => false,
                    })
            {
                v.push((l_continue, *l));
            }

            v
        }
        CFGStatement::TryCatch(l1, l2, l3, l4) => {
            let s1_l = (*l1, lookup(*l1, all_smts)); // starting labelled statement in try { .. }
            let mut v = vec![(*l, init(&s1_l))]; // from try-catch statement to try entry
            v.append(&mut flow(&s1_l, all_smts));

            let s2_l = (*l3, lookup(*l3, all_smts));
            v.append(&mut flow(&s2_l, all_smts));

            for l_f in r#final(&s1_l, all_smts) {
                v.push((l_f, *l2));
            }

            for l_f in r#final(&s2_l, all_smts) {
                v.push((l_f, *l4));
            }
            v
        }
        CFGStatement::TryEntry(sl) => {
            let sl_l = (*sl, lookup(*sl, all_smts));
            let mut v = flow(&sl_l, all_smts);
            v.push((*l, init(&sl_l)));
            v
        }
        CFGStatement::TryExit => Vec::new(),
        CFGStatement::CatchEntry(sl) => {
            let sl_l = (*sl, lookup(*sl, all_smts));
            let mut v = flow(&sl_l, all_smts);
            v.push((*l, init(&sl_l)));
            v
        }
        CFGStatement::CatchExit => Vec::new(),
        CFGStatement::FunctionEntry { .. } => todo!(),
        CFGStatement::FunctionExit { .. } => todo!(),
    }
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
        (1, 2),
        (11, 13),
        (15, 17),
        (9, 11),
        (9, 15),
        (7, 9),
        (4, 7),
        (2, 4),
        (23, 25),
        (27, 29),
        (21, 23),
        (21, 27),
        (20, 21),
        (13, 19),
        (17, 19),
        (25, 31),
        (29, 31),
        (0, 1),
        (19, 32),
        (31, 32),
    ];

    assert_eq!(expected, flw);
}
