use std::rc::Rc;

use derivative::Derivative;
use im_rc::{HashMap};
use itertools::Either;

use crate::{Declaration, SourcePos};

use super::{Class, CompilationUnit, DeclarationMember, Expression, Identifier, Interface, InterfaceMember, Invocation, Lhs, Method, NonVoidType, Rhs, Statement, TypeExpr};

type Label  = u64; 
type Supply = u64; 
type Nodes  = HashMap<Label, CFGStatement>;
type Flows  = Vec<(Label, Label)>;

pub fn new_unique(supply : &mut Supply ) -> Label {
    let t = *supply;
    *supply = *supply+1; 
    return t;
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum BaseStatement{
    Skip,
    Declare {
        type_: NonVoidType,
        var: Identifier,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Assign {
        lhs: Lhs,
        rhs: Rhs,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Assert {
        assertion: Rc<Expression>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Assume {
        assumption: Either<Rc<Expression>, TypeExpr>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Guard { 
        expression: Either<Rc<Expression>, TypeExpr>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
}


#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum CFGStatement {
    /// Can be any Statement minus any of the branching statements in this enum
    Statement(BaseStatement),
    //condition, then, else
    Ite(Label, Label, Label),
    // condition, body
    While(Label, Label),
    // try, catch
    TryCatch(Label, Label),
    // left label can be anything *except* another Seq.  
    Seq(Label, Label),
    // Invocation can't be turned into a label because it is dependent on runtime
    Call (Invocation),
    Continue,
    Break,
    Return {
        expression: Option<Rc<Expression>>,
    },
    Throw {
        message: String,
    },
    // Special node for rejoining of 'if' and 'trycatch' statements
    // assuming that both branches actually 
    Join 
}

impl CompilationUnit{
    pub fn to_graph(self : CompilationUnit) -> (Label, Nodes, Flows){
        let mut supply: u64 = 0;
        let mut nodes: Nodes = HashMap::new();
        let mut flows: Flows = vec![];

        for decl in self.members {
            match decl{
                Declaration::Class(class) => class.fill_graph(&mut supply, &mut nodes, &mut flows),
                Declaration::Interface(interface) => interface.fill_graph(&mut supply, &mut nodes, &mut flows),
            }

        }
        let entry: u64 = 0;
        return (entry, nodes, flows);
    }
}


impl Class{
    fn fill_graph(&self, supply:  &mut Supply, nodes: &mut Nodes, flows: &mut Flows) -> (){
        for member in &self.members{
            member.fill_graph(supply, nodes, flows);
        }
        return ()
    }
}
impl Interface{
    fn fill_graph(&self, supply:  &mut Supply, nodes: &mut Nodes, flows: &mut Flows) -> (){
        for member in &self.members{
            member.fill_graph(supply, nodes, flows);
        }
        return ()
    }
}

impl DeclarationMember{
    fn fill_graph(&self, supply:  &mut Supply, nodes: &mut Nodes, flows: &mut Flows) -> Option<Label>{
        match self {
            DeclarationMember::Method(method) => {
                return Some(method.fill_graph(supply, nodes, flows));
            },
            DeclarationMember::Constructor(method) => {
                return Some(method.fill_graph(supply, nodes, flows));
            },
            DeclarationMember::Field { .. } => return None,
        }
    }
}

impl InterfaceMember{
    fn fill_graph(&self, supply:  &mut Supply, nodes: &mut Nodes, flows: &mut Flows) -> Option<Label>{
        match self{
            InterfaceMember::DefaultMethod(method) => {
                return Some(method.fill_graph(supply, nodes, flows));
            },
            InterfaceMember::AbstractMethod(_abstract_method) => return None,
        }
    }
}


impl Method{
    fn fill_graph(&self, supply:  &mut Supply, nodes: &mut Nodes, flows: &mut Flows) -> Label{
        let (entry, _exit) = self.body.borrow().fill_graph(supply, nodes, flows, None, None);
        return entry;
    }
}

impl Statement{
    fn fill_graph(&self, supply:  &mut Supply, nodes: &mut Nodes, flows: &mut Flows,lob: Option<Label>, catch: Option<Label>) -> (Label, Option<Label>){
        match self{
            Statement::Skip => {
                let index = new_unique(supply); 
                let element = BaseStatement::Skip;
                nodes.insert(index, CFGStatement::Statement(element));
                return (index, Some(index));
            }
            Statement::Declare { type_ , var, info } => {
                let index = new_unique(supply); 
                let element = BaseStatement::Declare { type_: type_.clone(), var: var.clone(), info: info.clone() }; 
                nodes.insert(index, CFGStatement::Statement(element));
                return (index, Some(index));
            }
            Statement::Assign { lhs, rhs, info } => {
                let index = new_unique(supply); 
                let element = BaseStatement::Assign { lhs: lhs.clone(), rhs: rhs.clone(), info: info.clone()}; 
                nodes.insert(index, CFGStatement::Statement(element));
                return (index, Some(index));

            },
            Statement::Assert { assertion, info } =>  {
                let index = new_unique(supply); 
                let element = BaseStatement::Assert { assertion: assertion.clone(), info: info.clone()}; 
                nodes.insert(index, CFGStatement::Statement(element));
                return (index, Some(index));

            },
            Statement::Assume { assumption, info } =>  {
                let index = new_unique(supply); 
                let element = BaseStatement::Assume { assumption: assumption.clone(), info: info.clone()}; 
                nodes.insert(index, CFGStatement::Statement(element));
                return (index, Some(index));
            },

            Statement::Seq { stat1, stat2 } => {
                let (start, mid) = stat1.fill_graph(supply, nodes, flows, lob, catch); 
                match mid{
                    //either we broke/continued in a loop, or we threw an error
                    None => return (start, mid),
                    Some(midlabel) => {
                        let (then, exit) = stat2.fill_graph(supply, nodes, flows, lob, catch);
                        flows.push((midlabel, then));
                        return(start, exit);
                    }
                }
            },
            // note that entry and exit edges to Call statements are special
            // need runtime support, can't be properly captured at "compile" time.
            Statement::Call { invocation, info: _ } => {
                let index = new_unique(supply); 
                let element = CFGStatement::Call(invocation.clone()); 
                nodes.insert(index, element);
                return (index, Some(index));
            },
            Statement::While { guard, body, info } => {
                let w_index = new_unique(supply); 

                let g_index = new_unique(supply); 
                let g_element = CFGStatement::Statement(
                    BaseStatement::Guard{ expression: Either::Left(guard.clone()), info: info.clone()}
                );

                let (b_index, b_exit) = body.fill_graph(supply, nodes, flows, Some(w_index), catch);

                let w_element = CFGStatement::While(g_index, b_index);
                nodes.insert(w_index, w_element); 
                nodes.insert(g_index, g_element);
                // b_index should already be inserted 
                assert!(nodes.contains_key(&b_index));

                flows.push((w_index, g_index));
                flows.push((g_index, b_index));
                
                if let Some(b_end) = b_exit{
                    //the body has a "normal" exit, aka not a break, continue, or throw
                    //and thus it has a back edge we still need to add
                    flows.push((b_end, w_index)) 
                }
                return (w_index, Some(g_index));
            }
            Statement::Continue { info: _  } => {
                let index = new_unique(supply); 
                let element = CFGStatement::Continue; 
                nodes.insert(index, element);
                if let Some(w_index) = lob{
                    flows.push((index, w_index));
                }
                return (index, None);
            },
            Statement::Break { info: _  } => {
                todo!("still need to handle breaks in the CFG generation")
            },
            Statement::Return { expression, info: _  } => {
                let index = new_unique(supply); 
                let element = CFGStatement::Return{ expression: expression.clone()}; 
                nodes.insert(index, element);
                // the flow is to be determined at runtime 
                return (index, None);
            },
            Statement::Throw { message, info: _  } => {
                let index = new_unique(supply); 
                let element = CFGStatement::Throw { message: message.clone() };
                nodes.insert(index, element);
                if let Some(c_index) = catch{
                    flows.push((index, c_index))
                }
                return (index, None);
            },
            Statement::Ite { guard, true_body, false_body, info  } => {
                let ite_index = new_unique(supply); 
                
                let g_index = new_unique(supply);
                let g_element = CFGStatement::Statement(
                    BaseStatement::Guard{ expression: guard.clone(), info: info.clone()}
                ); 

                let (t_index, t_exit) = true_body.fill_graph(supply, nodes, flows, lob, catch);
                let (e_index, e_exit) = false_body.fill_graph(supply, nodes, flows, lob, catch);
                
                let ite_element = CFGStatement::Ite(g_index, t_index, e_index); 
                nodes.insert(ite_index, ite_element); 
                nodes.insert(g_index, g_element);
                
                // t_index and e_index should already be inserted 
                assert!(nodes.contains_key(&t_index));
                assert!(nodes.contains_key(&e_index));
                flows.push((ite_index, t_index));
                flows.push((ite_index, e_index));
                
                match (t_exit, e_exit){
                    (None,         None        ) => return (ite_index, None),
                    (None,         Some(r)) => return (ite_index, Some(r)),
                    (Some(l), None        ) => return (ite_index, Some(l)),
                    (Some(l), Some(r)) => {
                        let j_index = new_unique(supply);
                        let j_element = CFGStatement::Join; 
                        nodes.insert(j_index, j_element);
                        flows.push((l, j_index)); 
                        flows.push((r, j_index));
                        return (ite_index, Some(j_index));
                    }
                }
            },
            Statement::Try { try_body, catch_body, info: _  } => {
                let _tc_index = new_unique(supply); 
                let (cb_index, _cb_exit)= catch_body.fill_graph(supply, nodes, flows, lob, catch);
                let (_tr_index, _tr_exit) = try_body.fill_graph(supply, nodes, flows, lob, Some(cb_index));
                
                let _tc_element = 
                todo!();
            },
            Statement::Block { body } => {
                return body.fill_graph(supply, nodes, flows, lob, catch);
            },
        }
    }
}
