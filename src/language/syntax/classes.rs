use derivative::Derivative;

use crate::positioned::SourcePos;

use super::{DeclarationMember, Identifier};
use std::fmt::Debug;

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub struct Class {
    pub name: Identifier,
    pub members: Vec<DeclarationMember>,

    pub extends: Option<Identifier>,
    pub implements: Vec<Identifier>,

    #[derivative(PartialEq = "ignore")]
    pub info: SourcePos,
}
