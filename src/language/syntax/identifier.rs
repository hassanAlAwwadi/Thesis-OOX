use crate::positioned::{SourcePos, WithPosition};
use derivative::Derivative;

use std::{
    fmt::{Debug, Display},
    ops::Deref,
    rc::Rc,
};

#[derive(Clone, Derivative)]
#[derivative(PartialEq, Hash, Eq, PartialOrd, Ord)]
pub struct Identifier {
    name: Rc<str>,

    #[derivative(PartialEq = "ignore")]
    #[derivative(Hash = "ignore")]
    #[derivative(PartialOrd = "ignore")]
    #[derivative(Ord = "ignore")]
    info: SourcePos,
}

impl WithPosition for Identifier {
    fn get_position(&self) -> SourcePos {
        self.info
    }
}

impl Debug for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl PartialEq<&str> for Identifier {
    fn eq(&self, other: &&str) -> bool {
        self.name.as_ref() == *other
    }
}

impl PartialEq<Identifier> for &str {
    fn eq(&self, other: &Identifier) -> bool {
        other.name.as_ref() == *self
    }
}

impl Identifier {
    pub fn with_pos(name: String, info: SourcePos) -> Identifier {
        Identifier {
            name: name.into(),
            info,
        }
    }

    pub fn with_unknown_pos(name: String) -> Identifier {
        Identifier {
            name: name.into(),
            info: SourcePos::UnknownPosition,
        }
    }

    pub fn as_str(&self) -> &str {
        &self.name
    }
}

impl Deref for Identifier {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.name
    }
}

impl AsRef<str> for Identifier {
    fn as_ref(&self) -> &str {
        &self.name
    }
}

impl From<&str> for Identifier {
    fn from(other: &str) -> Self {
        Identifier::with_unknown_pos(other.to_owned())
    }
}

impl From<String> for Identifier {
    fn from(other: String) -> Self {
        Identifier::with_unknown_pos(other)
    }
}
impl From<Identifier> for String {
    fn from(value: Identifier) -> Self {
        value.name.to_string()
    }
}
