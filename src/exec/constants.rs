use crate::Identifier;

pub fn retval() -> Identifier {
    Identifier::with_unknown_pos("retval".to_string())
}

pub fn this_str() -> Identifier {
    Identifier::with_unknown_pos("this".to_owned())
}

pub fn unreachable() -> u64{
    return std::u64::MAX;
}