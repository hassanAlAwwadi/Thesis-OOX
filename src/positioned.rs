
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourcePos {
    UnknownPosition,
    SourcePos {
        line: u64,
        col: u64,
    }
}