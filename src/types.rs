/// This module contains core types used by combinators library

/// Result of the parsing
/// `value`    - parsed value
/// `residual` - rest of the string not parsed
#[derive(Debug, Clone, Copy)]
pub struct Parsed<'a, T> {
    pub value: T,
    pub residual: &'a str,
}

/// Helper function to make Parsed<> construction less verbose
pub fn parsed<'a, T>(value: T, residual: &'a str) -> Parsed<'a, T> {
    Parsed { value, residual }
}

/// Result of the parsing
/// Some - parsing successful
/// None - parsing failed
pub type ParserResult<'a, T> = Option<Parsed<'a, T>>;
