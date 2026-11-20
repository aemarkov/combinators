/// This module contains core types used by combinators library

/// Result of the parsing
/// `value`    - parsed value
/// `residual` - rest of the string not parsed
#[derive(Debug, Clone, Copy)]
pub struct Parsed<'a, T> {
    pub value: T,
    pub residual: &'a str,
}

impl<'a, T> Parsed<'a, T> {
    pub fn new(value: T, residual: &'a str) -> Self {
        Parsed { value, residual }
    }
}

/// Result of the parsing
/// Some - parsing successful
/// None - parsing failed
pub type ParserResult<'a, T> = Option<Parsed<'a, T>>;
