/// This crate contains basic combinators

/// Result of the parsing
/// `value`    - parsed value
/// `residual` - rest of the string not parsed
#[derive(Clone, Copy)]
pub struct Parsed<'a, T> {
    pub value: T,
    pub residual: &'a str,
}

impl<'a, T> Parsed<'a, T> {
    pub fn new(value: T, residual: &'a str) -> Self {
        Self { value, residual }
    }
}

/// Helper function to make Parsed<> construction less verbose
fn parsed<'a, T>(value: T, residual: &'a str) -> Parsed<'a, T> {
    Parsed { value, residual }
}

/// Result of the parsing
/// Some - parsing successful
/// None - parsed failed
pub type ParserResult<'a, T> = Option<Parsed<'a, T>>;

/// Creates a parsed which expects a given string
pub fn tag<'a, 'b>(tag: &'b str) -> impl FnOnce(&'a str) -> ParserResult<&'a str> + 'b {
    move |str: &'a str| {
        if str.starts_with(tag) {
            Some(parsed(&str[..tag.len()], &str[tag.len()..]))
        } else {
            None
        }
    }
}

/// Combines two parsers to parse both subsequent expressions
pub fn and<'a, F1, F2, R1, R2>(f1: F1, f2: F2) -> impl FnOnce(&'a str) -> ParserResult<'a, (R1, R2)>
where
    F1: FnOnce(&'a str) -> ParserResult<'a, R1>,
    F2: FnOnce(&'a str) -> ParserResult<'a, R2>,
{
    |str: &'a str| {
        f1(str).and_then(|res1| {
            f2(res1.residual).map(|res2| parsed((res1.value, res2.value), &res2.residual))
        })
    }
}

/// Combines two parsers to parse either first expression or another
pub fn or<'a, F1, F2, R>(f1: F1, f2: F2) -> impl FnOnce(&'a str) -> ParserResult<'a, R>
where
    F1: FnOnce(&'a str) -> ParserResult<'a, R>,
    F2: FnOnce(&'a str) -> ParserResult<'a, R>,
{
    |str: &'a str| f1(str).or_else(|| f2(str))
}

/// Creates a parser to skip a whitespace
pub fn whitespace() -> impl FnOnce(&str) -> ParserResult<()> {
    |str| {
        let pos = str.find(|c| !char::is_whitespace(c)).unwrap_or(str.len());

        Some(parsed((), &str[pos..]))
    }
}

/// Creates parser to parse an u32 integer
pub fn int_u32() -> impl FnOnce(&str) -> ParserResult<u32> {
    |str| {
        let idx = str.find(|c| !char::is_numeric(c)).unwrap_or(str.len());

        str[..idx]
            .parse::<u32>()
            .ok()
            .map(|x| parsed(x, &str[idx..]))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tag() {
        let res = tag("abc")("abc123");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, "abc");
        assert_eq!(res.unwrap().residual, "123");

        let res = tag("abc")("abc");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, "abc");
        assert_eq!(res.unwrap().residual, "");

        let res = tag("abc")("123");
        assert!(res.is_none());
    }

    #[test]
    fn test_and() {
        let res = and(tag("abc"), tag("def"))("abcdef123");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, ("abc", "def"));
        assert_eq!(res.unwrap().residual, "123");

        let res = and(tag("abc"), tag("def"))("abcdef");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, ("abc", "def"));
        assert_eq!(res.unwrap().residual, "");

        let res = and(tag("abc"), tag("def"))("def");
        assert!(res.is_none());

        let res = and(tag("abc"), tag("def"))("def");
        assert!(res.is_none());
    }

    #[test]
    fn test_or() {
        let res = or(tag("abc"), tag("def"))("abcdef123");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, "abc");
        assert_eq!(res.unwrap().residual, "def123");

        let res = or(tag("abc"), tag("def"))("abc123");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, "abc");
        assert_eq!(res.unwrap().residual, "123");

        let res = or(tag("abc"), tag("def"))("def123");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, "def");
        assert_eq!(res.unwrap().residual, "123");

        let res = or(tag("abc"), tag("def"))("123");
        assert!(res.is_none());
    }

    #[test]
    fn test_whitespace() {
        let res = whitespace()("hello");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, ());
        assert_eq!(res.unwrap().residual, "hello");

        let res = whitespace()("    hello");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, ());
        assert_eq!(res.unwrap().residual, "hello");

        let res = whitespace()("    ");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, ());
        assert_eq!(res.unwrap().residual, "");
    }

    #[test]
    fn test_number() {
        let res = int_u32()("1234");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, 1234);
        assert_eq!(res.unwrap().residual, "");

        let res = int_u32()("1234hello");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, 1234);
        assert_eq!(res.unwrap().residual, "hello");

        let res = int_u32()("hello");
        assert!(res.is_none());
    }
}
