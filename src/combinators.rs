/// This crate contains basic combinators

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
pub fn and<'a, P1, P2, R1, R2>(p1: P1, p2: P2) -> impl FnOnce(&'a str) -> ParserResult<'a, (R1, R2)>
where
    P1: FnOnce(&'a str) -> ParserResult<'a, R1>,
    P2: FnOnce(&'a str) -> ParserResult<'a, R2>,
{
    |str: &'a str| {
        p1(str).and_then(|res1| {
            p2(res1.residual).map(|res2| parsed((res1.value, res2.value), &res2.residual))
        })
    }
}

/// Combines two parsers to parse either first expression or another
pub fn or<'a, P1, P2, R>(p1: P1, p2: P2) -> impl FnOnce(&'a str) -> ParserResult<'a, R>
where
    P1: FnOnce(&'a str) -> ParserResult<'a, R>,
    P2: FnOnce(&'a str) -> ParserResult<'a, R>,
{
    |str: &'a str| p1(str).or_else(|| p2(str))
}

/// Maps ParserResult<T> of  the parser P to the ParserResult<U> by applying a function T -> U
pub fn map<'a, T, U, P, F>(p: P, f: F) -> impl FnOnce(&'a str) -> ParserResult<'a, U>
where
    P: FnOnce(&'a str) -> ParserResult<'a, T>,
    F: FnOnce(T) -> U,
{
    |str: &'a str| p(str).map(|x| parsed(f(x.value), x.residual))
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
    fn test_map() {
        let res = map(tag("abc"), |x| x.len())("abc123");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, 3);
        assert_eq!(res.unwrap().residual, "123");

        let res = map(int_u32(), |x| x * 2)("123abc");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, 246);
        assert_eq!(res.unwrap().residual, "abc");

        let res = map(tag("abc"), |x| x.len())("123");
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
