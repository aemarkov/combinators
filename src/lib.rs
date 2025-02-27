use std::str::FromStr;

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
pub fn parsed<'a, T>(value: T, residual: &'a str) -> Parsed<'a, T> {
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

/// Takes a specific number of characters
pub fn take(n: usize) -> impl FnOnce(&str) -> ParserResult<&str> {
    move |str| {
        let mut it = str.char_indices();

        for i in 0..n {
            if it.next().is_none() {
                return None;
            }
        }

        let idx = it.next().map(|(idx, _)| idx).unwrap_or(str.len());
        Some(parsed(&str[..idx], &str[idx..]))
    }
}

/// Takes a characters while predicate is true
pub fn take_while<F>(f: F) -> impl FnOnce(&str) -> ParserResult<&str>
where
    F: Fn(char) -> bool,
{
    move |str| {
        if let Some((idx, _)) = (str.char_indices().skip_while(|(_, c)| f(*c))).next() {
            Some(parsed(&str[..idx], &str[idx..]))
        } else {
            Some(parsed(&str, ""))
        }
    }
}

/// Combines two parsers to parse both subsequent expressions
/// While Rust doesn't support variadic generics, we have to implement
/// separate function for all supported number of arguments manually
/// TODO: Try to use macros?
pub fn and2<'a, P1, P2, R1, R2>(
    p1: P1,
    p2: P2,
) -> impl FnOnce(&'a str) -> ParserResult<'a, (R1, R2)>
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

/// Combines three parsers to parse both subsequent expressions
pub fn and3<'a, P1, P2, P3, R1, R2, R3>(
    p1: P1,
    p2: P2,
    p3: P3,
) -> impl FnOnce(&'a str) -> ParserResult<'a, (R1, R2, R3)>
where
    P1: FnOnce(&'a str) -> ParserResult<'a, R1>,
    P2: FnOnce(&'a str) -> ParserResult<'a, R2>,
    P3: FnOnce(&'a str) -> ParserResult<'a, R3>,
{
    |str: &'a str| {
        p1(str)
            .and_then(|res1| p2(&res1.residual).map(|res2| (res1.value, res2.value, res2.residual)))
            .and_then(|res1| {
                p3(res1.2).map(|res2| parsed((res1.0, res1.1, res2.value), &res2.residual))
            })
    }
}

/// Combines multiple parsers to parse all subsequent expressions
/// In contrast to and2(), and3() etc all parsers should have a same return type
pub fn and<'a, P, I, R>(parsers: I) -> impl FnOnce(&'a str) -> ParserResult<'a, Vec<R>>
where
    P: FnOnce(&'a str) -> ParserResult<'a, R>,
    I: IntoIterator<Item = P>,
{
    |str: &'a str| {
        let mut results: Vec<R> = Vec::new();
        let mut str = str;
        for parser in parsers {
            if let Some(res) = parser(str) {
                results.push(res.value);
                str = res.residual;
            } else {
                return None;
            }
        }

        Some(parsed(results, str))
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
    |str| take_while(|c| c.is_whitespace())(str).and_then(|res| Some(parsed((), res.residual)))
}

/// Creates parser to parse something from string
pub fn from_str<T>() -> impl FnOnce(&str) -> ParserResult<T>
where
    T: FromStr,
{
    |str| {
        let idx = str.find(|c| !char::is_numeric(c)).unwrap_or(str.len());

        str[..idx].parse::<T>().ok().map(|x| parsed(x, &str[idx..]))
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
    fn test_take() {
        let res = take(6)("приветмир");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, "привет");
        assert_eq!(res.unwrap().residual, "мир");

        let res = take(6)("привет");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, "привет");
        assert_eq!(res.unwrap().residual, "");

        let res = take(6)("прив");
        assert!(res.is_none());
    }

    #[test]
    fn test_take_while() {
        let res = take_while(|c| c.is_alphabetic())("привет123");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, "привет");
        assert_eq!(res.unwrap().residual, "123");

        let res = take_while(|c| c.is_alphabetic())("привет");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, "привет");
        assert_eq!(res.unwrap().residual, "");

        let res = take_while(|c| c.is_alphabetic())("123привет");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, "");
        assert_eq!(res.unwrap().residual, "123привет");
    }

    #[test]
    fn test_and2() {
        let res = and2(tag("abc"), tag("def"))("abcdef123");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, ("abc", "def"));
        assert_eq!(res.unwrap().residual, "123");

        let res = and2(tag("abc"), tag("def"))("abcdef");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, ("abc", "def"));
        assert_eq!(res.unwrap().residual, "");

        let res = and2(tag("abc"), tag("def"))("def");
        assert!(res.is_none());

        let res = and2(tag("abc"), tag("def"))("abc");
        assert!(res.is_none());
    }

    #[test]
    fn test_and3() {
        let res = and3(tag("abc"), tag("def"), tag("ghi"))("abcdefghi123");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, ("abc", "def", "ghi"));
        assert_eq!(res.unwrap().residual, "123");

        let res = and3(tag("abc"), tag("def"), tag("ghi"))("abcdefghi");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, ("abc", "def", "ghi"));
        assert_eq!(res.unwrap().residual, "");

        let res = and3(tag("abc"), tag("def"), tag("ghi"))("abcdefgh");
        assert!(res.is_none());
    }

    #[test]
    fn test_and() {
        // Two parsers, equal to and2()
        let res = and([tag("abc"), tag("def")])("abcdef123");
        assert!(res.is_some());
        let res = res.unwrap();
        assert_eq!(res.value, vec!["abc", "def"]);
        assert_eq!(res.residual, "123");

        let res = and([tag("abc"), tag("def")])("abcdef");
        assert!(res.is_some());
        let res = res.unwrap();
        assert_eq!(res.value, vec!["abc", "def"]);
        assert_eq!(res.residual, "");

        let res = and([tag("abc"), tag("def")])("abcde");
        assert!(res.is_none());

        // Three parsers
        let res = and([tag("abc"), tag("def"), tag("ghi")])("abcdefghi123");
        assert!(res.is_some());
        let res = res.unwrap();
        assert_eq!(res.value, vec!["abc", "def", "ghi"]);
        assert_eq!(res.residual, "123");
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

        let res = map(from_str(), |x| x * 2)("123abc");
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
        let res = from_str()("1234");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, 1234);
        assert_eq!(res.unwrap().residual, "");

        let res = from_str()("1234hello");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, 1234);
        assert_eq!(res.unwrap().residual, "hello");

        let res = from_str()("hello");
        assert!(res.is_none());
    }
}
