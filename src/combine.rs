/// This module contains combinators - parsers to combine two or more parsers into a single parser
use crate::types::*;

/// Combines two parsers to parse both subsequent expressions:
/// ```text
/// EXPR -> EXPR1 EXPR2
/// ```
/// NOTE:
/// While Rust doesn't support variadic generics, we have to implement
/// separate function for all supported number of arguments manually
// TODO: Try to use macros?
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

/// Combines three parsers to parse both subsequent expressions:
/// ```text
/// EXPR -> EXPR1 EXPR2 EXPR3
/// ```
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
/// In contrast to [and2()], [and3()] etc all parsers should have a same return type
/// ```text
/// EXPR -> EXPR1 ... EXPR_N
/// ```
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
/// ```text
/// EXPR -> EXPR1
///      |  EXPR2
/// ```
pub fn or<'a, P1, P2, R>(p1: P1, p2: P2) -> impl FnOnce(&'a str) -> ParserResult<'a, R>
where
    P1: FnOnce(&'a str) -> ParserResult<'a, R>,
    P2: FnOnce(&'a str) -> ParserResult<'a, R>,
{
    |str: &'a str| p1(str).or_else(|| p2(str))
}

/// Maps parser `str -> ParserResult<T>` to the parse `str -> ParserResult<U>`
/// by applying a function T -> U
pub fn map<'a, T, U, P, F>(p: P, f: F) -> impl FnOnce(&'a str) -> ParserResult<'a, U>
where
    P: FnOnce(&'a str) -> ParserResult<'a, T>,
    F: FnOnce(T) -> U,
{
    |str: &'a str| p(str).map(|x| parsed(f(x.value), x.residual))
}

/// Maps parser `str -> ParserResult<T>` to the parse `str -> ParserResult<U>`
/// by applying a function T -> Option<U>. Differs from [map()] because it
/// "flats" Option and produce `ParserResult<U>` instead of `ParserResult<Option<U>>`
/// It's similar to functions like `flatmap` or `bind` from functional languages
pub fn and_then<'a, T, U, P, F>(p: P, f: F) -> impl FnOnce(&'a str) -> ParserResult<'a, U>
where
    P: FnOnce(&'a str) -> ParserResult<'a, T>,
    F: FnOnce(T) -> Option<U>,
{
    |str: &'a str| p(str).and_then(|x| f(x.value).map(|y| parsed(y, x.residual)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::base::*;

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

        let res = map(tag("abc"), |x| x.len())("123");
        assert!(res.is_none());
    }

    #[test]
    fn test_and_then() {
        // Successful take, success parse
        let res = and_then(take(3), |x| x.parse::<u32>().ok())("123abc");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, 123);
        assert_eq!(res.unwrap().residual, "abc");

        // Successful take, failed parse
        let res = and_then(take(3), |x| x.parse::<u32>().ok())("abcdef");
        assert!(res.is_none());

        // Failed take
        let res = and_then(take(3), |x| x.parse::<u32>().ok())("ab");
        assert!(res.is_none());
    }
}
