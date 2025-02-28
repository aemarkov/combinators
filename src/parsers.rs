/// This module contains common higher-level to parse different values
use crate::{base::*, types::*};

use std::str::FromStr;

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
    fn test_from_string() {
        let res = from_str::<u32>()("1234");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, 1234);
        assert_eq!(res.unwrap().residual, "");

        let res = from_str::<u32>()("1234hello");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, 1234);
        assert_eq!(res.unwrap().residual, "hello");

        let res = from_str::<u32>()("hello");
        assert!(res.is_none());
    }
}
