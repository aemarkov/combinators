/// This module contains basic parsers
use crate::types::*;

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

        for _ in 0..n {
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

        let res = tag("")("abc");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, "");
        assert_eq!(res.unwrap().residual, "abc");

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
}
