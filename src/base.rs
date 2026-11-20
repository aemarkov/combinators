/// This module contains basic parsers
use crate::types::*;

/// Creates a parsed which expects a given string
pub fn tag<'a, 'b>(tag: &'b str) -> impl FnOnce(&'a str) -> ParserResult<&'a str> + 'b {
    move |s: &'a str| {
        if s.starts_with(tag) {
            let (value, residual) = s.split_at(tag.len());
            Some(Parsed::new(value, residual))
        } else {
            None
        }
    }
}

/// Takes a specific number of characters
pub fn take<'a>(n: usize) -> impl FnOnce(&'a str) -> ParserResult<&'a str> {
    move |s: &str| {
        let byte_offset = s
            .char_indices()
            .map(|(i, _)| i)
            // add extra iteration, because nth(s.len()) points one position behind the
            // string
            .chain(std::iter::once(s.len()))
            .nth(n)?;
        let (value, residual) = s.split_at(byte_offset);
        Some(Parsed::new(value, residual))
    }
}

/// Takes a characters while predicate is true
pub fn take_while<F>(f: F) -> impl FnOnce(&str) -> ParserResult<&str>
where
    F: Fn(char) -> bool,
{
    move |s| {
        let byte_offset = s
            .char_indices()
            // add extra iteration, because nth(s.len()) points one position behind the
            // string
            .chain(std::iter::once((s.len(), char::default())))
            .skip_while(|(_, c)| f(*c))
            .next()?;
        let (value, residual) = s.split_at(byte_offset.0);
        Some(Parsed::new(value, residual))
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
