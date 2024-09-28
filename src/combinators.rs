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
    pub fn new(value: T, residual: &'a str) -> Self{
        Self { value, residual, }
    }
}

/// Result of the parsing
/// Some - parsing successful
/// None - parsed failed
pub type ParserResult<'a, T> = Option<Parsed<'a, T>>;


/// Parses fixed string
pub fn tag<'a, 'b>(str: &'a str, tag: &'b str) -> ParserResult<'a, &'a str> {
    if str.starts_with(tag) {
        Some(Parsed::new(&str[..tag.len()], &str[tag.len()..]))
    } else {
        None
    }
}


/// Parses two subsequent expressions
pub fn and<'a, F1, F2, R1, R2>(f1: F1, f2: F2, str: &'a str) -> ParserResult<'a, (R1, R2)>
    where F1: FnOnce(&'a str) -> ParserResult<'a, R1>,
          F2: FnOnce(&'a str) -> ParserResult<'a, R2>
{
    if let Some(res1) = f1(&str) {
        if let Some(res2) = f2(res1.residual) {
            Some(Parsed::new((res1.value, res2.value), &res2.residual))
        } else {
            None
        }
    } else {
        None
    }
}


/// Parses either first expression or second
pub fn or<'a, F1, F2, R>(f1: F1, f2: F2, str: &'a str) -> ParserResult<'a, R>
    where F1: FnOnce(&'a str) -> ParserResult<'a, R>,
          F2: FnOnce(&'a str) -> ParserResult<'a, R>
{
    let res1 = f1(str);
    if res1.is_some() {
        res1
    } else {
        f2(str)
    }
}

/// Consumes a whitespace
pub fn whitespace(str: &str) -> ParserResult<()> {
    for (i, c) in str.chars().enumerate() {
        if !char::is_whitespace(c) {
            return Some(Parsed::new((), &str[i..]));
        }
    }

    Some(Parsed::new((), &str[str.len()..]))
}


/// Parses number
pub fn number(str: &str) -> ParserResult<u32> {
    let mut value: u32 = 0;
    let mut i = 0;

    for c in str.chars() {
        if let Some(digit) = c.to_digit(10) {
            value = value.checked_mul(10)?.checked_add(digit)?;
            i +=  1;
        } else {
            break;
        }
    }

    if i > 0 {
        Some(Parsed::new(value, &str[i..]))
    } else {
        None
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tag() {
        let res = tag("abc123", "abc");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, "abc");
        assert_eq!(res.unwrap().residual, "123");

        let res = tag("abc", "abc");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, "abc");
        assert_eq!(res.unwrap().residual, "");

        let res = tag("123", "abc");
        assert!(res.is_none());
    }

    #[test]
    fn test_and() {
        let parser = |str| and(|x| tag(x, "abc"), |x| tag(x, "def"), str);

        let res = parser("abcdef123");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, ("abc", "def"));
        assert_eq!(res.unwrap().residual, "123");

        let res = parser("def123");
        assert!(res.is_none());

        let res = parser("abc123");
        assert!(res.is_none());
    }

    #[test]
    fn test_or() {
        let parser = |str| or(|x| tag(x, "abc"), |x| tag(x, "def"), str);

        let res = parser("abcdef123");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, "abc");
        assert_eq!(res.unwrap().residual, "def123");

        let res = parser("abc123");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, "abc");
        assert_eq!(res.unwrap().residual, "123");

        let res = parser("def123");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, "def");
        assert_eq!(res.unwrap().residual, "123");

        let res = parser("123");
        assert!(res.is_none());
    }

    #[test]
    fn test_whitespace() {
        let res = whitespace("hello");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, ());
        assert_eq!(res.unwrap().residual, "hello");

        let res = whitespace("    hello");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, ());
        assert_eq!(res.unwrap().residual, "hello");

        let res = whitespace("    ");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, ());
        assert_eq!(res.unwrap().residual, "");
    }

    #[test]
    fn test_number() {
        let res = number("1234");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, 1234);
        assert_eq!(res.unwrap().residual, "");

        let res = number("1234hello");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, 1234);
        assert_eq!(res.unwrap().residual, "hello");

        let res = number("hello");
        assert!(res.is_none());
    }
}
