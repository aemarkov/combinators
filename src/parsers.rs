/// This module contains common higher-level to parse different values
use crate::{base::*, combine::*, types::*};

use std::{ops::Neg, str::FromStr};

/// Creates a parser to skip a whitespace
pub fn whitespace() -> impl FnOnce(&str) -> ParserResult<()> {
    |str| take_while(|c| c.is_whitespace())(str).and_then(|res| Some(parsed((), res.residual)))
}

// Helper macro to impl trait for multiple types and reduce boilerplate
macro_rules! impl_trait {
    ($trait:ident, $($t:ty),*) => {
        $(impl $trait for $t {})*
    };
}

/// Empty trait to bound generic parameter to any primitive unsigned integer type
pub trait UnsignedNumber: FromStr {}
impl_trait!(UnsignedNumber, u8, u16, u32, u64, u128, usize);

/// Empty trait to bound generic parameter to any primitive signed integer type
pub trait SignedNumber: FromStr {}
impl_trait!(SignedNumber, i8, i16, i32, i64, i128, isize);

/// Creates parser to read out digits
pub fn digits() -> impl FnOnce(&str) -> ParserResult<&str> {
    take_while(|c| c.is_numeric())
}

/// Creates parser to parse unsigned decimal integer from string
pub fn unsigned_int<'a, T>() -> impl FnOnce(&'a str) -> ParserResult<'a, T>
where
    T: UnsignedNumber,
{
    and_then(digits(), |x| x.parse::<T>().ok())
}

/// Creates parser to parses signed  decimal integer from string
pub fn signed_int<'a, T>() -> impl FnOnce(&'a str) -> ParserResult<'a, T>
where
    T: SignedNumber,
    T: Neg<Output = T>,
{
    // str.parse::<T> can parse sign itself. However, when I check for sign
    // by tag(), it consumes the sign char. Ideally, we have to check without
    // consumption but it's not possible with current API.
    and_then(and2(or(tag("-"), tag("")), digits()), |(sign, digits)| {
        let value = digits.parse::<T>().ok()?;
        match sign {
            "-" => Some(-value),
            _ => Some(value),
        }
    })
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
    fn test_unsigned_number() {
        let res = unsigned_int::<u32>()("1234");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, 1234);
        assert_eq!(res.unwrap().residual, "");

        let res = unsigned_int::<u32>()("1234hello");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, 1234);
        assert_eq!(res.unwrap().residual, "hello");

        let res = unsigned_int::<u32>()("hello");
        assert!(res.is_none());
    }

    #[test]
    fn test_signed_number() {
        let res = signed_int::<i32>()("1234");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, 1234);
        assert_eq!(res.unwrap().residual, "");

        let res = signed_int::<i32>()("-1234");
        assert_eq!(res.is_some(), true);
        assert_eq!(res.unwrap().value, -1234);
        assert_eq!(res.unwrap().residual, "");

        let res = signed_int::<i32>()("-1234hello");
        assert_eq!(res.is_some(), true);
        assert_eq!(res.unwrap().value, -1234);
        assert_eq!(res.unwrap().residual, "hello");

        let res = signed_int::<i32>()("hello");
        assert_eq!(res.is_none(), true);
    }
}
