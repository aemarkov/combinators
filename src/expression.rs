/// This crate contains arithmetic expressions parsers
use crate::combinators::*;

/// Arithmetical operation
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Operand {
    PLUS,
    MINUS,
    MULT,
    DIV,
}

/// Creates a parser to parse "+" or "-"
pub fn plus_minus() -> impl FnOnce(&str) -> ParserResult<Operand> {
    |str| match str.chars().next()? {
        '+' => Some(Parsed::new(Operand::PLUS, &str[1..])),
        '-' => Some(Parsed::new(Operand::MINUS, &str[1..])),
        _ => None,
    }
}

// Creates a parser to parses "*" or "/"
pub fn mul_div() -> impl FnOnce(&str) -> ParserResult<Operand> {
    |str| match str.chars().next()? {
        '*' => Some(Parsed::new(Operand::MULT, &str[1..])),
        '/' => Some(Parsed::new(Operand::DIV, &str[1..])),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_plus_minus() {
        let res = plus_minus()("+ 1");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, Operand::PLUS);
        assert_eq!(res.unwrap().residual, " 1");

        let res = plus_minus()("- 1");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, Operand::MINUS);
        assert_eq!(res.unwrap().residual, " 1");

        let res = plus_minus()("1 + 1");
        assert!(res.is_none());
    }

    #[test]
    fn test_mul_div() {
        let res = mul_div()("* 1");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, Operand::MULT);
        assert_eq!(res.unwrap().residual, " 1");

        let res = mul_div()("/ 1");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, Operand::DIV);
        assert_eq!(res.unwrap().residual, " 1");

        let res = mul_div()("1 * 1");
        assert!(res.is_none());
    }
}
