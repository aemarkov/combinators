/// This crate contains arithmetic expressions parsers
use crate::combinators::*;
use std::fmt::{Debug, Display};

/// Arithmetical operation
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Operand {
    PLUS,
    MINUS,
    MULT,
    DIV,
}

impl Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operand::PLUS => write!(f, "+"),
            Operand::MINUS => write!(f, "-"),
            Operand::MULT => write!(f, "*"),
            Operand::DIV => write!(f, "/"),
        }
    }
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

/*
Example:
Parse an expression only "+" and "-", e.g. "1+2-3" (yes, no spaces)

Grammar:
EXPR  -> TERM EXPR'
EXPR' -> + TERM EXPR' | eps
TERM  -> num
*/

/// Abstract syntax tree node for arithmetic expression grammar
#[derive(Debug, PartialEq)]
pub enum AstNode {
    Expr(Box<AstNode>, Box<AstNode>),
    Expr1(Box<AstNode>, Box<AstNode>, Box<AstNode>),
    Op(Operand),
    Term(u32),
    Eps,
}

impl Display for AstNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AstNode::Expr(_, _) => self.print_node("", true, f),
            _ => Err(std::fmt::Error),
        }
    }
}

impl AstNode {
    fn print_node(
        &self,
        prefix: &str,
        is_last: bool,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        // Prefix - pseudo-graphic tree lines
        let node_prefix = if prefix.len() > 0 {
            prefix.to_owned() + if is_last { "└─" } else { "├─" }
        } else {
            // Don't print prefix for root
            "".to_owned()
        };

        let child_prefix = prefix.to_owned()
            + if is_last { " " } else { "│" }
            + if prefix.len() > 0 { "  " } else { "" };

        match self {
            AstNode::Expr(a, b) => {
                writeln!(f, "{}EXPR", node_prefix)?;
                a.print_node(&child_prefix, false, f)?;
                b.print_node(&child_prefix, true, f)
            }
            AstNode::Expr1(a, b, c) => {
                writeln!(f, "{}EXPR'", node_prefix)?;
                a.print_node(&child_prefix, false, f)?;
                b.print_node(&child_prefix, false, f)?;
                c.print_node(&child_prefix, true, f)
            }
            AstNode::Op(op) => writeln!(f, "{}OP({})", node_prefix, op),
            AstNode::Term(val) => writeln!(f, "{}TERM({})", node_prefix, val),
            AstNode::Eps => writeln!(f, "{}ε", node_prefix),
        }
    }
}

/*
NOTE: All other functions have signature (&str) -> FnOnce(&str) -> ParserResult<T>. So those
functions creates a parser function, which can be combined with other parsers. However, it's not
possible to have a recursive function with "impl Trait" return type.
There are some possible solutions:
 - return Box<dyn Trait>, but it has performance impact
 - return some custom struct with "parse(&str)" method, but it's not convenient

So for now I've decided just to change signature to (&str) -> ParserResult<T>. In other words, those
functions don't create parsers, they are parsers. It's OK while they don't have any extra arguments
(like tag() function).
*/

pub fn nt_expr(str: &str) -> ParserResult<AstNode> {
    map(and(nt_term, nt_expr1), |(a, b)| {
        AstNode::Expr(Box::new(a), Box::new(b))
    })(str)
}

fn nt_expr1<'a>(str: &'a str) -> ParserResult<AstNode> {
    or(
        map(and(and(plus_minus(), nt_term), nt_expr1), |((op, a), b)| {
            AstNode::Expr1(Box::new(AstNode::Op(op)), Box::new(a), Box::new(b))
        }),
        eps,
    )(str)
}

fn eps(str: &str) -> ParserResult<AstNode> {
    Some(Parsed::new(AstNode::Eps, str))
}

fn nt_term<'a>(str: &'a str) -> ParserResult<AstNode> {
    map(int_u32(), |x| AstNode::Term(x))(str)
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

    #[test]
    fn test_ast_print() {
        // Commit the current formatting behavior
        // This is not a  correct AST, but it covers more cases
        let res = AstNode::Expr(
            Box::new(AstNode::Expr1(
                Box::new(AstNode::Term(1)),
                Box::new(AstNode::Op(Operand::MULT)),
                Box::new(AstNode::Term(2)),
            )),
            Box::new(AstNode::Expr1(
                Box::new(AstNode::Term(3)),
                Box::new(AstNode::Op(Operand::PLUS)),
                Box::new(AstNode::Term(4)),
            )),
        );

        let output = res.to_string();
        let expected_output = "EXPR
 ├─EXPR'
 │  ├─TERM(1)
 │  ├─OP(*)
 │  └─TERM(2)
 └─EXPR'
    ├─TERM(3)
    ├─OP(+)
    └─TERM(4)
";

        assert_eq!(output, expected_output);
    }
}
