# Simple Parser Combinators

Play around with homemade parser combinators. See the real parser combinators libraries: [Nom](https://github.com/rust-bakery/nom), [Combine](https://github.com/Marwes/combine), [Parsec](https://hackage.haskell.org/package/parsec).

## What is parser combinators?
Parser combinators are a functional programming technique for constructing parsers by combining small, reusable parsing functions into more complex parsers.

Key concepts:
- parser - a function that accepts an input (e.g. a string) and return a result if parsing successful
- combinator - high-order function which combines multiple parsers into a new more complex parser

Examples of combinators:
- combine two parsers sequentially
- try parser alternatively
- repeat parser multiple times
- ...

Parser combinators can parse LL(1) grammar. However, as far I understand, it can parse not-LL grammar but with exponential time and possibility to fall into a infinite recursion.

## Documentation
This project contains several basic parsers, combinators along with several examples. It created just for fun and study purposes. All parsers works only with strings `&str`.

All parsers follows similar signature:
```rs
fn parser(/*arguments*/) -> impl FnOnce(&'a str) -> ParserResult<&'a str>;

/// Result of the parsing
/// `value`    - parsed value
/// `residual` - rest of the string not parsed
pub type ParserResult<'a, T> = Option<Parsed<'a, T>>;

/// Result of the parsing
/// Some - parsing successful
/// None - parsing failed
pub struct Parsed<'a, T> {
    pub value: T,
    pub residual: &'a str,
}
```

Each function returns a parser function (closure) which accepts input string `&str` and returns either `None` if parsing fails or parsing result with residual string.

### List of parsers

Basic parsers
| combinator | usage | input | output | comment |
|---|---|---|---|---|
| tag | `tag("abc")` | `"abcdef"` | `Ok(("abc", "def"))` | Matches specific prefix
| take | `take(3)` | `"abcdef"` | `Ok(("abc", "def))` | Takes first n symbols from string
| take_while | `take(\|c\|c.is_numeric())` | `"123abc"` | `Ok(("123", "abc"))` | Takes first symbols from string while predicate is true

Combine multiple parsers
| combinator | usage | input | output | comment |
|---|---|---|---|---|
| and2 | `and2(tag("abc"), tag("def"))` | `"abcdefghi"`| `Ok((("abc", "def"), "ghi"))` | Takes result from two subsequent parsers
| and2 | `and3(tag("abc"), tag("def"), tag("ghi"))` | `"abcdefghijkl"`| `Ok((("abc", "def", "ghi"), "jkl"))` | Takes result from three subsequent parsers
| and | `and([tag("abc"), tag("def")])` | `"abcdefghi"` | `Ok((["abc", "cde"], "ghi"))` | Takes result from several subsequent parsers. In contrast with `and2` and `and3` all parsers should have same return type
| or | `or(tag("abc"), tag("123"))` | `"abcdef"` | `Ok(("abc", "def"))` | Tries two parsers and return result of first successful one

Processing parser's result
| combinator | usage | input | output | comment |
|---|---|---|---|---|
| map | `map(take_while(\|c\|c.is_numeric()), \|x\|x.len())` | `"123abc"` | `Ok((3, "abc"))` | Maps parser result by applying function `T -> U`
| and_then | `and_then(take_while(\|c\|c.is_numeric()), \|x\|x.parse::<u32>().ok())` | `"123abc"` | `Ok((123, "abc"))` | Maps parser result by applying function `T -> Option<U>`

Some useful parsers
| combinator | usage | input | output | comment |
|---|---|---|---|---|
| whitespace | `whitespace()` | `"   abc"` | `Ok(((), "abc"))` | Consumes any whitespace from the beginning of the string. Always returns `Ok`
| digits | `digits()` | `"123abc"` | `Ok(("123", "abc"))` | Parsers digits (returns string)
| unsigned_int | `unsigned_int()` | `"123abc"` | `Ok((123, "abc"))` | Parsers unsigned integer value
| signed_int | `signed_int()` | `"-123abc"` | `Ok((-123, "abc"))` | Parsers signed integer value

## Examples

### Parse color

[Example: color](https://github.com/aemarkov/combinators/blob/master/examples/color.rs)

Let's break down how to use this library with a simple example: parsing a color, like `#aabbcc` or `rgb(10, 20, 30)`.

Run the example:
```
$ cargo run --example color '#ff0000'
Color: (255, 0, 0)
$ cargo run --example color 'rgb(15, 150, 200)'
Color: (15, 150, 200)
```

Implement HEX parser.

First, we need to parse a hex byte from string: take 2 symbols and trying to parse them into an `u8` integer. We use `take(2)` to take symbols and `and_then` to map `&str` to `u8` by applyting function `&str -> Option<u8>`.
```rs
fn hex_byte<'a>() -> impl FnOnce(&'a str) -> ParserResult<u8> {
    |str: &'a str| {
        take(2)(str).and_then(|x| {
            u8::from_str_radix(x.value, 16)
                .ok()
                .map(|y| parsed(y, x.residual))
        })
    }
}
```

Next, we need to take `#` following by three hex values. We actively use composition to build parser from smaller parts:
- use `and3(...)` with previously implemented `hex_byte()` to parse three subsequent bytes
- use `and2()` with `tag()` and previously implemented three bytes parser to parse `#` following by three hex bytes
```rs
fn hex_color<'a>() -> impl FnOnce(&'a str) -> ParserResult<(u8, u8, u8)> {
    map(
        and2(tag("#"), and3(hex_byte(), hex_byte(), hex_byte())),
        |(_, rgb)| rgb,
    )
}
```

Implement RGB parser in a same way:
```rs
/// Parses rgb color, e.g. rgb(10, 20, 30) with any spaces with braces
fn rgb_color<'a>() -> impl FnOnce(&'a str) -> ParserResult<(u8, u8, u8)> {
    map(and3(tag("rgb("), triplet(), tag(")")), |(_, rgb, _)| rgb)
}

/// Parses three comma separated decimals, e.g. 10, 20, 30
fn triplet<'a>() -> impl FnOnce(&'a str) -> ParserResult<(u8, u8, u8)> {
    and3(
        number_with_comma(),
        number_with_comma(),
        number_with_space(),
    )
}

/// Parses decimal with spaces and comma, e.g. "  10  ,"
fn number_with_comma<'a>() -> impl FnOnce(&'a str) -> ParserResult<u8> {
    map(and2(number_with_space(), tag(",")), |(x, _)| x)
}

/// Parses decimal with spaces around, e.g. " 10  "
fn number_with_space<'a>() -> impl FnOnce(&'a str) -> ParserResult<u8> {
    map(
        and3(whitespace(), unsigned_int(), whitespace()),
        |(_, x, _)| x,
    )
}
```

And finally, we can combine both HEX and RGB parsers into a single one using 'or`:
```rs
fn color<'a>() -> impl FnOnce(&'a str) -> ParserResult<Color> {
    or(rgb_color(), hex_color())
}

```

### Parse arithmetic expression

[Example: expressions](https://github.com/aemarkov/combinators/tree/master/examples/expressions)

Let try a more complex example. We are going to parse simple arithmetic expressions like `2*(3-1)`. Expression consist of integer numbers, parentheses (`()`) and operations (`+-*/`).

Grammar to parse simple arithmetic expressions with operators priority [1, §2.2.5]. This is a LR-grammar and it's not suitable for top-down parsing because it contains left recursion.
```
EXPR    -> EXPR + TERM
        |  EXPR - TERM
        |  TERM

TERM    -> TERM * FACTOR
        |  TERM / FACTOR
        |  FACTOR

FACTOR  -> num
        | ( EXPR )
```

Rewrite this grammar in LL(1) form [1, §4.1.2].
```
EXPR    -> TERM EXPR'

EXPR'   -> + TERM EXPR'
        |  - TERM EXPR'
        |  eps

TERM    -> FACTOR TERM'
TERM'   -> * FACTOR TERM'
        -> / FACTOR TERM'
        -> eps

FACTOR  -> num
        | (EXPR)
```

Provided example can parse simple expression and print result as a Abstract Syntax Tree. Spaces in expression are not allowed.

Run example
```
cargo run --example expressions '1-3*(5+3)'
```
Example output
```
Expr(Term(Factor(Num(1)), Eps), Expr1(Op(MINUS), Term(Factor(Num(3)), Term1(Op(MULT), Factor(Expr(Term(Factor(Num(5)), Eps), Expr1(Op(PLUS), Term(Factor(Num(3)), Eps), Eps))), Eps)), Eps))
AST:
EXPR
 ├─TERM
 │  ├─FACTOR
 │  │  └─NUM(1)
 │  └─ε
 └─EXPR'
    ├─OP(-)
    ├─TERM
    │  ├─FACTOR
    │  │  └─NUM(3)
    │  └─TERM'
    │     ├─OP(*)
    │     ├─FACTOR
    │     │  └─EXPR
    │     │     ├─TERM
    │     │     │  ├─FACTOR
    │     │     │  │  └─NUM(5)
    │     │     │  └─ε
    │     │     └─EXPR'
    │     │        ├─OP(+)
    │     │        ├─TERM
    │     │        │  ├─FACTOR
    │     │        │  │  └─NUM(3)
    │     │        │  └─ε
    │     │        └─ε
    │     └─ε
    └─ε
```

# References
1. Aho, A. V. (2007). Compilers: Principles, Techniques, & Tools. Pearson. 2nd Edition.
