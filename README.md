# Simple Parser Combinators

Play around with homemade parser combinators. See the real parser combinators libraries: [Nom](https://github.com/rust-bakery/nom), [Combine](https://github.com/Marwes/combine), [Parsec](https://hackage.haskell.org/package/parsec).

Parser combinator able to parse LL(1) grammar. However, as far I understand, it able to parse not-LL grammar but with exponential time and possibility to fall into a infinite recursion.

Example LL(1) grammar to parse simple arithmetic expressions.
```
EXPR  = MULT ADD
ADD   = + MULT ADD |
        - MULT ADD |
        eps
MULT  = TERM MULT'
MULT' = * TERM MULT' |
        / TERM MULT' |
        eps
TERM  = num | ( EXPR )
```

