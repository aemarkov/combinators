# Simple Parser Combinators

Play around with homemade parser combinators. See the real parser combinators libraries: [Nom](https://github.com/rust-bakery/nom), [Combine](https://github.com/Marwes/combine), [Parsec](https://hackage.haskell.org/package/parsec).

Parser combinator able to parse LL(1) grammar. However, as far I understand, it able to parse not-LL grammar but with exponential time and possibility to fall into a infinite recursion.

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

# References
1. Aho, A. V. (2007). Compilers: Principles, Techniques, & Tools. Pearson. 2nd Edition.
