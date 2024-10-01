mod combinators;
mod expression;

fn main() {
    let input = "1+2-3+4-5+1";
    let res = expression::nt_expr(input);
    println!("Input: {}", input);
    println!("AST:   {}", res.unwrap().value);
}
