mod combinators;
mod expression;

fn main() {
    let input = "(1+2)*3";
    let res = expression::nt_expr(input);
    let res = res.unwrap();
    println!("Input: {}", input);
    println!("{:?}", res.value);
    println!("AST:\n{}", res.value);
}
