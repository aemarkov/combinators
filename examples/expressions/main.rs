mod expression;

fn parse_args() -> Option<String> {
    if std::env::args().len() != 2 {
        return None;
    }

    return std::env::args().nth(1);
}

fn main() {
    if let Some(input) = parse_args() {
        if let Some(res) = expression::nt_expr(&input) {
            println!("{:?}", res.value);
            println!("AST:\n{}", res.value);
        } else {
            println!("Failed to parse");
        }
    } else {
        println!("Invalid arguments");
    }
}
