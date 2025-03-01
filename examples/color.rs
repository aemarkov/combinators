use combinators::*;

/* Parses color in various formats
 - hex: #aabbcc
 - rgb: rgb(170, 187, 204)
*/

/// Parses HEX color, e.g. #aabbcc
fn hex_color<'a>() -> impl FnOnce(&'a str) -> ParserResult<(u8, u8, u8)> {
    map(
        and2(tag("#"), and3(hex_byte(), hex_byte(), hex_byte())),
        |(_, rgb)| rgb,
    )
}

/// Parses 2-digits HEX byte, e.g. "aa"
fn hex_byte<'a>() -> impl FnOnce(&'a str) -> ParserResult<u8> {
    |str: &'a str| {
        take(2)(str).and_then(|x| {
            u8::from_str_radix(x.value, 16)
                .ok()
                .map(|y| parsed(y, x.residual))
        })
    }
}

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hex_byte() {
        let res = hex_byte()("abcdef");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, 0xab);
        assert_eq!(res.unwrap().residual, "cdef");

        let res = hex_byte()("a");
        assert!(res.is_none());
    }

    #[test]
    fn test_hex_color() {
        let res = hex_color()("#abcdefblabla");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, (0xab, 0xcd, 0xef));
        assert_eq!(res.unwrap().residual, "blabla");

        let res = hex_color()("abcde");
        assert!(res.is_none());
    }

    #[test]
    fn test_rgb_color() {
        let res = rgb_color()("rgb( 220, 230 , 100   )bla");
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, (220, 230, 100));
        assert_eq!(res.unwrap().residual, "bla");

        let res = rgb_color()("rgb(220, 230");
        assert!(res.is_none());
    }
}

fn main() {
    let input = "#aabbcc";
    let res = hex_color()(input);
    println!("Input:  {}", input);
    println!("Color:  {:?}", res.unwrap().value);

    let input = "rgb(10, 20, 30)";
    let res = rgb_color()(input);
    println!("Input:  {}", input);
    println!("Color:  {:?}", res.unwrap().value);
}
