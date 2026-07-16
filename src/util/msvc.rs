// i had to steal this from LLVM's MicrosoftCXXNameMangler::mangleNumber and mangleBits
pub fn encode_num(num: i32) -> String {
    // <non-negative integer> ::= A@              # when Number == 0
    //                        ::= <decimal digit> # when 1 <= Number <= 10
    //                        ::= <hex digit>+ @  # when Number >= 10
    // <number>               ::= [?] <non-negative integer>
    let mut ret = String::new();
    let mut eval = num;
    if eval < 0 {
        eval = -eval;
        ret.push('?');
    }
    if eval == 0 {
        ret.push_str("A@");
    } else if eval >= 1 && eval <= 10 {
        ret += &*(eval - 1).to_string();
    } else {
        let mut digits = Vec::new();
        let mut value = eval as u32;
        while value != 0 {
            let nibble = (value & 0xF) as u8;
            digits.push((b'A' + nibble) as char);
            value >>= 4;
        }
        digits.reverse();
        for ch in digits {
            ret.push(ch);
        }
        ret.push('@');
    }
    ret
}
