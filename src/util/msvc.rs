use std::cmp::min;

use crc::{Algorithm, Crc};

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
pub fn encode_unsigned_num(num: u32) -> String {
    // <non-negative integer> ::= A@              # when Number == 0
    //                        ::= <decimal digit> # when 1 <= Number <= 10
    //                        ::= <hex digit>+ @  # when Number >= 10
    // <number>               ::= [?] <non-negative integer>
    let mut ret = String::new();
    let eval = num;
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

const SPECIAL_CHARS: [char; 10] = [',', '/', '\\', ':', '.', ' ', '\n', '\t', '\'', '-'];

fn encode_byte(out: &mut String, byte: u8) {
    // There are five different manglings for characters:
    // - [a-zA-Z0-9_$]: A one-to-one mapping.
    // - ?[a-z]: The range from \xe1 to \xfa.
    // - ?[A-Z]: The range from \xc1 to \xda.
    // - ?[0-9]: The set of [,/\:. \n\t'-].
    // - ?$XX: A fallback which maps nibbles.

    if (byte >= 'a' as u8 && byte <= 'z' as u8)
        || (byte >= 'A' as u8 && byte <= 'Z' as u8)
        || (byte >= '0' as u8 && byte <= '9' as u8)
        || byte == '_' as u8
        || byte == '$' as u8
    {
        out.push(byte as char);
    } else if (byte >= 0xC1 && byte <= 0xDA) || (byte >= 0xE1 && byte <= 0xFA) {
        out.push('?');
        out.push((byte & 0x7F) as char);
    } else {
        // for these, you have to push ?, then the index into the special chars array
        let idx = SPECIAL_CHARS.iter().position(|&c| c as u8 == byte);
        match idx {
            Some(idx) => out.push_str(format!("?{}", idx).as_str()),
            // fallback, map nibbles
            None => {
                out.push_str("?$");
                out.push(('A' as u8 + ((byte >> 4) & 0xF)) as char);
                out.push(('A' as u8 + (byte & 0xF)) as char);
            }
        }
    }
}

const JAM_CRC: Algorithm<u32> = Algorithm {
    width: 32,
    poly: 0x04C11DB7,
    init: 0xFFFFFFFF,
    refin: true,
    refout: true,
    xorout: 0,
    check: 0x340BC6D9,
    residue: 0,
};

// stole llvm's mangleStringLiteral for this one
pub fn encode_narrow_string_literal(str: &str) -> String {
    // <char-type> ::= 0   # char, char16_t, char32_t
    //                     # (little endian char data in mangling)
    //             ::= 1   # wchar_t (big endian char data in mangling)
    //
    // <literal-length> ::= <non-negative integer>  # the length of the literal
    //
    // <encoded-crc>    ::= <hex digit>+ @          # crc of the literal including
    //                                              # trailing null bytes
    //
    // <encoded-string> ::= <simple character>           # uninteresting character
    //                  ::= '?$' <hex digit> <hex digit> # these two nibbles
    //                                                   # encode the byte for the
    //                                                   # character
    //                  ::= '?' [a-z]                    # \xe1 - \xfa
    //                  ::= '?' [A-Z]                    # \xc1 - \xda
    //                  ::= '?' [0-9]                    # [,/\:. \n\t'-]
    //
    // <literal> ::= '??_C@_' <char-type> <literal-length> <encoded-crc>
    //               <encoded-string> '@'
    let mut ret = String::new();
    ret.push_str("??_C@_");
    ret.push('0');
    let str_len = str.len() + 1;
    ret.push_str(encode_num(str_len as i32).as_str());

    let crc = Crc::<u32>::new(&JAM_CRC);
    // the null terminator for a string gets included in the CRC
    let mut cstr = str.as_bytes().to_vec();
    cstr.push(0);
    let hash = crc.checksum(&cstr);
    ret.push_str(encode_unsigned_num(hash).as_str());

    // now, encode no more than the first 32 bytes
    let num_bytes_to_mangle = min(32, cstr.len());

    for i in 0..num_bytes_to_mangle {
        encode_byte(&mut ret, cstr[i]);
    }

    // then push an @
    ret.push('@');

    ret
}

pub fn encode_wide_string_literal(wstr: &str) -> String {
    let mut ret = String::new();
    ret.push_str("??_C@_");
    ret.push('1');

    // we need the null terminator, come on rust
    let mut cwstr: Vec<u16> = wstr.encode_utf16().collect();
    cwstr.push(0);

    let wstr_byte_size = cwstr.len() * 2;

    ret.push_str(encode_num(wstr_byte_size as i32).as_str());

    let mut crc_bytes = Vec::with_capacity(wstr_byte_size);
    for wchar in &cwstr {
        // llvm does le_bytes, xbox 360 went be_bytes. xbox 360 isn't like the other girls 💅
        crc_bytes.extend(wchar.to_be_bytes());
    }

    let crc = Crc::<u32>::new(&JAM_CRC);
    let hash = crc.checksum(&crc_bytes);
    ret.push_str(encode_unsigned_num(hash).as_str());

    // now, encode no more than the first 32 characters
    let num_bytes_to_mangle = min(64, wstr_byte_size);

    // so it goes BE for the CRC, but back to LE for the individual wchar mangling?
    // ok microsoft epic sick
    for i in (0..num_bytes_to_mangle).step_by(2) {
        encode_byte(&mut ret, crc_bytes[i + 1]);
        encode_byte(&mut ret, crc_bytes[i]);
    }

    // then push an @
    ret.push('@');

    ret
}
