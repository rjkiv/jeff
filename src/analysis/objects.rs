use anyhow::{ensure, Result};

use crate::{
    obj::{ObjDataKind, ObjInfo, ObjSectionKind, ObjSymbolKind, SymbolIndex},
    util::{
        config::is_auto_symbol,
        msvc::{encode_narrow_string_literal, encode_wide_string_literal},
    },
};

pub fn detect_objects(obj: &mut ObjInfo) -> Result<()> {
    for (section_index, section) in obj
        .sections
        .iter_mut()
        .filter(|(_, s)| s.kind != ObjSectionKind::Code && s.name != ".pdata")
    {
        let section_end = (section.address + section.size) as u32;

        let mut replace_symbols = vec![];
        for (idx, symbol) in obj.symbols.for_section(section_index) {
            let mut symbol = symbol.clone();
            if symbol.name.starts_with("..") {
                continue;
            }
            let expected_size = match symbol.data_kind {
                ObjDataKind::Byte => 1,
                ObjDataKind::Byte2 | ObjDataKind::Short => 2,
                ObjDataKind::Byte4 | ObjDataKind::Float | ObjDataKind::Int => 4,
                ObjDataKind::Byte8 | ObjDataKind::Double => 8,
                _ => {
                    if symbol.name.contains("NULL_THUNK_DATA") {
                        4
                    } else {
                        0
                    }
                }
            };
            if !symbol.size_known {
                let next_addr = obj
                    .symbols
                    .for_section_range(section_index, symbol.address as u32 + 1..)
                    .next()
                    .map_or(section_end, |(_, symbol)| symbol.address as u32);
                let new_size = next_addr - symbol.address as u32;
                // log::debug!("Guessed {} size {:#X}", symbol.name, new_size);
                symbol.size = match (new_size, expected_size) {
                    (..=4, 1) => expected_size,
                    (2 | 4, 2) => expected_size,
                    (..=8, 1 | 2 | 4) => {
                        // alignment to double
                        if obj.symbols.at_section_address(section_index, next_addr).any(|(_, sym)| sym.data_kind == ObjDataKind::Double)
                        // If we're at a TU boundary, we can assume it's just padding
                        || section.splits.has_split_at(symbol.address as u32 + new_size)
                        {
                            expected_size
                        } else {
                            new_size
                        }
                    }
                    _ => {
                        if symbol.name.contains("NULL_THUNK_DATA") {
                            4
                        } else {
                            new_size
                        }
                    }
                } as u64;
                symbol.size_known = true;
            }
            symbol.kind = ObjSymbolKind::Object;
            if expected_size > 1 && symbol.size as u32 % expected_size != 0 {
                symbol.data_kind = ObjDataKind::Unknown;
            }
            replace_symbols.push((idx, symbol));
        }
        for (idx, symbol) in replace_symbols {
            obj.symbols.replace(idx, symbol)?;
        }

        let mut symbol_sizes_to_replace: Vec<(SymbolIndex, u32)> = vec![];

        // if we have splits at this point, they came from a map
        // adjust for any new symbol discoveries as needed
        for (split_start, split_info) in section.splits.iter_mut() {
            // we want the last ObjSymbol, such that the ObjSymbol's start address is within split_start and split_info.end
            if let Some((last_sym_idx, last_sym)) = obj
                .symbols
                .for_section_range(section_index, split_start..split_info.end)
                .next_back()
            {
                // if it goes over the split bounds, shrink the sym size so it does
                // if it turns out that's wrong, ehhhhh the user can adjust it later,
                // where they'll have an existing splits/symbols.txt and this code won't be reached
                if split_info.end < last_sym.address as u32 + last_sym.size as u32 {
                    log::debug!(
                        "Symbol at {:08X}-{:08X} goes beyond split end at {:08X}!",
                        last_sym.address,
                        last_sym.address as u32 + last_sym.size as u32,
                        split_info.end
                    );
                    symbol_sizes_to_replace.push((last_sym_idx, split_info.end));
                }
            }
        }

        for (sym, new_end) in symbol_sizes_to_replace {
            let mut new_sym = obj.symbols[sym].clone();
            new_sym.size = new_end as u64 - new_sym.address;
            log::debug!("Adjusting symbol bounds to {:08X}-{:08X}", new_sym.address, new_end);
            obj.symbols.replace(sym, new_sym)?;
        }
    }
    Ok(())
}

struct DetectedString {
    pub idx: SymbolIndex,
    pub kind: ObjDataKind,
    pub size: usize,
    pub mangled_name: Option<String>,
}

pub fn detect_strings(obj: &mut ObjInfo) -> Result<()> {
    let mut symbols_set: Vec<DetectedString> = vec![];
    for (section_index, section) in obj
        .sections
        .iter()
        .filter(|(_, s)| matches!(s.kind, ObjSectionKind::Data | ObjSectionKind::ReadOnlyData))
    {
        enum StringResult {
            None,
            String { length: usize, terminated: bool },
            WString { length: usize, str: String },
        }
        fn is_string(data: &[u8]) -> StringResult {
            // because symbol sizes are unreliable we're passing in the remaining data for the section
            // so, trim up to the first zero instead of the last
            let bytes = data.iter().position(|&b| b == 0).map(|pos| &data[..pos]).unwrap_or(data);

            // if no zeroes were stripped, probably not a string
            if bytes.len() == data.len() {
                return StringResult::None;
            }

            if !bytes.is_empty()
                && bytes.iter().all(|&c| c.is_ascii_graphic() || c.is_ascii_whitespace())
            {
                return StringResult::String {
                    length: bytes.len(),
                    terminated: data.len() > bytes.len(),
                };
            }

            // narrow bytes didn't work, try wide bytes
            let wide_bytes = data
                .chunks_exact(2)
                .position(|c| c == [0, 0])
                .map(|pos| &data[..pos * 2])
                .unwrap_or(data);

            if wide_bytes.is_empty() {
                return StringResult::None;
            }
            if wide_bytes.len() % 2 == 0 && data.len() >= wide_bytes.len() + 2 {
                // Found at least 2 bytes of trailing 0s, check UTF-16
                let mut ok = true;
                let mut str = String::new();
                for n in std::char::decode_utf16(
                    wide_bytes.chunks_exact(2).map(|c| u16::from_be_bytes(c.try_into().unwrap())),
                ) {
                    match n {
                        Ok(c) if c.is_ascii_graphic() || c.is_ascii_whitespace() => {
                            str.push(c);
                        }
                        _ => {
                            ok = false;
                            break;
                        }
                    }
                }
                if ok {
                    return StringResult::WString { length: wide_bytes.len(), str };
                }
            }
            StringResult::None
        }
        for (symbol_idx, symbol) in obj
            .symbols
            .for_section(section_index)
            .filter(|(_, sym)| sym.data_kind == ObjDataKind::Unknown)
        {
            // jump tables are not strings
            if symbol.name.starts_with("jumptable_") {
                continue;
            }
            // if the size is 1, considering there's no null terminator, it's probably not a string
            if symbol.size == 1 {
                continue;
            }
            // let's not try to search for strings that aren't 4 byte aligned - we can find those later as we actually decomp
            if symbol.address & 3 != 0 {
                continue;
            }
            let data = section.symbol_data(symbol)?;
            match is_string(data) {
                StringResult::None => {}
                StringResult::String { length, terminated } => {
                    let size = if terminated { length + 1 } else { length };
                    if symbol.size == size as u64
                        || (is_auto_symbol(symbol) && symbol.size > size as u64)
                    {
                        let str = String::from_utf8_lossy(&data[..length]);
                        log::debug!("Found string '{}' @ {}", str, symbol.name);
                        symbols_set.push(DetectedString {
                            idx: symbol_idx,
                            kind: ObjDataKind::String,
                            size,
                            mangled_name: Some(encode_narrow_string_literal(&str)),
                        });
                    }
                }
                StringResult::WString { length, str } => {
                    let size = length + 2;
                    if symbol.size == size as u64
                        || (is_auto_symbol(symbol) && symbol.size > size as u64)
                    {
                        log::debug!("Found wide string '{}' @ {}", str, symbol.name);
                        symbols_set.push(DetectedString {
                            idx: symbol_idx,
                            kind: ObjDataKind::String16,
                            size,
                            mangled_name: Some(encode_wide_string_literal(&str)),
                        });
                    }
                }
            }
        }
    }

    for entry in symbols_set.iter() {
        let mut symbol = obj.symbols[entry.idx].clone();
        symbol.name = match &entry.mangled_name {
            Some(mangled_name) => mangled_name.clone(),
            None => format!("str_{:08X}", symbol.address as u32),
        };
        symbol.data_kind = entry.kind;
        // canonically, strings are not 4 byte aligned
        symbol.size = entry.size as u64;
        symbol.size_known = true;
        log::debug!(
            "Setting {} ({:#010X}) to size {:#X}",
            symbol.name,
            symbol.address,
            symbol.size
        );
        obj.symbols.replace(entry.idx, symbol)?;
    }
    Ok(())
}
