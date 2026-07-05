use anyhow::Result;

use crate::{
    analysis::cfa::SectionAddress,
    obj::{ObjDataKind, ObjInfo, ObjSectionKind, ObjSymbolKind, SymbolIndex},
    util::{config::is_auto_symbol, split::is_linker_generated_label},
};

pub fn detect_objects(obj: &mut ObjInfo) -> Result<()> {
    for (section_index, section) in
        obj.sections.iter_mut().filter(|(_, s)| s.kind != ObjSectionKind::Code)
    {
        let section_end = (section.address + section.size) as u32;

        let mut replace_symbols = vec![];
        for (idx, symbol) in obj.symbols.for_section(section_index) {
            let mut symbol = symbol.clone();
            if is_linker_generated_label(&symbol.name) || symbol.name.starts_with("..") {
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
                log::debug!("Guessed {} size {:#X}", symbol.name, new_size);
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
    }
    Ok(())
}

struct DetectedString {
    pub idx: SymbolIndex,
    pub kind: ObjDataKind,
    pub size: usize,
    // future field for mangling detected strings directly into MSVC symbols
    pub demangled_name: Option<String>,
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
        pub const fn trim_zeroes_end(mut bytes: &[u8]) -> &[u8] {
            while let [rest @ .., last] = bytes {
                if *last == 0 {
                    bytes = rest;
                } else {
                    break;
                }
            }
            bytes
        }
        fn is_string(data: &[u8]) -> StringResult {
            let bytes = trim_zeroes_end(data);
            if bytes.is_empty() {
                return StringResult::None;
            }
            if bytes.iter().all(|&c| c.is_ascii_graphic() || c.is_ascii_whitespace()) {
                return StringResult::String {
                    length: bytes.len(),
                    terminated: data.len() > bytes.len(),
                };
            }
            if bytes.len() % 2 == 0 && data.len() >= bytes.len() + 2 {
                // Found at least 2 bytes of trailing 0s, check UTF-16
                let mut ok = true;
                let mut str = String::new();
                for n in std::char::decode_utf16(
                    bytes.chunks_exact(2).map(|c| u16::from_be_bytes(c.try_into().unwrap())),
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
                    return StringResult::WString { length: bytes.len(), str };
                }
            }
            StringResult::None
        }
        for (symbol_idx, symbol) in obj
            .symbols
            .for_section(section_index)
            .filter(|(_, sym)| sym.data_kind == ObjDataKind::Unknown)
        {
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
                            demangled_name: Some(str.to_string()),
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
                            demangled_name: Some(str.clone()),
                        });
                    }
                }
            }
        }
    }

    for entry in symbols_set.iter() {
        let mut symbol = obj.symbols[entry.idx].clone();

        // if we see a string involving dynamic casting, we've got RTTI
        // this specific string is thrown in an std::exception, so it should also be detectable in retail builds
        if let Some(the_string) = &entry.demangled_name {
            if the_string == "Bad dynamic_cast!" {
                obj.rtti = true;
            }
        }

        // TODO: create an MSVC mangled representation of the string, and have that be the new symbol name
        symbol.name = format!("str_{:08X}", symbol.address as u32);
        log::debug!("Setting {} ({:#010X}) to size {:#X}", symbol.name, symbol.address, entry.size);
        symbol.data_kind = entry.kind;
        symbol.size = entry.size as u64;
        symbol.size_known = true;
        obj.symbols.replace(entry.idx, symbol)?;
    }
    Ok(())
}

struct RTTITypeDescriptorEntry {
    pub symbol_index: SymbolIndex,
    pub entry_addr: u64,
    pub name: String,
}
struct RTTITypeDescriptorEntries {
    pub type_info_vtable_addr: Option<SectionAddress>,
    pub entries: Vec<RTTITypeDescriptorEntry>,
}

impl Default for RTTITypeDescriptorEntries {
    fn default() -> Self { Self { type_info_vtable_addr: None, entries: Vec::new() } }
}

pub fn detect_rtti(obj: &mut ObjInfo) -> Result<()> {
    if !obj.rtti {
        log::debug!("This object does not use RTTI, skipping");
        return Ok(());
    }

    let Some((section_index, section)) = obj.sections.by_name(".data")? else {
        // No .data section
        return Ok(());
    };

    // this should also detect and label __RTtypeid and __RTDynamicCast

    // str from_utf8 doesn't stop at the null terminator
    // why would it? that would make life too easy
    fn cstr_slice_to_str(bytes: &[u8]) -> Result<&str, std::str::Utf8Error> {
        let end = bytes.iter().position(|&b| b == 0).unwrap_or(bytes.len());
        std::str::from_utf8(&bytes[..end])
    }

    let mut rtti_td_entries = RTTITypeDescriptorEntries::default();

    // find the RTTI type descriptors in .data
    for (sym_idx, sym) in obj.symbols.for_section(section_index) {
        // 4 bytes for the type_info vtable, 4 bytes of 0, then the name - will start with ".?AU" for structs or ".?AV" for classes
        if sym.size < 12 {
            continue;
        }

        let sym_data = section.symbol_data(sym)?;
        if &sym_data[8..12] == b".?AU" || &sym_data[8..12] == b".?AV" {
            let this_vtable_addr = u32::from_be_bytes(sym_data[0..4].try_into()?);

            // if we've already set the global type info vtable addr
            if let Some(global_vtable_addr) = rtti_td_entries.type_info_vtable_addr {
                // check that the one we just read is the same, as there can only be one unique type info vtable addr
                assert_eq!(
                    global_vtable_addr.address, this_vtable_addr,
                    "type_info::vftable address mismatch!"
                );
            } else {
                // else, populate the global vtable addr with this one
                let the_vtable_sec_idx = obj.sections.at_address(this_vtable_addr)?.0;
                rtti_td_entries.type_info_vtable_addr =
                    Some(SectionAddress::new(the_vtable_sec_idx, this_vtable_addr));
            }

            let should_be_zero = u32::from_be_bytes(sym_data[4..8].try_into()?);
            assert_eq!(should_be_zero, 0, "how on earth is this not zero");

            // purposefully skipping the . at the start
            let type_str = cstr_slice_to_str(&sym_data[9..])?;

            rtti_td_entries.entries.push(RTTITypeDescriptorEntry {
                symbol_index: sym_idx,
                entry_addr: sym.address,
                name: type_str.to_string(),
            });
            log::debug!("Discovered RTTI Type Descriptor entry: {}", type_str);
        }
    }

    // this is where you apply the symbol for type_info's vtable
    if let Some(global_vtable_addr) = rtti_td_entries.type_info_vtable_addr {
        let orig_type_info_symbol_info: Vec<_> = obj
            .symbols
            .at_section_address(global_vtable_addr.section, global_vtable_addr.address)
            .collect();
        for (orig_sym_idx, orig_sym) in orig_type_info_symbol_info {
            let mut new_sym = orig_sym.clone();
            new_sym.name = "??_7type_info@@6B@".to_string();
            obj.symbols.replace(orig_sym_idx, new_sym)?;
            break;
        }
    } else {
        unreachable!("So you have RTTI, but no global type info vtable addr?");
    }
    // and each of the RTTI Type Descriptor entries
    for td_entry in rtti_td_entries.entries.iter() {
        let mut new_sym = obj.symbols[td_entry.symbol_index].clone();
        // example:
        // Type Descriptor class name (. omitted): ?AVFilePath@@
        // Type Descriptor full symbol: ??_R0?AVFilePath@@@8
        new_sym.name = format!("??_R0{}@8", td_entry.name);
        obj.symbols.replace(td_entry.symbol_index, new_sym)?;
    }

    Ok(())
}
