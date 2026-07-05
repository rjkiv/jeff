use anyhow::Result;

use crate::{
    analysis::cfa::SectionAddress,
    obj::{ObjInfo, SymbolIndex},
};

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

// str from_utf8 doesn't stop at the null terminator
// why would it? that would make life too easy
fn cstr_slice_to_str(bytes: &[u8]) -> Result<&str, std::str::Utf8Error> {
    let end = bytes.iter().position(|&b| b == 0).unwrap_or(bytes.len());
    std::str::from_utf8(&bytes[..end])
}

// Finds and applies RTTI Type Descriptor symbols. Also does this with type_info's vtable.
fn find_rtti_type_descriptors(
    obj: &mut ObjInfo,
    entries: &mut RTTITypeDescriptorEntries,
) -> Result<()> {
    let Some((section_index, section)) = obj.sections.by_name(".data")? else {
        // No .data section
        return Ok(());
    };

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
            if let Some(global_vtable_addr) = entries.type_info_vtable_addr {
                // check that the one we just read is the same, as there can only be one unique type info vtable addr
                assert_eq!(
                    global_vtable_addr.address, this_vtable_addr,
                    "type_info::vftable address mismatch!"
                );
            } else {
                // else, populate the global vtable addr with this one
                let the_vtable_sec_idx = obj.sections.at_address(this_vtable_addr)?.0;
                entries.type_info_vtable_addr =
                    Some(SectionAddress::new(the_vtable_sec_idx, this_vtable_addr));
            }

            let should_be_zero = u32::from_be_bytes(sym_data[4..8].try_into()?);
            assert_eq!(should_be_zero, 0, "how on earth is this not zero");

            // purposefully skipping the . at the start
            let type_str = cstr_slice_to_str(&sym_data[9..])?;

            entries.entries.push(RTTITypeDescriptorEntry {
                symbol_index: sym_idx,
                entry_addr: sym.address,
                name: type_str.to_string(),
            });

            log::debug!("Discovered RTTI Type Descriptor entry: {}", type_str);
        }
    }

    // apply the symbol for type_info's vtable
    if let Some(global_vtable_addr) = entries.type_info_vtable_addr {
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
    for td_entry in entries.entries.iter() {
        let mut new_sym = obj.symbols[td_entry.symbol_index].clone();
        // example:
        // Type Descriptor class name (. omitted): ?AVFilePath@@
        // Type Descriptor full symbol: ??_R0?AVFilePath@@@8
        new_sym.name = format!("??_R0{}@8", td_entry.name);
        obj.symbols.replace(td_entry.symbol_index, new_sym)?;
    }

    Ok(())
}

pub fn detect_rtti(obj: &mut ObjInfo) -> Result<()> {
    if !obj.rtti {
        log::debug!("This object does not use RTTI, skipping");
        return Ok(());
    }

    // TODO:
    // this should also detect and label __RTtypeid and __RTDynamicCast
    // fix __RTtypeid and __RTDynamicCast so there's no dangling fn's
    // "Bad dynamic_cast!" would mean dynamic cast exists
    // "Attempted a typeid of NULL pointer!" would mean typeid exists

    let mut rtti_td_entries = RTTITypeDescriptorEntries::default();

    find_rtti_type_descriptors(obj, &mut rtti_td_entries)?;

    // with the RTTI Type Descriptor info, find the remaining RTTI structures

    Ok(())
}
