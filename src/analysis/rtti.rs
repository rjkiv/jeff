use std::collections::BTreeMap;

use anyhow::Result;

use crate::{
    analysis::cfa::SectionAddress,
    obj::{ObjInfo, SectionIndex, SymbolIndex},
};

struct BaseClassDescriptor {
    pub symbol_index: SymbolIndex,
    pub identifiers: [i32; 4],
}

struct CompleteObjectLocator {
    // the symbol index for the Complete Object Locator
    pub object_locator_index: SymbolIndex,
    // the symbol index for the corresponding vftable
    pub vftable_index: Option<SymbolIndex>,
    // the name of this object locator's superclass
    pub superclass_name: Option<String>,
}

// A class that uses RTTI.
#[derive(Default)]
struct RTTIObject {
    // A class using RTTI can only ever have one type descriptor, class hierarchy descriptor, and base class array

    // we want the symbol index of the Type Descriptor object so we can rename it later
    // if we have the symbol index, we also effectively have the address of the symbol
    // because we can grab it via ObjSymbol obj.symbols[SymbolIndex].clone()'s addr field;
    pub type_descriptor: Option<SymbolIndex>,

    pub class_hierarchy_descriptor: Option<SymbolIndex>,
    pub uses_multiple_inheritance: bool,
    pub uses_virtual_inheritance: bool,
    pub num_base_classes: u32,

    pub base_class_array: Option<SymbolIndex>,

    // however, it can have multiple complete object locators, one per superclass
    // it will also have one vftable per object locator
    pub complete_object_locators: Vec<CompleteObjectLocator>,

    // it can also potentially have more than one base class descriptor if multiple subclasses inherit from it
    pub base_class_descriptors: Vec<BaseClassDescriptor>,
}

struct RTTIMetadata {
    // populated when searching for Type Descriptor entries
    type_info_vtable_addr: Option<SectionAddress>,
    // key = addr of the Type Descriptor entry, value = the TD entry metadata
    // this map is used once Type Descriptor entries have been found,
    // and you then need to find the rest of the RTTI objects
    // because it's easier to search when the Type Descriptor addr is the key
    rtti_type_descriptor_entries: BTreeMap<u32, String>,
    // key = the type name, value = all the RTTI object addresses
    rtti_data_by_name: BTreeMap<String, RTTIObject>,
}

impl Default for RTTIMetadata {
    fn default() -> Self {
        Self {
            type_info_vtable_addr: None,
            rtti_type_descriptor_entries: BTreeMap::new(),
            rtti_data_by_name: BTreeMap::new(),
        }
    }
}

// Set the Class Hierarchy Descriptor address if we don't have it, or verify that it's the same as what we've got.
fn set_class_hierarchy_descriptor(
    obj: &ObjInfo,
    rtti: &mut RTTIObject,
    rdata_section: SectionIndex,
    class_hierarchy_descriptor_addr: u32,
) -> Result<()> {
    // from the supplied Class Hierarchy Descriptor Address, get the corresponding SymbolIndex
    let orig_type_info_symbol_info: Vec<_> =
        obj.symbols.at_section_address(rdata_section, class_hierarchy_descriptor_addr).collect();
    match rtti.class_hierarchy_descriptor {
        Some(desc) => {
            for (orig_sym_idx, orig_sym) in orig_type_info_symbol_info {
                assert_eq!(
                    orig_sym_idx, desc,
                    "Found different Class Hierarchy Descriptor locations!"
                );
                break;
            }
        }
        None => {
            for (orig_sym_idx, orig_sym) in orig_type_info_symbol_info {
                rtti.class_hierarchy_descriptor = Some(orig_sym_idx);
                break;
            }
        }
    }
    Ok(())
}

// str from_utf8 doesn't stop at the null terminator
// why would it? that would make life too easy
fn cstr_slice_to_str(bytes: &[u8]) -> Result<&str, std::str::Utf8Error> {
    let end = bytes.iter().position(|&b| b == 0).unwrap_or(bytes.len());
    std::str::from_utf8(&bytes[..end])
}

// Finds RTTI Type Descriptor symbols, and type_info's vtable.
fn find_rtti_type_descriptors(obj: &mut ObjInfo, rtti: &mut RTTIMetadata) -> Result<()> {
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
            if let Some(global_vtable_addr) = rtti.type_info_vtable_addr {
                // check that the one we just read is the same, as there can only be one unique type info vtable addr
                assert_eq!(
                    global_vtable_addr.address, this_vtable_addr,
                    "type_info::vftable address mismatch!"
                );
            } else {
                // else, populate the global vtable addr with this one
                let the_vtable_sec_idx = obj.sections.at_address(this_vtable_addr)?.0;
                rtti.type_info_vtable_addr =
                    Some(SectionAddress::new(the_vtable_sec_idx, this_vtable_addr));
            }

            let should_be_zero = u32::from_be_bytes(sym_data[4..8].try_into()?);
            assert_eq!(should_be_zero, 0, "how on earth is this not zero");

            // purposefully skipping the . at the start
            let type_str = cstr_slice_to_str(&sym_data[9..])?;

            rtti.rtti_type_descriptor_entries.insert(sym.address as u32, type_str.to_string());
            let rtti_addrs = rtti.rtti_data_by_name.entry(type_str.to_string()).or_default();
            rtti_addrs.type_descriptor = Some(sym_idx);

            // log::debug!("Discovered RTTI Type Descriptor entry: {}", type_str);
        }
    }
    Ok(())
}

fn apply_rtti_symbols(obj: &mut ObjInfo, rtti: &RTTIMetadata) -> Result<()> {
    // apply the symbol for type_info's vtable
    if let Some(global_vtable_addr) = rtti.type_info_vtable_addr {
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
    // and each of the RTTI object entries
    for (name, addrs) in &rtti.rtti_data_by_name {
        // RTTI Type Descriptors
        if let Some(symbol_idx) = &addrs.type_descriptor {
            let mut new_sym = obj.symbols[*symbol_idx].clone();
            // example:
            // Type Descriptor class name (. omitted): ?AVFilePath@@
            // Type Descriptor full symbol: ??_R0?AVFilePath@@@8
            new_sym.name = format!("??_R0{}@8", name);
            // edit the descriptor's size to only be the vtable addr, zero word, and the string length
            new_sym.size = 8 + name.len() as u64;
            // shoutout 4 byte alignment
            new_sym.size = new_sym.size.next_multiple_of(4);
            obj.symbols.replace(*symbol_idx, new_sym)?;
        } else {
            unreachable!();
        }
        // RTTI Class Hierarchy Descriptors
        if let Some(symbol_idx) = &addrs.class_hierarchy_descriptor {
            let mut new_sym = obj.symbols[*symbol_idx].clone();
            // example:
            // Type Descriptor class name (. omitted): ?AVFilePath@@
            // Class Hierarchy Descriptor full symbol: ??_R3FilePath@@8
            new_sym.name = format!("??_R3{}8", name[3..].to_string());
            obj.symbols.replace(*symbol_idx, new_sym)?;
        }
        // RTTI Base Class Arrays
        if let Some(symbol_idx) = &addrs.base_class_array {
            let mut new_sym = obj.symbols[*symbol_idx].clone();
            // example:
            // Type Descriptor class name (. omitted): ?AVFilePath@@
            // Class Hierarchy Descriptor full symbol: ??_R2FilePath@@8
            new_sym.name = format!("??_R2{}8", name[3..].to_string());
            obj.symbols.replace(*symbol_idx, new_sym)?;
        }
        // TODO: RTTI Complete Object Locators
        // TODO: RTTI Base Class Descriptors
    }
    Ok(())
}

fn find_remaining_rtti_structs(obj: &mut ObjInfo, rtti: &mut RTTIMetadata) -> Result<()> {
    let Some((section_index, section)) = obj.sections.by_name(".rdata")? else {
        // No .rdata section
        return Ok(());
    };

    // the remaining RTTI structures live in .rdata
    for (sym_idx, sym) in obj.symbols.for_section(section_index) {
        // this obviously would not apply to strings
        if sym.name.starts_with("str_") {
            continue;
        }
        // the objects we care about are all at least 16 bytes
        if sym.size < 16 {
            continue;
        }

        let sym_data = section.symbol_data(sym)?; // data_range

        // if the first word is a Type Descriptor address, this is a Base Class Descriptor
        if let Some(cur_rtti_type_name) =
            rtti.rtti_type_descriptor_entries.get(&u32::from_be_bytes(sym_data[0..4].try_into()?))
        {
            log::debug!("RTTI Base Class Descriptor found at: {:#08X}", sym.address as u32);

            // base class descriptors are 28 bytes / 7 words
            let base_class_descriptor_data =
                section.data_range(sym.address as u32, sym.address as u32 + 28)?;

            let cur_rtti_obj = rtti.rtti_data_by_name.get_mut(cur_rtti_type_name).expect("Type Descriptor entry exists in the address lookup map, but not the name lookup map");
            // words 3,4,5,6 are identifiers used to make the symbol
            cur_rtti_obj.base_class_descriptors.push(BaseClassDescriptor {
                symbol_index: sym_idx,
                identifiers: [
                    i32::from_be_bytes(base_class_descriptor_data[8..12].try_into()?),
                    i32::from_be_bytes(base_class_descriptor_data[12..16].try_into()?),
                    i32::from_be_bytes(base_class_descriptor_data[16..20].try_into()?),
                    i32::from_be_bytes(base_class_descriptor_data[20..24].try_into()?),
                ],
            });
            // finally, word 7 is the address of the Class Hierarchy Descriptor
            set_class_hierarchy_descriptor(
                obj,
                cur_rtti_obj,
                section_index,
                u32::from_be_bytes(base_class_descriptor_data[24..28].try_into()?),
            )?;
        }
        // if the 4th word is a Type Descriptor address, this is a Complete Object Locator
        else if let Some(cur_rtti_type_name) =
            rtti.rtti_type_descriptor_entries.get(&u32::from_be_bytes(sym_data[12..16].try_into()?))
        {
            log::debug!("RTTI Complete Object Locator found at: {:#08X}", sym.address as u32);

            // base class descriptors are 20 bytes / 5 words
            let base_class_descriptor_data =
                section.data_range(sym.address as u32, sym.address as u32 + 20)?;

            let cur_rtti_obj = rtti.rtti_data_by_name.get_mut(cur_rtti_type_name).expect("Type Descriptor entry exists in the address lookup map, but not the name lookup map");
            cur_rtti_obj.complete_object_locators.push(CompleteObjectLocator {
                object_locator_index: sym_idx,
                vftable_index: None,
                superclass_name: None,
            });
            set_class_hierarchy_descriptor(
                obj,
                cur_rtti_obj,
                section_index,
                u32::from_be_bytes(base_class_descriptor_data[16..20].try_into()?),
            )?;
        }
    }

    // we found each RTTI object's Class Hierarchy Descriptor index, but not currently analyzed
    // this loop will analyze them and get us the Base Class Array and other inheritance metadata
    for (name, rtti_obj) in &mut rtti.rtti_data_by_name {
        if let Some(class_hierarchy_sym_idx) = rtti_obj.class_hierarchy_descriptor {
            // we need the data from the class hierarchy descriptor here
            let sym = &obj.symbols[class_hierarchy_sym_idx];
            // class hierarchy descriptors are 16 bytes / 4 words
            let class_hierarchy_data =
                section.data_range(sym.address as u32, sym.address as u32 + 28)?;

            let attributes = u32::from_be_bytes(class_hierarchy_data[4..8].try_into()?);
            rtti_obj.uses_multiple_inheritance = if attributes & 1 != 0 { true } else { false };
            rtti_obj.uses_virtual_inheritance = if attributes & 2 != 0 { true } else { false };
            rtti_obj.num_base_classes = u32::from_be_bytes(class_hierarchy_data[8..12].try_into()?);
            let base_class_array_addr =
                u32::from_be_bytes(class_hierarchy_data[12..16].try_into()?);
            let base_class_array_symbol_info: Vec<_> =
                obj.symbols.at_section_address(section_index, base_class_array_addr).collect();
            for (orig_sym_idx, orig_sym) in base_class_array_symbol_info {
                rtti_obj.base_class_array = Some(orig_sym_idx);
                break;
            }
        }
        // no unreachable!() else case here, because some Type Descriptors legit just don't have other RTTI metadata
    }

    // now we just need the vftables/superclass names from the Complete Object Locators

    Ok(())
}

// useful resource: https://github.com/Chaoses-Ib/Cpp/blob/main/Languages/C++/Types/Run-Time%20Type%20Information.md
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

    let mut rtti_metadata: RTTIMetadata = Default::default();

    // first, find the RTTI Type Descriptors
    find_rtti_type_descriptors(obj, &mut rtti_metadata)?;

    // with the RTTI Type Descriptor info, find the remaining RTTI structures
    find_remaining_rtti_structs(obj, &mut rtti_metadata)?;

    apply_rtti_symbols(obj, &rtti_metadata)?;
    Ok(())
}
