use std::collections::BTreeMap;

use anyhow::Result;

use crate::obj::{ObjInfo, SymbolIndex};

// Info pertaining to an RTTI Object in the analyzed exe.
#[derive(Clone, Debug)]
struct RTTIExeInfo {
    pub symbol_index: SymbolIndex, // the symbol index of this RTTI Object (for labeling)
    pub addr: u32,                 // the address in the exe of this RTTI Object
}

// An RTTI Type Descriptor.
struct TypeDescriptor {
    pub exe_info: RTTIExeInfo,
    pub name: String, // the object's class name
}

// An RTTI Base Class Descriptor Object.
struct BaseClassDescriptor {
    pub exe_info: RTTIExeInfo,
    pub type_descriptor_addr: u32, // type descriptor of the class
    pub num_contained_bases: u32,  // number of nested classes following in the Base Class Array
    pub m_disp: i32,               // member displacement
    pub p_disp: i32,               // vbtable displacement
    pub v_disp: i32,               // displacement inside vbtable
    pub attributes: u32, // flags: 0x40 bit means has Class Hierarchy Descriptor, 0x10 bit means base class is virtually inherited
    pub class_hierarchy_descriptor_addr: u32,
}

// An RTTI Base Class Array object.
struct BaseClassArray {
    pub exe_info: RTTIExeInfo,
    pub base_class_descriptors: Vec<u32>, // the addresses of the BCDs that make up this Base Class Array
}

// An RTTI Class Hierarchy Descriptor object.
struct ClassHierarchyDescriptor {
    pub exe_info: RTTIExeInfo,
    pub signature: u32,             // always 0
    pub attributes: u32, // bit 0 set = multiple inheritance, bit 1 set = virtual inheritance
    pub num_base_classes: u32, // number of entries in the Base Class Array
    pub base_class_array_addr: u32, // addr of the Base Class Array
}

// An RTTI Complete Object Locator.
struct CompleteObjectLocator {
    pub exe_info: RTTIExeInfo,
    pub signature: u32, // always 0
    pub offset: u32,    // offset of this vtable in complete class (from top)
    pub cd_offset: u32, // offset of constructor displacement
    pub type_descriptor_addr: u32,
    pub class_hierarchy_descriptor_addr: u32,
    // The vftable associated with this COL
    pub vftable_addr: u32,
}

// A virtual function table.
struct VFTable {
    pub exe_info: RTTIExeInfo,
}

struct RTTIBaseClass {
    // the specific Type Descriptor for this superclass
    pub type_descriptor_addr: u32,
    pub complete_object_locator_addr: u32,
    pub vftable_addr: u32,
}

// A class that uses RTTI
#[derive(Default)]
struct RTTIClass {
    pub name: String, // this class's name
    // A class using RTTI can only ever have one type descriptor, class hierarchy descriptor, and base class array
    pub type_descriptor_addr: u32,
    pub class_hierarchy_descriptor_addr: u32,
    pub base_class_array_addr: u32,
    pub base_class_array_len: u32, // for ez reference, preventing a BCA lookup for it
    // Technically an RTTIClass can have multiple BCDs, depending on how many other classes inherit from it,
    // but this field will store the BCD for this class itself, sourced from the first entry in the BCA.
    pub base_class_descriptor_addr: u32,
    // But, it can have multiple base classes, each with their own COL and vftable
    // this field will be for when everything is properly computed and organized
    pub base_classes: Vec<RTTIBaseClass>,
    // this is meant to be loose, for tracking discovered addrs that haven't yet been organized into proper RTTIBaseClasses
    pub direct_base_class_descriptor_addrs: Vec<u32>,
    // only need to track COLs, since those have a vftable field anyway
    pub unresolved_col_addrs: Vec<u32>,
    pub has_any_virtual_inheritance: bool,
}

// RTTI Metadata to be passed between functions.
#[derive(Default)]
struct RTTIMetadata {
    // this will be populated when searching for Type Descriptor entries
    pub type_info_vtable: Option<RTTIExeInfo>,
    // key = type descriptor addr, value = the RTTI class
    pub discovered_classes: BTreeMap<u32, RTTIClass>,
    // LOOKUP MAPS - quick lookup for RTTI Objects via their address in the exe
    pub base_class_descriptor_lookup: BTreeMap<u32, BaseClassDescriptor>,
    pub base_class_array_lookup: BTreeMap<u32, BaseClassArray>,
    pub class_hierarchy_descriptor_lookup: BTreeMap<u32, ClassHierarchyDescriptor>,
    pub complete_object_locator_lookup: BTreeMap<u32, CompleteObjectLocator>,
    pub type_descriptor_lookup: BTreeMap<u32, TypeDescriptor>,
    pub vftable_lookup: BTreeMap<u32, VFTable>,
}

impl RTTIMetadata {
    // method to walk inheritance tree for TDs?
    // methods to get from lookups?
    fn get_type_descriptor(&self, addr: u32) -> &TypeDescriptor {
        self.type_descriptor_lookup.get(&addr).unwrap_or_else(|| {
            unreachable!("Invalid Type Descriptor addr {:08X}", addr);
        })
    }
}

// i had to steal this from LLVM's MicrosoftCXXNameMangler::mangleNumber and mangleBits
fn encode_num(num: i32) -> String {
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

fn find_rtti_type_descriptors(obj: &ObjInfo, rtti: &mut RTTIMetadata) -> Result<()> {
    let Some((section_index, section)) = obj.sections.by_name(".data")? else {
        unreachable!("RTTI being used, but there's no .data section???");
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
            if let Some(global_vtable) = &rtti.type_info_vtable {
                // check that the one we just read is the same, as there can only be one unique type info vtable addr
                assert_eq!(
                    global_vtable.addr, this_vtable_addr,
                    "type_info::vftable address mismatch!"
                );
            } else {
                // else, populate the global vtable addr with this one
                // need the symbol index of type info's vtable - sym_idx == the symbol of the Type Descriptor
                if let Some((vtable_sym_idx, _)) = obj
                    .symbols
                    .at_section_address(
                        obj.sections.at_address(this_vtable_addr)?.0,
                        this_vtable_addr,
                    )
                    .next()
                {
                    rtti.type_info_vtable =
                        Some(RTTIExeInfo { symbol_index: vtable_sym_idx, addr: this_vtable_addr });
                }
            }

            let should_be_zero = u32::from_be_bytes(sym_data[4..8].try_into()?);
            assert_eq!(
                should_be_zero, 0,
                "how on earth is this not zero: type descriptor spare, addr {:08X}",
                sym.address as u32
            );

            // str from_utf8 doesn't stop at the null terminator
            // why would it? that would make life too easy
            fn cstr_slice_to_str(bytes: &[u8]) -> Result<&str, std::str::Utf8Error> {
                let end = bytes.iter().position(|&b| b == 0).unwrap_or(bytes.len());
                std::str::from_utf8(&bytes[..end])
            }

            // purposefully skipping the . at the start
            // additionally, sym_data doesn't always contain the full string,
            // so we're just gonna pass in ALL the data from this section, starting with the first "?" in the name
            let type_str = cstr_slice_to_str(&section.data_range(sym.address as u32 + 9, 0)?)?;

            let this_type_desc = TypeDescriptor {
                exe_info: RTTIExeInfo { symbol_index: sym_idx, addr: sym.address as u32 },
                name: type_str.to_string(),
            };

            rtti.type_descriptor_lookup.insert(sym.address as u32, this_type_desc);

            let mut new_rtti_class = RTTIClass::default();
            new_rtti_class.name = type_str.to_string();
            new_rtti_class.type_descriptor_addr = sym.address as u32;
            rtti.discovered_classes.insert(new_rtti_class.type_descriptor_addr, new_rtti_class);

            // log::debug!("Discovered RTTI Type Descriptor entry: {}", type_str);
        }
    }
    Ok(())
}

fn find_bcds_and_cols(obj: &ObjInfo, rtti: &mut RTTIMetadata) -> Result<()> {
    let Some((section_index, section)) = obj.sections.by_name(".rdata")? else {
        unreachable!("RTTI being used, but there's no .rdata section???");
    };

    // the remaining RTTI structures live in .rdata
    for (sym_idx, sym) in obj.symbols.for_section(section_index) {
        // this obviously would not apply to strings
        // the objects we care about are all at least 16 bytes
        if sym.name.starts_with("str_") || sym.size < 4 {
            continue;
        }

        let sym_data = section.symbol_data(sym)?; // data_range
        let first_word = u32::from_be_bytes(sym_data[0..4].try_into()?);

        // if the first word is a Type Descriptor address, this is a Base Class Descriptor
        if let Some(rtti_class) = rtti.discovered_classes.get_mut(&first_word) {
            // log::debug!("RTTI Base Class Descriptor found at: {:#08X}", sym.address as u32);

            // base class descriptors are 28 bytes / 7 words
            let base_class_descriptor_data =
                section.data_range(sym.address as u32, sym.address as u32 + 28)?;

            // check the CHD addr and make sure it's the same
            // we'll actually parse CHDs/add them to our lookup outside of this loop
            let chd_addr = u32::from_be_bytes(base_class_descriptor_data[24..28].try_into()?);
            if rtti_class.class_hierarchy_descriptor_addr != 0 {
                assert_eq!(
                    rtti_class.class_hierarchy_descriptor_addr, chd_addr,
                    "Found different Class Hierarchy Descriptor locations! addr {:08X}",
                    sym.address as u32
                );
            } else {
                rtti_class.class_hierarchy_descriptor_addr = chd_addr;
            }
            let bcd = BaseClassDescriptor {
                exe_info: RTTIExeInfo { symbol_index: sym_idx, addr: sym.address as u32 },
                type_descriptor_addr: first_word,
                num_contained_bases: u32::from_be_bytes(
                    base_class_descriptor_data[4..8].try_into()?,
                ),
                m_disp: i32::from_be_bytes(base_class_descriptor_data[8..12].try_into()?),
                p_disp: i32::from_be_bytes(base_class_descriptor_data[12..16].try_into()?),
                v_disp: i32::from_be_bytes(base_class_descriptor_data[16..20].try_into()?),
                attributes: u32::from_be_bytes(base_class_descriptor_data[20..24].try_into()?),
                class_hierarchy_descriptor_addr: chd_addr,
            };
            rtti.base_class_descriptor_lookup.insert(sym.address as u32, bcd);
        } else if sym.size >= 16 {
            // if the 4th word is a Type Descriptor address, this is a Complete Object Locator
            let fourth_word = u32::from_be_bytes(sym_data[12..16].try_into()?);
            if let Some(rtti_class) = rtti.discovered_classes.get_mut(&fourth_word) {
                // log::debug!("RTTI Complete Object Locator found at: {:#08X}", sym.address as u32);

                // complete object locators are 20 bytes / 5 words
                let complete_object_locator_data =
                    section.data_range(sym.address as u32, sym.address as u32 + 20)?;

                // check the CHD addr and make sure it's the same
                // we'll actually parse CHDs/add them to our lookup outside of this loop
                let chd_addr = u32::from_be_bytes(complete_object_locator_data[16..20].try_into()?);
                if rtti_class.class_hierarchy_descriptor_addr != 0 {
                    assert_eq!(
                        rtti_class.class_hierarchy_descriptor_addr, chd_addr,
                        "Found different Class Hierarchy Descriptor locations! addr {:08X}",
                        sym.address as u32
                    );
                } else {
                    rtti_class.class_hierarchy_descriptor_addr = chd_addr;
                }
                // create a CompleteObjectLocator and add to the lookup
                let col = CompleteObjectLocator {
                    exe_info: RTTIExeInfo { symbol_index: sym_idx, addr: sym.address as u32 },
                    signature: u32::from_be_bytes(complete_object_locator_data[0..4].try_into()?),
                    offset: u32::from_be_bytes(complete_object_locator_data[4..8].try_into()?),
                    cd_offset: u32::from_be_bytes(complete_object_locator_data[8..12].try_into()?),
                    type_descriptor_addr: fourth_word,
                    class_hierarchy_descriptor_addr: chd_addr,
                    // we'll find this later
                    vftable_addr: 0,
                };
                assert_eq!(
                    col.signature, 0,
                    "how on earth is this not zero: COL signature, addr {:08X}",
                    sym.address as u32
                );
                rtti_class.unresolved_col_addrs.push(sym.address as u32);
                rtti.complete_object_locator_lookup.insert(sym.address as u32, col);
            }
        }
    }
    Ok(())
}

fn find_chds_and_bcas(obj: &ObjInfo, rtti: &mut RTTIMetadata) -> Result<()> {
    let Some((section_index, section)) = obj.sections.by_name(".rdata")? else {
        unreachable!("RTTI being used, but there's no .rdata section???");
    };

    for cur_rtti_class in &mut rtti.discovered_classes.values_mut() {
        if cur_rtti_class.class_hierarchy_descriptor_addr != 0 {
            // get the CHD, and in the process, the addr of the corresponding BCA
            let Some((chd_sym_idx, chd_sym)) = obj
                .symbols
                .at_section_address(section_index, cur_rtti_class.class_hierarchy_descriptor_addr)
                .next()
            else {
                unreachable!(
                    "CHD addr is not 0 ({:08X}), but despite that, we can't find its symbol in the exe!", cur_rtti_class.class_hierarchy_descriptor_addr
                );
            };
            assert_eq!(chd_sym.address as u32, cur_rtti_class.class_hierarchy_descriptor_addr);
            // complete object locators are 16 bytes / 4 words
            let class_hierarchy_descriptor_data = section.data_range(
                cur_rtti_class.class_hierarchy_descriptor_addr,
                cur_rtti_class.class_hierarchy_descriptor_addr + 16,
            )?;

            // create a CHD and add to our lookup
            let chd = ClassHierarchyDescriptor {
                exe_info: RTTIExeInfo {
                    symbol_index: chd_sym_idx,
                    addr: cur_rtti_class.class_hierarchy_descriptor_addr,
                },
                signature: u32::from_be_bytes(class_hierarchy_descriptor_data[0..4].try_into()?),
                attributes: u32::from_be_bytes(class_hierarchy_descriptor_data[4..8].try_into()?),
                num_base_classes: u32::from_be_bytes(
                    class_hierarchy_descriptor_data[8..12].try_into()?,
                ),
                base_class_array_addr: u32::from_be_bytes(
                    class_hierarchy_descriptor_data[12..16].try_into()?,
                ),
            };
            assert_eq!(
                chd.signature, 0,
                "how on earth is this not zero: CHD signature, addr {:08X}",
                chd_sym.address as u32
            );
            cur_rtti_class.base_class_array_addr = chd.base_class_array_addr;
            let num_bca_entries = chd.num_base_classes;
            rtti.class_hierarchy_descriptor_lookup
                .insert(cur_rtti_class.class_hierarchy_descriptor_addr, chd);

            // now, this obj should have a BCA set, so let's analyze that
            assert_ne!(cur_rtti_class.base_class_array_addr, 0);
            assert_ne!(num_bca_entries, 0);

            let Some((bca_sym_idx, bca_sym)) = obj
                .symbols
                .at_section_address(section_index, cur_rtti_class.base_class_array_addr)
                .next()
            else {
                unreachable!(
                    "BCA addr is not 0 ({:08X}), but despite that, we can't find its symbol in the exe!", cur_rtti_class.base_class_array_addr
                );
            };
            assert_eq!(bca_sym.address as u32, cur_rtti_class.base_class_array_addr);
            let mut bca_entries = Vec::with_capacity(num_bca_entries as usize);
            let base_class_array_data = section.data_range(
                cur_rtti_class.base_class_array_addr,
                cur_rtti_class.base_class_array_addr + (num_bca_entries * 4),
            )?;
            for chunk in base_class_array_data.chunks_exact(4) {
                bca_entries.push(u32::from_be_bytes(chunk.try_into()?));
            }
            assert_eq!(bca_entries.len(), num_bca_entries as usize);
            let bca = BaseClassArray {
                exe_info: RTTIExeInfo {
                    symbol_index: bca_sym_idx,
                    addr: cur_rtti_class.base_class_array_addr,
                },
                base_class_descriptors: bca_entries,
            };
            cur_rtti_class.base_class_array_len = bca.base_class_descriptors.len() as u32;
            rtti.base_class_array_lookup.insert(cur_rtti_class.base_class_array_addr, bca);
        }
        // no unreachable!() else case here, because some Type Descriptors legit just don't have other RTTI metadata
    }
    Ok(())
}

fn find_vftables(obj: &ObjInfo, rtti: &mut RTTIMetadata) -> Result<()> {
    let Some((section_index, section)) = obj.sections.by_name(".rdata")? else {
        unreachable!("RTTI being used, but there's no .rdata section???");
    };

    // run through the objects in .rdata again, and check if the previous addr over has a value in complete_object_locator_addresses.
    // if it does, then we're looking at the corresponding vftable
    let mut first = true;
    for (sym_idx, sym) in obj.symbols.for_section(section_index) {
        // skip the first item, since we're doing a little subtraction
        if first {
            first = false;
            continue;
        }
        // this obviously would not apply to strings
        if sym.name.starts_with("str_") {
            continue;
        }

        let maybe_complete_object_locator_address = u32::from_be_bytes(
            section.data_range((sym.address - 4) as u32, sym.address as u32)?.try_into()?,
        );

        // log::debug!("Found the vtable for {}! It's at {:08X}", rtti_name, sym.address);
        let vftable =
            VFTable { exe_info: RTTIExeInfo { symbol_index: sym_idx, addr: sym.address as u32 } };
        rtti.vftable_lookup.insert(sym.address as u32, vftable);

        // thanks to ownership we have to COL lookup twice
        if let Some(col) =
            rtti.complete_object_locator_lookup.get_mut(&maybe_complete_object_locator_address)
        {
            col.vftable_addr = sym.address as u32;
        }
    }
    Ok(())
}

fn find_rtti_structs(obj: &ObjInfo, rtti: &mut RTTIMetadata) -> Result<()> {
    // first, find the RTTI Type Descriptors
    find_rtti_type_descriptors(obj, rtti)?;
    // then a few more sweeps to get the rest
    // first sweep: get BCDs and COLs in our lookups
    // our RTTIClasses will have CHD addresses, but they won't be analyzed yet
    find_bcds_and_cols(obj, rtti)?;
    // second sweep: with our CHD addresses, create CHDs and BCAs for our lookups
    find_chds_and_bcas(obj, rtti)?;
    // last sweep: from the COLs we have, get the vftables
    find_vftables(obj, rtti)?;
    Ok(())
}

fn compute_superclasses(obj: &ObjInfo, rtti: &mut RTTIMetadata) -> Result<()> {
    let mut classes_to_process: Vec<&mut RTTIClass> = vec![];
    // for each RTTIClass, go through the BCA and determine the superclasses from their BCDs
    for rtti_class in &mut rtti.discovered_classes.values_mut() {
        if let Some(bca) = rtti.base_class_array_lookup.get(&rtti_class.base_class_array_addr) {
            // we skip over the first entry in the BCA, because it's just the BCD for this class
            rtti_class.base_class_descriptor_addr = bca.base_class_descriptors[0];
            let mut i = 1;
            while i < bca.base_class_descriptors.len() {
                // the BCD evaluated here is a base class of this RTTIClass...
                let cur_bcd_addr = bca.base_class_descriptors[i];
                let Some(cur_bcd) = rtti.base_class_descriptor_lookup.get(&cur_bcd_addr) else {
                    unreachable!(
                        "BCA at {:08X} has an invalid BCD {:08X}!",
                        bca.exe_info.addr, cur_bcd_addr
                    );
                };
                // ...so mark down the bcd addr, and then advance i by however many num bases the BCD says there are + 1
                rtti_class.direct_base_class_descriptor_addrs.push(cur_bcd_addr);
                i += cur_bcd.num_contained_bases as usize + 1;
            }
            // check for ANY sign of virtual inheritance in the tree
            for cur_bcd_addr in bca.base_class_descriptors.iter() {
                let Some(cur_bcd) = rtti.base_class_descriptor_lookup.get(&cur_bcd_addr) else {
                    unreachable!(
                        "BCA at {:08X} has an invalid BCD {:08X}!",
                        bca.exe_info.addr, cur_bcd_addr
                    );
                };
                if cur_bcd.attributes & 0x10 != 0 {
                    rtti_class.has_any_virtual_inheritance = true;
                    break;
                }
            }
        }
        classes_to_process.push(rtti_class);
    }
    // now, sort the RTTIClasses by smallest number of unresolved vftables
    // we do this because smaller vftable counts are likely to have less complex inheritance.
    // also, RTTIClasses with smaller vftable counts will very likely serve as the base classes
    // for more complexly inherited classes down the line as we progress through the Vec.
    // within each group of RTTIClasses that have the same number of COLs/vftables,
    // further sort them by smallest number of BCA entries.
    classes_to_process
        .sort_by_key(|class| (class.unresolved_col_addrs.len(), class.base_class_array_len));

    for rtti_class in classes_to_process {
        // if this RTTIClass doesn't even have a BCA nor any known COLs/vftables, don't bother with all this
        if rtti_class.base_class_array_addr == 0 || rtti_class.unresolved_col_addrs.len() == 0 {
            continue;
        }

        // 1 COL/vftable = zero virtual inheritance, easiest case to deal with rn
        if rtti_class.unresolved_col_addrs.len() == 1 {
            let Some(my_sole_col) =
                rtti.complete_object_locator_lookup.get(&rtti_class.unresolved_col_addrs[0])
            else {
                unreachable!(
                    "RTTI class {} has an invalid COL addr {:08X}!",
                    rtti_class.name, rtti_class.unresolved_col_addrs[0]
                );
            };
            rtti_class.base_classes.push(RTTIBaseClass {
                // for 1 COL/vftable, it belongs to us - so use our TD
                type_descriptor_addr: rtti_class.type_descriptor_addr,
                complete_object_locator_addr: my_sole_col.exe_info.addr,
                vftable_addr: my_sole_col.vftable_addr,
            });
            rtti_class.unresolved_col_addrs.clear();
        } else if rtti_class.unresolved_col_addrs.len() == 2 {
            // this branch and onward (when unresolved_col_addrs.len > 1)
            // will require walking up the inheritance tree to get the COL/vftable base class names
            // for each direct base in direct_base_class_descriptor_addrs, go from: BCD -> TD -> RTTIClass -> base_classes
            log::debug!(
                "RTTI Class with 2 COL/vftables {} has {} direct bases!",
                rtti_class.name,
                rtti_class.direct_base_class_descriptor_addrs.len()
            );

            // rtti.get_type_descriptor(0);
        }

        // else {
        //     log::debug!(
        //         "RTTI Class {} has {} direct bases and {} COL/vftable pairs to analyze!",
        //         rtti_class.name,
        //         rtti_class.direct_base_class_descriptor_addrs.len(),
        //         rtti_class.unresolved_col_addrs.len()
        //     );
        // }
    }

    Ok(())
}

fn apply_rtti_symbols(obj: &mut ObjInfo, rtti: &RTTIMetadata) -> Result<()> {
    // type_info's vftable
    if let Some(global_vtable_addr) = &rtti.type_info_vtable {
        let mut new_sym = obj.symbols[global_vtable_addr.symbol_index].clone();
        new_sym.name = "??_7type_info@@6B@".to_string();
        obj.symbols.replace(global_vtable_addr.symbol_index, new_sym)?;
    } else {
        unreachable!("So you have RTTI, but no global type info vtable addr?");
    }
    // RTTI Base Class Descriptors
    for (_, bcd) in &rtti.base_class_descriptor_lookup {
        if let Some(rtti_obj) = rtti.discovered_classes.get(&bcd.type_descriptor_addr) {
            let mut new_sym = obj.symbols[bcd.exe_info.symbol_index].clone();
            new_sym.name = format!(
                "??_R1{}{}{}{}{}8",
                encode_num(bcd.m_disp),
                encode_num(bcd.p_disp),
                encode_num(bcd.v_disp),
                encode_num(bcd.attributes as i32),
                rtti_obj.name[3..].to_string()
            );
            // TODO: if a symbol exists between this addr, and this addr + 28, wipe it, because that space will go to this symbol
            // new_sym.size = 28;
            // new_sym.size_known = true;
            obj.symbols.replace(bcd.exe_info.symbol_index, new_sym)?;
        } else {
            unreachable!(
                "Base Class Array at {:08X} has invalid Type Descriptor addr {:08X}",
                bcd.exe_info.addr, bcd.type_descriptor_addr
            );
        }
    }
    // iterate across our RTTIClasses to get TDs, CHDs, and BCAs
    for (td_addr, rtti_obj) in &rtti.discovered_classes {
        assert_eq!(td_addr, &rtti_obj.type_descriptor_addr);
        {
            let td = rtti.get_type_descriptor(rtti_obj.type_descriptor_addr);
            let mut new_sym = obj.symbols[td.exe_info.symbol_index].clone();
            // example:
            // Type Descriptor class name (. omitted): ?AVFilePath@@
            // Type Descriptor full symbol: ??_R0?AVFilePath@@@8
            new_sym.name = format!("??_R0{}@8", rtti_obj.name);
            // edit the descriptor's size to only be the vtable addr, zero word, and the string length
            new_sym.size = 8 + rtti_obj.name.len() as u64;
            // shoutout 4 byte alignment
            new_sym.size = new_sym.size.next_multiple_of(4);
            obj.symbols.replace(td.exe_info.symbol_index, new_sym)?;
        }
        if rtti_obj.class_hierarchy_descriptor_addr != 0 {
            if let Some(chd) = rtti
                .class_hierarchy_descriptor_lookup
                .get(&rtti_obj.class_hierarchy_descriptor_addr)
            {
                let mut new_sym = obj.symbols[chd.exe_info.symbol_index].clone();
                // example:
                // Type Descriptor class name (. omitted): ?AVFilePath@@
                // Class Hierarchy Descriptor full symbol: ??_R3FilePath@@8
                new_sym.name = format!("??_R3{}8", rtti_obj.name[3..].to_string());
                obj.symbols.replace(chd.exe_info.symbol_index, new_sym)?;
            } else {
                unreachable!(
                    "RTTI Class {} has invalid Class Hierarchy Descriptor addr {:08X}",
                    rtti_obj.name, rtti_obj.class_hierarchy_descriptor_addr
                );
            }
        }
        if rtti_obj.base_class_array_addr != 0 {
            if let Some(bca) = rtti.base_class_array_lookup.get(&rtti_obj.base_class_array_addr) {
                let mut new_sym = obj.symbols[bca.exe_info.symbol_index].clone();
                // example:
                // Type Descriptor class name (. omitted): ?AVFilePath@@
                // Class Hierarchy Descriptor full symbol: ??_R2FilePath@@8
                new_sym.name = format!("??_R2{}8", rtti_obj.name[3..].to_string());
                obj.symbols.replace(bca.exe_info.symbol_index, new_sym)?;
            } else {
                unreachable!(
                    "RTTI Class {} has invalid Base Class Array addr {:08X}",
                    rtti_obj.name, rtti_obj.base_class_array_addr
                );
            }
        }
        // label single COLs and vftables
        if rtti_obj.base_classes.len() == 1 {
            let Some(col) = rtti
                .complete_object_locator_lookup
                .get(&rtti_obj.base_classes[0].complete_object_locator_addr)
            else {
                unreachable!(
                    "RTTI Class {} has invalid Complete Object Locator addr {:08X}",
                    rtti_obj.name, rtti_obj.base_classes[0].complete_object_locator_addr
                );
            };
            let mut new_col_sym = obj.symbols[col.exe_info.symbol_index].clone();
            new_col_sym.name = format!("??_R4{}6B@", rtti_obj.name[3..].to_string());
            obj.symbols.replace(col.exe_info.symbol_index, new_col_sym)?;

            let Some(vftable) = rtti.vftable_lookup.get(&rtti_obj.base_classes[0].vftable_addr)
            else {
                unreachable!(
                    "RTTI Class {} has invalid vftable addr {:08X}",
                    rtti_obj.name, rtti_obj.base_classes[0].vftable_addr
                );
            };

            let mut new_vftable_sym = obj.symbols[vftable.exe_info.symbol_index].clone();
            new_vftable_sym.name = format!("??_7{}6B@", rtti_obj.name[3..].to_string());
            obj.symbols.replace(vftable.exe_info.symbol_index, new_vftable_sym)?;
        }
        // TODO: iterate through RTTIClass's base_classes field for multiple COLs/vftables
    }
    Ok(())
}

pub fn detect_rtti(obj: &mut ObjInfo) -> Result<()> {
    // TODO: re-enable this before merging to main
    // if !obj.rtti {
    //     log::debug!("This object does not use RTTI, skipping");
    //     return Ok(());
    // }

    // TODO:
    // this should also detect and label __RTtypeid and __RTDynamicCast
    // fix __RTtypeid and __RTDynamicCast so there's no dangling fn's
    // "Bad dynamic_cast!" would mean dynamic cast exists
    // "Attempted a typeid of NULL pointer!" would mean typeid exists

    let mut rtti_metadata = RTTIMetadata::default();

    // find all the RTTI structs you can
    find_rtti_structs(obj, &mut rtti_metadata)?;
    // analyze for superclass info
    compute_superclasses(obj, &mut rtti_metadata)?;
    // apply the symbols to the exe
    apply_rtti_symbols(obj, &rtti_metadata)?;

    Ok(())
}
