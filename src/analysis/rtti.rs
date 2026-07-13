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

#[derive(Clone)]
enum InheritanceKind {
    // if physical, keep track of the m_disp
    Physical(i32),
    // i dunno what to keep track of for virtual yet
    Virtual,
}

// Info for a base class of an RTTIClass.
// Used for both applying final symbol labels, and for analysis of future derived RTTIClasses.
#[derive(Clone)]
struct RTTIBaseClass {
    // the specific Type Descriptor for this superclass
    // contains the base class's name, used for labeling and analysis
    pub type_descriptor_addr: u32,
    // The COL for this base class, used in the final label
    pub complete_object_locator_addr: u32,
    // The vftable for this base class, used in the final label
    pub vftable_addr: u32,
    // Whether this base class is virtually inherited, used for analysis
    // use InheritanceKind here?
    pub inheritance_kind: InheritanceKind,
}

impl Default for RTTIBaseClass {
    fn default() -> Self {
        Self {
            type_descriptor_addr: 0,
            complete_object_locator_addr: 0,
            vftable_addr: 0,
            inheritance_kind: InheritanceKind::Physical(-1),
        }
    }
}

struct RTTIBaseClassCandidate {
    // contains the name to assign to the COL
    pub type_descriptor_addr: u32,
    pub inheritance_kind: InheritanceKind,
}

// A class that uses RTTI
#[derive(Clone, Default)]
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

    // only tracks type descriptors for now, subject to change
    fn walk_inheritance_tree(
        &self,
        // the type descriptor of the main class whose inheritance tree we're trying to walk in the first place
        main_td: u32,
        direct_bases: &Vec<u32>,
        has_primary: bool,
    ) -> Result<Vec<RTTIBaseClassCandidate>> {
        // a pool of relevant information to be extracted from our direct bases' base classes
        let mut candidate_pool: Vec<RTTIBaseClassCandidate> = Vec::new();

        // for each direct base DB, note DB's base classes
        for (i, bcd_addr) in direct_bases.iter().enumerate() {
            let bcd =
                self.base_class_descriptor_lookup.get(bcd_addr).unwrap_or_else(|| unreachable!());
            let cur_bcd_is_physical = bcd.p_disp == -1;
            let cur_base_class = self
                .discovered_classes
                .get(&bcd.type_descriptor_addr)
                .unwrap_or_else(|| unreachable!());

            // log::debug!(
            //     "\tDirect base ({}): {}",
            //     if cur_bcd_is_physical { "physical" } else { "virtual" },
            //     cur_base_class.name
            // );

            // from each base class that DB has, record the base class's name (td), physical vs virtual
            for base in &cur_base_class.base_classes {
                let td = base.type_descriptor_addr;
                // let iter_base_class =
                //     self.discovered_classes.get(&td).unwrap_or_else(|| unreachable!());
                let mut is_physical = false;
                // if base's type descriptor == cur base class's type descriptor,
                // whether this is physical or virtual will depend on cur_bcd_is_physical
                if td == cur_base_class.type_descriptor_addr {
                    is_physical = cur_bcd_is_physical;
                } else {
                    is_physical = !matches!(base.inheritance_kind, InheritanceKind::Virtual);
                }

                // log::debug!(
                //     "\t\tcontains base class ({}): {}",
                //     if is_physical { "physical" } else { "virtual" },
                //     iter_base_class.name
                // );

                // if there's already a candidate in our pool with the same type descriptor
                if let Some(existing_candidate) =
                    candidate_pool.iter_mut().find(|c| c.type_descriptor_addr == td)
                {
                    // but, it happens to be virtual, and this one is physical
                    if matches!(existing_candidate.inheritance_kind, InheritanceKind::Virtual)
                        && is_physical
                    {
                        // swap it out
                        existing_candidate.inheritance_kind = InheritanceKind::Physical(0);
                    }
                }
                // else, just add it as normal
                else {
                    candidate_pool.push(RTTIBaseClassCandidate {
                        type_descriptor_addr: td,
                        inheritance_kind: if is_physical {
                            InheritanceKind::Physical(0)
                        } else {
                            InheritanceKind::Virtual
                        },
                    });
                }

                // let mut inheritance_kind: InheritanceKind;
                // if !is_physical || base.is_virtual {
                //     inheritance_kind = InheritanceKind::Virtual;
                // } else {
                //     // examine the base's COL (if it's not 0) and look at the offset
                //     // add that to bcd's m_disp
                //     let col = self
                //         .complete_object_locator_lookup
                //         .get(&base.complete_object_locator_addr)
                //         .unwrap_or_else(|| unreachable!());
                //     inheritance_kind = InheritanceKind::Physical(col.offset as i32 + bcd.m_disp);
                // }
                //
                // candidate_pool
                //     .push(RTTIBaseClassCandidate { type_descriptor_addr: td, inheritance_kind })
            }
        }
        if has_primary {
            // From the first direct physical base, the first physical base that has a COL for it, is the primary base
            if let Some(index) = candidate_pool.iter().position(|candidate| {
                matches!(candidate.inheritance_kind, InheritanceKind::Physical(_))
            }) {
                let primary = candidate_pool.remove(index);
                // push it up front, we're gonna make the first entry in our candidate pool the primary
                candidate_pool.insert(0, primary);
            }
            // Or, if there are no direct physical bases, add yourself to the recorded base classes, and make yourself the primary
            else {
                candidate_pool.insert(0, RTTIBaseClassCandidate {
                    type_descriptor_addr: main_td,
                    inheritance_kind: InheritanceKind::Physical(0),
                });
            }
        }

        // add another pass here? to remove any physical candidates that don't fit for any physical COL (0/X/0)

        for (i, candidate) in candidate_pool.iter().enumerate() {
            let cand_class = self
                .discovered_classes
                .get(&candidate.type_descriptor_addr)
                .unwrap_or_else(|| unreachable!());
            if i == 0 && has_primary {
                log::debug!("\tPrimary candidate: {}", cand_class.name);
            } else {
                let phys_str = match candidate.inheritance_kind {
                    InheritanceKind::Physical(_) => "physical",
                    InheritanceKind::Virtual => "virtual",
                };
                log::debug!("\tCandidate ({}): {}", phys_str, cand_class.name);
            }
        }

        Ok(candidate_pool)
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

fn compute_direct_bases(rtti: &mut RTTIMetadata) -> Result<Vec<u32>> {
    let mut classes_to_process_by_type_descriptor = Vec::new();
    // for each RTTIClass, go through the BCA and determine the superclasses from their BCDs
    for rtti_class in &mut rtti.discovered_classes.values_mut() {
        classes_to_process_by_type_descriptor.push(rtti_class.type_descriptor_addr);
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
    }
    // now, sort the RTTIClasses by smallest number of unresolved vftables
    // we do this because smaller vftable counts are likely to have less complex inheritance.
    // also, RTTIClasses with smaller vftable counts will very likely serve as the base classes
    // for more complexly inherited classes down the line as we progress through the Vec.
    // within each group of RTTIClasses that have the same number of COLs/vftables,
    // further sort them by smallest number of BCA entries.
    classes_to_process_by_type_descriptor.sort_by_key(|td| {
        let c = rtti.discovered_classes.get(td).unwrap_or_else(|| unreachable!());
        (c.unresolved_col_addrs.len(), c.base_class_array_len)
    });
    Ok(classes_to_process_by_type_descriptor)
}

fn compute_superclasses(obj: &ObjInfo, rtti: &mut RTTIMetadata) -> Result<()> {
    let classes_to_process_by_type_descriptor = compute_direct_bases(rtti)?;
    for td in &classes_to_process_by_type_descriptor {
        let mut new_rtti_class =
            rtti.discovered_classes.get(td).unwrap_or_else(|| unreachable!()).clone();
        // if this RTTIClass doesn't even have a BCA, don't bother with all this
        if new_rtti_class.base_class_array_addr == 0 {
            continue;
        }

        // 0 COLs/vftables - still record base class info anyway
        if new_rtti_class.unresolved_col_addrs.len() == 0 {
            for direct_bcd_addr in &new_rtti_class.direct_base_class_descriptor_addrs {
                let bcd = rtti
                    .base_class_descriptor_lookup
                    .get(direct_bcd_addr)
                    .unwrap_or_else(|| unreachable!());
                new_rtti_class.base_classes.push(RTTIBaseClass {
                    type_descriptor_addr: bcd.type_descriptor_addr,
                    complete_object_locator_addr: 0,
                    vftable_addr: 0,
                    inheritance_kind: InheritanceKind::Physical(0),
                });
            }
            *rtti.discovered_classes.get_mut(td).unwrap_or_else(|| unreachable!()) = new_rtti_class;
        }
        // 1 COL/vftable = zero virtual inheritance, easiest case to deal with rn
        else if new_rtti_class.unresolved_col_addrs.len() == 1 {
            let Some(my_sole_col) =
                rtti.complete_object_locator_lookup.get(&new_rtti_class.unresolved_col_addrs[0])
            else {
                unreachable!(
                    "RTTI class {} has an invalid COL addr {:08X}!",
                    new_rtti_class.name, new_rtti_class.unresolved_col_addrs[0]
                );
            };
            new_rtti_class.base_classes.push(RTTIBaseClass {
                // for 1 COL/vftable, it belongs to us - so use our TD
                type_descriptor_addr: new_rtti_class.type_descriptor_addr,
                complete_object_locator_addr: my_sole_col.exe_info.addr,
                vftable_addr: my_sole_col.vftable_addr,
                inheritance_kind: InheritanceKind::Physical(0),
            });
            new_rtti_class.unresolved_col_addrs.clear();
            *rtti.discovered_classes.get_mut(td).unwrap_or_else(|| unreachable!()) = new_rtti_class;
        }
        // arbitrary len limit, just lowering the scope
        else if new_rtti_class.unresolved_col_addrs.len() <= 3 {
            // this branch and onward (when unresolved_col_addrs.len > 1)
            // will require walking up the inheritance tree to get the COL/vftable base class names
            log::debug!(
                "RTTI Class with {} COL/vftables {} has {} direct bases!",
                new_rtti_class.unresolved_col_addrs.len(),
                new_rtti_class.name,
                new_rtti_class.direct_base_class_descriptor_addrs.len()
            );

            // If there's a COL with 0,0,0, a primary COL exists
            // if false, we don't assign a primary candidate in walk inheritance tree
            let has_primary_col = new_rtti_class.unresolved_col_addrs.iter().any(|col_addr| {
                let col = rtti
                    .complete_object_locator_lookup
                    .get(col_addr)
                    .unwrap_or_else(|| unreachable!());
                col.signature == 0 && col.offset == 0 && col.cd_offset == 0
            });

            let base_class_candidate_pool = rtti.walk_inheritance_tree(
                new_rtti_class.type_descriptor_addr,
                &new_rtti_class.direct_base_class_descriptor_addrs,
                has_primary_col,
            )?;

            if base_class_candidate_pool.len() != new_rtti_class.unresolved_col_addrs.len() {
                log::warn!("RTTIClass {} inheritance tree was not correctly processed, skipping further analysis...", new_rtti_class.name);
                continue;
            }

            for col_addr in new_rtti_class.unresolved_col_addrs.iter() {
                let col = rtti
                    .complete_object_locator_lookup
                    .get(col_addr)
                    .unwrap_or_else(|| unreachable!());
                log::debug!("\tCOL: {}, {}, {}", col.signature, col.offset, col.cd_offset);
            }

            for candidate in base_class_candidate_pool.iter() {
                new_rtti_class.base_classes.push(RTTIBaseClass {
                    type_descriptor_addr: candidate.type_descriptor_addr,
                    complete_object_locator_addr: 0,
                    vftable_addr: 0,
                    inheritance_kind: candidate.inheritance_kind.clone(),
                })
            }
            *rtti.discovered_classes.get_mut(td).unwrap_or_else(|| unreachable!()) = new_rtti_class;

            // match candidates in our pool to COL/vftables
            // the one whose offset is 0, that's either this class or a direct base
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
    if !obj.rtti {
        log::debug!("This object does not use RTTI, skipping");
        return Ok(());
    }

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
