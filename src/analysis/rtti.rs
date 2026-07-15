use std::{
    cell::RefCell,
    collections::{btree_map::Entry, BTreeMap},
    rc::{Rc, Weak},
};

use anyhow::Result;
use memchr::memmem;

use crate::{
    analysis::{cfa::AnalyzerState, pass::AnalysisPass},
    obj::ObjInfo,
};

// An RTTI Base Class Descriptor Object.
struct BaseClassDescriptor {
    pub addr: u32,                // the address of this in the exe
    pub num_contained_bases: u32, // number of nested classes following in the Base Class Array
    pub m_disp: i32,              // member displacement
    pub p_disp: i32,              // vbtable displacement
    pub v_disp: i32,              // displacement inside vbtable
    // flags: 0x40 bit means has Class Hierarchy Descriptor, 0x10 bit means base class is virtually inherited
    pub attributes: u32,
    // NOTE: The RTTIClass associated with a BCD's TypeDescriptor and ClassHierarchyDescriptor entries will always be the same on Xbox 360,
    // so we can condense those into one single owner field.
    pub owner: Weak<RefCell<RTTIClass>>,
}

// An RTTI Class Hierarchy Descriptor object. Also contains Base Class Array information.
struct ClassHierarchyDescriptor {
    pub addr: u32,                  // the address of this in the exe
    pub signature: u32,             // always 0
    pub attributes: u32, // bit 0 set = multiple inheritance, bit 1 set = virtual inheritance
    pub num_base_classes: u32, // number of entries in the Base Class Array
    pub base_class_array_addr: u32, // BCA addr in the exe
    pub base_class_descriptors: Vec<Rc<BaseClassDescriptor>>, // the BCDs that make up the Base Class Array
}

// An RTTI Complete Object Locator.
struct CompleteObjectLocator {
    pub addr: u32,      // the address of this in the exe
    pub signature: u32, // always 0
    pub offset: u32,    // offset of this vtable in complete class (from top)
    pub cd_offset: u32, // offset of constructor displacement
    // NOTE: The RTTIClass associated with a COL's TypeDescriptor and ClassHierarchyDescriptor entries will always be the same on Xbox 360,
    // so we can condense those into one single owner field.
    pub owner: Weak<RefCell<RTTIClass>>,
    // The address of the vftable associated with this COL
    pub vftable_addr: u32,
    // how many entries the vftable has
    pub num_vftable_entries: u32,
}

// A class that uses RTTI
struct RTTIClass {
    // A class using RTTI can only ever have one type descriptor, class hierarchy descriptor (and by extension, Base Class Array)
    pub name: String, // this class's name, inferred from the type descriptor
    pub type_descriptor_addr: u32, // type descriptor addr in the exe
    // Make this an Option because some RTTIClasses can legit just only have a Type Descriptor and nothing else
    pub class_hierarchy_descriptor: Option<ClassHierarchyDescriptor>,
    // But, it can have multiple base classes, each with their own COL and vftable
    pub complete_object_locators: Vec<CompleteObjectLocator>,
    // TODO: add a field for base classes/direct bases when walking the inheritance tree
}

// RTTI Metadata to be passed between functions.
struct RTTIMetadata {
    // the addr of type_info's vftable; this will be populated when searching for Type Descriptor entries
    pub type_info_vtable: Option<u32>,
    pub discovered_classes: Vec<Rc<RefCell<RTTIClass>>>,
}

// what if we had RTTI scanning here instead? before any CFA?
// you can find Type Descriptors from: .?AU, .?AV, .PAU, .PAV
// doing it here gives you more control over what size the symbols are
// doing it in here would also mean no SymbolIndex, since we're not replacing symbols, we're adding them

fn find_all_rtti_structs(obj: &ObjInfo, rtti: &mut RTTIMetadata) -> Result<bool> {
    let Some((_, data_section)) = obj.sections.by_name(".data")? else {
        unreachable!("No .data section???");
    };

    // temporary maps to help us when populating/parsing RTTI objects
    let mut classes_by_type_descriptor_exe_addr: BTreeMap<u32, Rc<RefCell<RTTIClass>>> =
        BTreeMap::new();
    let mut classes_by_chd_exe_addr: BTreeMap<u32, Rc<RefCell<RTTIClass>>> = BTreeMap::new();

    // first, find the RTTI Type Descriptors in .data
    // since we aren't using ObjSymbols this time around, search for every instance of .?AU, .?AV, .PAU, .PAV
    let mut i = 8;
    let data = &data_section.data;
    while i < data.len() {
        let chunk = &data[i..i + 4];
        if chunk == b".?AU" || chunk == b".?AV" || chunk == b".PAU" || chunk == b".PAV" {
            let td_addr = data_section.address as u32 + (i - 8) as u32;
            let this_vtable_addr = u32::from_be_bytes(data[i - 8..i - 4].try_into()?);
            // if we've already set the global type info vtable addr
            if let Some(global_vtable_addr) = rtti.type_info_vtable {
                // check that the one we just read is the same, as there can only be one unique type info vtable addr
                assert_eq!(
                    global_vtable_addr, this_vtable_addr,
                    "type_info::vftable address mismatch!"
                );
            } else {
                // else, populate the global vtable addr with this one
                rtti.type_info_vtable = Some(this_vtable_addr);
            }
            let should_be_zero = u32::from_be_bytes(data[i - 4..i].try_into()?);
            assert_eq!(
                should_be_zero, 0,
                "how on earth is this not zero: type descriptor spare, addr {:08X}",
                td_addr
            );
            // str from_utf8 doesn't stop at the null terminator
            // why would it? that would make life too easy
            fn cstr_slice_to_str(bytes: &[u8]) -> Result<&str, std::str::Utf8Error> {
                let end = bytes.iter().position(|&b| b == 0).unwrap_or(bytes.len());
                std::str::from_utf8(&bytes[..end])
            }
            // purposefully skipping the . at the start
            // additionally, since we don't know how long the full string is,
            // we're just gonna pass in ALL the data from this section, starting with the first "?" in the name
            let type_str = cstr_slice_to_str(&data_section.data_range(td_addr + 9, 0)?)?;

            let new_rtti_class = RTTIClass {
                name: type_str.to_string(),
                type_descriptor_addr: td_addr,
                class_hierarchy_descriptor: None,
                complete_object_locators: Vec::new(),
            };

            let rtti_class_ptr = Rc::new(RefCell::new(new_rtti_class));
            rtti.discovered_classes.push(rtti_class_ptr.clone());
            classes_by_type_descriptor_exe_addr.insert(td_addr, rtti_class_ptr.clone());

            // log::debug!("Discovered RTTI Type Descriptor entry at {:08X}: {}", td_addr, type_str);
            i += type_str.len().next_multiple_of(4);
        } else {
            i += 4;
        }
    }

    // quick check - if there were 0 Type Descriptors found, RTTI isn't supported, bail early
    if classes_by_type_descriptor_exe_addr.is_empty() {
        return Ok(false);
    }

    // the remaining RTTI structures live in .rdata
    let Some((_, rdata_section)) = obj.sections.by_name(".rdata")? else {
        unreachable!("No .rdata section???");
    };

    // for calculating vftable sizes
    let Some((_, text_section)) = obj.sections.by_name(".text")? else {
        unreachable!("No .text section???");
    };

    // now, search for COLs after the TDs (BCDs can't be found reliably, they can conflict with catchables)
    let mut i = 0;
    let data = &rdata_section.data;
    while i < data.len() {
        let cur_word = u32::from_be_bytes(data[i..i + 4].try_into()?);
        // if cur word is a key that exists in type_descriptor_lookup
        if let Some(rtti_class) = classes_by_type_descriptor_exe_addr.get(&cur_word) {
            // check the next word over
            let next_word = u32::from_be_bytes(data[i + 4..i + 8].try_into()?);
            // if it's a valid address in rdata, it means we're looking at a Complete Object Locator.
            if rdata_section.address as u32 <= next_word
                && next_word < rdata_section.address as u32 + rdata_section.size as u32
            {
                let col_start_addr = rdata_section.address as u32 + (i - 12) as u32;
                // log::debug!(
                //     "Discovered RTTI Complete Object Locator entry at {:08X}!",
                //     col_start_addr
                // );

                // because we're using Rc's, it means we gotta get all our fields initialized before we apply the Rc<> part.
                // so, when parsing a COL, take note of the ClassHierarchyDescriptor addr (add it in another lookup map)
                // and then get the vftable addr right then and there, using the COL's addr

                // next_word == the COL's CHD address
                match classes_by_chd_exe_addr.entry(next_word) {
                    Entry::Vacant(entry) => {
                        entry.insert(rtti_class.clone());
                    }
                    Entry::Occupied(entry) => {
                        assert!(
                            Rc::ptr_eq(entry.get(), &rtti_class),
                            "CHD {:08X} already associated with a different RTTIClass {}!",
                            next_word,
                            rtti_class.borrow().name,
                        );
                    }
                }

                // search for col_start_addr in .rdata
                if let Some(col_start_idx) = memmem::find(data, &col_start_addr.to_be_bytes()) {
                    // the vftable is the next addr over from the COL, hence the +4
                    let vftable_idx = col_start_idx + 4;
                    let vftable_addr = rdata_section.address as u32 + vftable_idx as u32;

                    // calculate vftable entry count here
                    // as long as an entry is a valid address in .text, keep going
                    let mut num_vftable_entries: u32 = 0;
                    loop {
                        let cur_vftable_idx_offset =
                            vftable_idx + (num_vftable_entries as usize * 4);
                        let cur_vftable_entry = u32::from_be_bytes(
                            data[cur_vftable_idx_offset..cur_vftable_idx_offset + 4].try_into()?,
                        );
                        // check that cur_vftable_entry is within .text bounds
                        if text_section.address as u32 <= cur_vftable_entry
                            && cur_vftable_entry
                                < text_section.address as u32 + text_section.size as u32
                        {
                            num_vftable_entries += 1;
                        } else {
                            break;
                        }
                    }

                    // log::debug!(
                    //     "VFTable for COL at {:08X} found! It's at {:08X}",
                    //     col_start_addr,
                    //     vftable_addr
                    // );

                    let col = CompleteObjectLocator {
                        addr: col_start_addr,
                        signature: u32::from_be_bytes(data[i - 12..i - 8].try_into()?),
                        offset: u32::from_be_bytes(data[i - 8..i - 4].try_into()?),
                        cd_offset: u32::from_be_bytes(data[i - 4..i].try_into()?),
                        owner: Rc::downgrade(&rtti_class),
                        vftable_addr,
                        num_vftable_entries,
                    };
                    assert_eq!(
                        col.signature, 0,
                        "how on earth is this not zero: COL signature, addr {:08X}",
                        col_start_addr
                    );
                    rtti_class.borrow_mut().complete_object_locators.push(col);
                    i += 8;
                } else {
                    panic!("How can a COL not have a vftable???")
                }
            } else {
                i += 4;
            }
        } else {
            i += 4;
        }
    }

    // at this point, our RTTIClasses are only missing their CHD fields.
    // but, we saved their addresses in classes_by_chd_exe_addr above.
    // so parse them, and also parse BCAs/BCDs along the way.

    // this lookup map here is because one BCD can be referenced by multiple BCAs,
    // and we're not tryna make two BCDs with identical values;
    // rather, just have the multiple BCAs point to the same BCD.
    let mut bcds_by_exe_addr: BTreeMap<u32, Rc<BaseClassDescriptor>> = BTreeMap::new();

    for (chd_exe_addr, the_rtti_class) in classes_by_chd_exe_addr {
        // log::debug!("CHD found at {:08X} for {}!", chd_exe_addr, the_rtti_class.borrow().name);
        // navigate to the bytes in .rdata that make up this CHD, and parse it
        let chd_data_idx = chd_exe_addr - rdata_section.address as u32;
        let chd_data = &rdata_section.data[chd_data_idx as usize..chd_data_idx as usize + 16];
        let mut chd = ClassHierarchyDescriptor {
            addr: chd_exe_addr,
            signature: u32::from_be_bytes(chd_data[0..4].try_into()?),
            attributes: u32::from_be_bytes(chd_data[4..8].try_into()?),
            num_base_classes: u32::from_be_bytes(chd_data[8..12].try_into()?),
            base_class_array_addr: u32::from_be_bytes(chd_data[12..16].try_into()?),
            base_class_descriptors: vec![],
        };
        assert_eq!(
            chd.signature, 0,
            "how on earth is this not zero: CHD signature, addr {:08X}",
            chd_exe_addr
        );
        // if the recorded BCA addr is not within .rdata, something has gone horribly wrong
        assert!(
            rdata_section.address as u32 <= chd.base_class_array_addr
                && chd.base_class_array_addr
                    < rdata_section.address as u32 + rdata_section.size as u32,
            "Bad BCA addr {:08X}!",
            chd.base_class_array_addr
        );
        // parse the BCA and BCDs as well, since the CHD will own the BCA
        let bca_data_idx = chd.base_class_array_addr - rdata_section.address as u32;
        let bca_data = &rdata_section.data
            [bca_data_idx as usize..bca_data_idx as usize + (chd.num_base_classes * 4) as usize];

        for (_, chunk) in bca_data.chunks_exact(4).enumerate() {
            let cur_bcd_addr = u32::from_be_bytes(chunk[0..4].try_into()?);
            let cur_bcd = match bcds_by_exe_addr.entry(cur_bcd_addr) {
                Entry::Vacant(entry) => {
                    // it's vacant, parse and create a new BCD instance
                    let bcd_data_idx = cur_bcd_addr - rdata_section.address as u32;
                    let bcd_data =
                        &rdata_section.data[bcd_data_idx as usize..bcd_data_idx as usize + 28];
                    let td_addr = u32::from_be_bytes(bcd_data[0..4].try_into()?);
                    let Some(class_for_bcd) = classes_by_type_descriptor_exe_addr.get(&td_addr)
                    else {
                        panic!("Bad Type Descriptor addr {:08X}!", td_addr);
                    };
                    let bcd_ptr = Rc::new(BaseClassDescriptor {
                        addr: cur_bcd_addr,
                        num_contained_bases: u32::from_be_bytes(bcd_data[4..8].try_into()?),
                        m_disp: i32::from_be_bytes(bcd_data[8..12].try_into()?),
                        p_disp: i32::from_be_bytes(bcd_data[12..16].try_into()?),
                        v_disp: i32::from_be_bytes(bcd_data[16..20].try_into()?),
                        attributes: u32::from_be_bytes(bcd_data[20..24].try_into()?),
                        owner: Rc::downgrade(&class_for_bcd),
                    });
                    entry.insert(bcd_ptr.clone());
                    bcd_ptr
                }
                Entry::Occupied(entry) => {
                    // it's occupied, just use the one we've got
                    entry.get().clone()
                }
            };
            chd.base_class_descriptors.push(cur_bcd.clone());
        }

        the_rtti_class.borrow_mut().class_hierarchy_descriptor = Some(chd);
    }

    Ok(true)
}

pub struct FindRTTIObjectsXbox {}

impl AnalysisPass for FindRTTIObjectsXbox {
    fn execute(state: &mut AnalyzerState, obj: &ObjInfo) -> Result<()> {
        let mut rtti_metadata = RTTIMetadata { type_info_vtable: None, discovered_classes: vec![] };

        log::info!("Hello from FindRTTIObjectsXbox");

        // try to find Type Descriptors
        // if you found none, that would mean there's no RTTI, so quit early
        // else, do everything you've already implemented in rtti.rs

        // find all the RTTI structs you can
        if !find_all_rtti_structs(obj, &mut rtti_metadata)? {
            return Ok(());
        }

        // we'll mainly be editing state.known_symbols
        Ok(())
    }
}
