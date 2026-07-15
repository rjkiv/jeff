use std::{
    cell::RefCell,
    collections::BTreeMap,
    rc::{Rc, Weak},
};

use anyhow::Result;

use crate::{
    analysis::{cfa::AnalyzerState, pass::AnalysisPass},
    obj::ObjInfo,
};

// An RTTI Base Class Descriptor Object.
struct BaseClassDescriptor {
    pub addr: u32,                        // the address of this in the exe
    pub type_descriptor: Weak<RTTIClass>, // type descriptor of the class
    pub num_contained_bases: u32, // number of nested classes following in the Base Class Array
    pub m_disp: i32,              // member displacement
    pub p_disp: i32,              // vbtable displacement
    pub v_disp: i32,              // displacement inside vbtable
    pub attributes: u32, // flags: 0x40 bit means has Class Hierarchy Descriptor, 0x10 bit means base class is virtually inherited
    pub class_hierarchy_descriptor: Weak<ClassHierarchyDescriptor>,
}

// An RTTI Class Hierarchy Descriptor object. Also contains Base Class Array information.
struct ClassHierarchyDescriptor {
    pub addr: u32,                  // the address of this in the exe
    pub signature: u32,             // always 0
    pub attributes: u32, // bit 0 set = multiple inheritance, bit 1 set = virtual inheritance
    pub num_base_classes: u32, // number of entries in the Base Class Array
    pub base_class_array_addr: u32, // BCA addr in the exe
    pub base_class_descriptors: Vec<Rc<BaseClassDescriptor>>, // the addresses of the BCDs that make up this Base Class Array
}

// An RTTI Complete Object Locator.
struct CompleteObjectLocator {
    pub addr: u32,      // the address of this in the exe
    pub signature: u32, // always 0
    pub offset: u32,    // offset of this vtable in complete class (from top)
    pub cd_offset: u32, // offset of constructor displacement
    pub type_descriptor: Weak<RTTIClass>,
    pub class_hierarchy_descriptor: Weak<ClassHierarchyDescriptor>,
    // The address of the vftable associated with this COL
    pub vftable_addr: u32,
}

// A class that uses RTTI
struct RTTIClass {
    // A class using RTTI can only ever have one type descriptor, class hierarchy descriptor (and by extension, Base Class Array)
    pub name: String, // this class's name, inferred from the type descriptor
    pub type_descriptor_addr: u32, // type descriptor addr in the exe
    // Make this an Option because some RTTIClasses can legit just only have a Type Descriptor and nothing else
    pub class_hierarchy_descriptor: Option<Rc<ClassHierarchyDescriptor>>,
    // But, it can have multiple base classes, each with their own COL and vftable
    pub complete_object_locators: Vec<Rc<CompleteObjectLocator>>,
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
    let mut type_descriptor_lookup: BTreeMap<u32, Rc<RefCell<RTTIClass>>> = BTreeMap::new();

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
            type_descriptor_lookup.insert(td_addr, rtti_class_ptr.clone());

            log::debug!("Discovered RTTI Type Descriptor entry at {:08X}: {}", td_addr, type_str);
            i += type_str.len().next_multiple_of(4);
        } else {
            i += 4;
        }
    }

    // quick check - if there were 0 Type Descriptors found, RTTI isn't supported, bail early
    if type_descriptor_lookup.is_empty() {
        return Ok(false);
    }

    // find: COLs (BCDs can't be found reliably)
    // if we spot a COL, should we go recursively down the graph, creating structs?
    // so from the COL, step to the CHD, then the BCA, then each of its BCDs?

    Ok(true)
}

// fn find_rtti_structs(obj: &ObjInfo, rtti: &mut RTTIMetadata) -> Result<bool> {
//     // first, find the RTTI Type Descriptors
//     find_rtti_type_descriptors(obj, rtti)?;
//     // quick check - if there were 0 Type Descriptors found, RTTI isn't supported, bail early
//     if rtti.type_descriptor_lookup.is_empty() {
//         return Ok(false);
//     }
//     // then a few more sweeps to get the rest
//     // first sweep: get BCDs and COLs in our lookups
//     // our RTTIClasses will have CHD addresses, but they won't be analyzed yet
//     find_bcds_and_cols(obj, rtti)?;
//     // // second sweep: with our CHD addresses, create CHDs and BCAs for our lookups
//     // find_chds_and_bcas(obj, rtti)?;
//     // // last sweep: from the COLs we have, get the vftables
//     // find_vftables(obj, rtti)?;
//     Ok(true)
// }

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
