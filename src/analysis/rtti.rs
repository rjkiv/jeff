#![allow(dead_code)]
#![allow(unused)]
// laying down the foundations for labeling multiple/virtual inheritance RTTI objects
// haven't implemented it yet

use std::{
    cell::RefCell,
    collections::{btree_map::Entry, BTreeMap},
    rc::{Rc, Weak},
};

use anyhow::Result;
use memchr::memmem;

use crate::{
    analysis::{
        cfa::{AnalyzerState, FunctionInfo, SectionAddress},
        pass::AnalysisPass,
    },
    obj::{ObjInfo, ObjSectionKind, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind},
    util::msvc::encode_num,
};

// An RTTI Base Class Descriptor Object.
struct BaseClassDescriptor {
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
    pub signature: u32,                                       // always 0
    pub attributes: u32, // bit 0 set = multiple inheritance, bit 1 set = virtual inheritance
    pub num_base_classes: u32, // number of entries in the Base Class Array
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
    // Make this an Option because some RTTIClasses can legit just only have a Type Descriptor and nothing else
    pub class_hierarchy_descriptor: Option<ClassHierarchyDescriptor>,
    // But, it can have multiple base classes, each with their own COL and vftable
    pub complete_object_locators: Vec<CompleteObjectLocator>,
    // TODO: add a field for base classes/direct bases when walking the inheritance tree
}

// RTTI Metadata to be passed between functions.
struct RTTIMetadata {
    pub discovered_classes: Vec<Rc<RefCell<RTTIClass>>>,
}

// Parse our ObjInfo for all the RTTI structures we can find.
// Add labels for RTTI structures as we find them (eager approach), except for COLs, as we'll be analyzing them specially later.
fn find_all_rtti_structs(obj: &mut ObjInfo, rtti: &mut RTTIMetadata) -> Result<bool> {
    let (data_sec_idx, data_section) = obj.sections.by_name(".data")?.expect("No .data section!");

    // i hate that goddamn borrow checker
    let mut syms_to_add: Vec<ObjSymbol> = vec![];

    // we'll find this as we search for Type Descriptor entries
    let mut type_info_vtable: Option<u32> = None;

    // temporary maps to help us when populating/parsing RTTI objects
    let mut classes_by_type_descriptor_exe_addr: BTreeMap<u32, Rc<RefCell<RTTIClass>>> =
        BTreeMap::new();
    let mut classes_by_chd_exe_addr: BTreeMap<u32, Rc<RefCell<RTTIClass>>> = BTreeMap::new();

    // first, find the RTTI Type Descriptors in .data
    // since we aren't using ObjSymbols this time around, search for every instance of .?AU, .?AV, .PAU, .PAV
    let mut i = 8;
    let data = &data_section.data;
    while i + 4 < data.len() {
        let chunk = &data[i..i + 4];
        if chunk == b".?AU" || chunk == b".?AV" || chunk == b".PAU" || chunk == b".PAV" {
            let td_addr = data_section.address as u32 + (i - 8) as u32;
            let this_vtable_addr = u32::from_be_bytes(data[i - 8..i - 4].try_into()?);
            // if we've already set the global type info vtable addr
            if let Some(global_vtable_addr) = type_info_vtable {
                // check that the one we just read is the same, as there can only be one unique type info vtable addr
                assert_eq!(
                    global_vtable_addr, this_vtable_addr,
                    "type_info::vftable address mismatch!"
                );
            } else {
                // else, populate the global vtable addr with this one
                type_info_vtable = Some(this_vtable_addr);
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
            let type_str = cstr_slice_to_str(data_section.data_range(td_addr + 9, 0)?)?;

            let new_rtti_class = RTTIClass {
                name: type_str.to_string(),
                class_hierarchy_descriptor: None,
                complete_object_locators: Vec::new(),
            };

            let rtti_class_ptr = Rc::new(RefCell::new(new_rtti_class));
            rtti.discovered_classes.push(rtti_class_ptr.clone());
            classes_by_type_descriptor_exe_addr.insert(td_addr, rtti_class_ptr.clone());

            // log::debug!("Discovered RTTI Type Descriptor entry at {:08X}: {}", td_addr, type_str);
            syms_to_add.push(ObjSymbol {
                // example:
                // Type Descriptor class name (. omitted): ?AVFilePath@@
                // Type Descriptor full symbol: ??_R0?AVFilePath@@@8
                name: format!("??_R0{}@8", type_str),
                address: td_addr,
                section: Some(data_sec_idx),
                size: (type_str.len() + 8) as u32,
                size_known: true,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Object,
                ..Default::default()
            });

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
    let (rdata_sec_idx, rdata_section) =
        obj.sections.by_name(".rdata")?.expect("No .rdata section!");
    // for parsing vftables
    let (text_sec_idx, text_section) = obj.sections.by_name(".text")?.expect("No .text section!");

    // add the type_info vftable here
    let vftable_addr =
        type_info_vtable.expect("So there's RTTI, but no global type info vtable addr?");
    syms_to_add.push(ObjSymbol {
        name: "??_7type_info@@6B@".to_string(),
        address: vftable_addr,
        section: Some(rdata_sec_idx),
        size: 4,
        size_known: true,
        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
        kind: ObjSymbolKind::Object,
        ..Default::default()
    });

    // now, search for COLs after the TDs (BCDs can't be found reliably, they can conflict with catchables)
    let mut i = 0;
    let data = &rdata_section.data;
    while i + 4 < data.len() {
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
                            Rc::ptr_eq(entry.get(), rtti_class),
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
                            // add this to our known function addrs
                            // check to see if the addr is already part of a known function - if it's not, add it to known_functions
                            if let Entry::Vacant(e) = obj
                                .known_functions
                                .entry(SectionAddress::new(text_sec_idx, cur_vftable_entry))
                            {
                                e.insert(None);
                            }
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
                        owner: Rc::downgrade(rtti_class),
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

    // it is entirely possible that a new CHD can be discovered while populating other CHDs,
    // due to an RTTI class not having any COLs, and thus, no CHD discovered at that point.
    // so, this will serve as an indicator for which CHDs have been fully parsed
    let mut parsed_chds_by_exe_addr: BTreeMap<u32, Rc<RefCell<RTTIClass>>> = BTreeMap::new();

    while classes_by_chd_exe_addr.len() != parsed_chds_by_exe_addr.len() {
        let mut missed_chds: BTreeMap<u32, Rc<RefCell<RTTIClass>>> = BTreeMap::new();
        for (chd_exe_addr, the_rtti_class) in &classes_by_chd_exe_addr {
            // don't re-parse
            if parsed_chds_by_exe_addr.contains_key(chd_exe_addr) {
                continue;
            }

            // log::debug!("CHD found at {:08X} for {}!", chd_exe_addr, the_rtti_class.borrow().name);
            // navigate to the bytes in .rdata that make up this CHD, and parse it
            let chd_data_idx = chd_exe_addr - rdata_section.address as u32;
            let chd_data = &rdata_section.data[chd_data_idx as usize..chd_data_idx as usize + 16];
            let mut chd = ClassHierarchyDescriptor {
                signature: u32::from_be_bytes(chd_data[0..4].try_into()?),
                attributes: u32::from_be_bytes(chd_data[4..8].try_into()?),
                num_base_classes: u32::from_be_bytes(chd_data[8..12].try_into()?),
                base_class_descriptors: vec![],
            };
            assert_eq!(
                chd.signature, 0,
                "how on earth is this not zero: CHD signature, addr {:08X}",
                chd_exe_addr
            );

            let base_class_array_addr = u32::from_be_bytes(chd_data[12..16].try_into()?);

            // label the CHD here
            syms_to_add.push(ObjSymbol {
                // example:
                // Type Descriptor class name (. omitted): ?AVFilePath@@
                // Class Hierarchy Descriptor full symbol: ??_R3FilePath@@8
                name: format!("??_R3{}8", &the_rtti_class.borrow().name[3..]),
                address: *chd_exe_addr,
                section: Some(rdata_sec_idx),
                size: 16,
                size_known: true,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Object,
                ..Default::default()
            });

            // if the recorded BCA addr is not within .rdata, something has gone horribly wrong
            assert!(
                rdata_section.address as u32 <= base_class_array_addr
                    && base_class_array_addr
                        < rdata_section.address as u32 + rdata_section.size as u32,
                "Bad BCA addr {:08X}!",
                base_class_array_addr
            );

            // label the BCA here
            syms_to_add.push(ObjSymbol {
                // example:
                // Type Descriptor class name (. omitted): ?AVFilePath@@
                // Class Hierarchy Descriptor full symbol: ??_R2FilePath@@8
                name: format!("??_R2{}8", &the_rtti_class.borrow().name[3..]),
                address: base_class_array_addr,
                section: Some(rdata_sec_idx),
                // there's a null word after the last BCD entry, hence the +1
                size: ((chd.num_base_classes + 1) * 4),
                size_known: true,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Object,
                ..Default::default()
            });

            // parse the BCA and BCDs as well, since the CHD will own the BCA
            let bca_data_idx = base_class_array_addr - rdata_section.address as u32;
            let bca_data = &rdata_section.data[bca_data_idx as usize
                ..bca_data_idx as usize + (chd.num_base_classes * 4) as usize];

            for chunk in bca_data.chunks_exact(4) {
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
                        let chd_addr = u32::from_be_bytes(bcd_data[24..28].try_into()?);
                        if !classes_by_chd_exe_addr.contains_key(&chd_addr) {
                            // log::warn!(
                            //     "Missing CHD addr {:08X} for {}!",
                            //     chd_addr,
                            //     class_for_bcd.borrow().name
                            // );
                            // if we don't have it marked as missed, add it in
                            missed_chds.entry(chd_addr).or_insert_with(|| class_for_bcd.clone());
                        }

                        let bcd_ptr = Rc::new(BaseClassDescriptor {
                            num_contained_bases: u32::from_be_bytes(bcd_data[4..8].try_into()?),
                            m_disp: i32::from_be_bytes(bcd_data[8..12].try_into()?),
                            p_disp: i32::from_be_bytes(bcd_data[12..16].try_into()?),
                            v_disp: i32::from_be_bytes(bcd_data[16..20].try_into()?),
                            attributes: u32::from_be_bytes(bcd_data[20..24].try_into()?),
                            owner: Rc::downgrade(class_for_bcd),
                        });
                        // label the BCD here
                        syms_to_add.push(ObjSymbol {
                            name: format!(
                                "??_R1{}{}{}{}{}8",
                                encode_num(bcd_ptr.m_disp),
                                encode_num(bcd_ptr.p_disp),
                                encode_num(bcd_ptr.v_disp),
                                encode_num(bcd_ptr.attributes as i32),
                                &class_for_bcd.borrow().name[3..]
                            ),
                            address: cur_bcd_addr,
                            section: Some(rdata_sec_idx),
                            size: 28,
                            size_known: true,
                            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                            kind: ObjSymbolKind::Object,
                            ..Default::default()
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
            parsed_chds_by_exe_addr.insert(*chd_exe_addr, the_rtti_class.clone());
        }
        let old_len = classes_by_chd_exe_addr.len();
        classes_by_chd_exe_addr.append(&mut missed_chds);
        assert!(classes_by_chd_exe_addr.len() >= old_len, "Unbreakable loop while parsing CHDs!");
    }

    for sym in syms_to_add {
        obj.add_symbol(sym, false)?;
    }

    Ok(true)
}

fn compute_superclass_info(obj: &mut ObjInfo, rtti: &mut RTTIMetadata) -> Result<()> {
    let (rdata_sec_idx, _) = obj.sections.by_name(".rdata")?.expect("No .rdata section!");

    // the borrow checker still mega sucks
    let mut syms_to_add: Vec<ObjSymbol> = vec![];

    // the original impl had us walking through each RTTI object and getting direct bases
    // but, since we have direct access to the BCAs now, this isn't necessary, we can just...do that on the fly

    // so, let's sort the RTTIClasses by smallest amount of COLs, and then smallest number of BCA entries (0 if no BCA)
    rtti.discovered_classes.sort_by_key(|rc| {
        let c = rc.borrow();
        let bca_len = match &c.class_hierarchy_descriptor {
            Some(chd) => chd.num_base_classes,
            None => 0,
        };
        (c.complete_object_locators.len(), bca_len)
    });

    for rc in &rtti.discovered_classes {
        // get the underlying RTTIClass from the Rc
        // make this mutable when you start modifying potential base class members
        let c = rc.borrow_mut();
        if let Some(chd) = &c.class_hierarchy_descriptor {
            // do the superclass analysis
            // 0 COLs/vftables - still record info/mark anything down here? not sure yet
            if c.complete_object_locators.is_empty() {
                // log::debug!("0 COL RTTI Object {}", c.name);
            }
            // 1 COL/vftable = zero virtual inheritance, easiest case to deal with rn
            else if c.complete_object_locators.len() == 1 {
                // log::debug!("1 COL RTTI Object {}", c.name);
                let the_sole_col = &c.complete_object_locators[0];
                // make a label for the COL, and for the vftable
                syms_to_add.push(ObjSymbol {
                    name: format!("??_R4{}6B@", &c.name[3..]),
                    address: the_sole_col.addr,
                    section: Some(rdata_sec_idx),
                    size: 20,
                    size_known: true,
                    flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                    kind: ObjSymbolKind::Object,
                    ..Default::default()
                });
                syms_to_add.push(ObjSymbol {
                    name: format!("??_7{}6B@", &c.name[3..]),
                    address: the_sole_col.vftable_addr,
                    section: Some(rdata_sec_idx),
                    size: (the_sole_col.num_vftable_entries * 4),
                    size_known: true,
                    flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                    kind: ObjSymbolKind::Object,
                    ..Default::default()
                });
            }
            // nightmare territory - 2+ COLs
            else {
                // TODO: walk the inheritance tree and deduce superclass info for the final labels
                // for now, mark down the vftables/COLs and their sizes
                for col in &c.complete_object_locators {
                    syms_to_add.push(ObjSymbol {
                        name: format!("COL_for_{}_{:08X}", &c.name[3..], col.addr),
                        address: col.addr,
                        section: Some(rdata_sec_idx),
                        size: 20,
                        size_known: true,
                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                        kind: ObjSymbolKind::Object,
                        ..Default::default()
                    });
                    syms_to_add.push(ObjSymbol {
                        name: format!("VFTABLE_for_{}_{:08X}", &c.name[3..], col.addr),
                        address: col.vftable_addr,
                        section: Some(rdata_sec_idx),
                        size: (col.num_vftable_entries * 4),
                        size_known: true,
                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                        kind: ObjSymbolKind::Object,
                        ..Default::default()
                    });
                }
            }
        }
    }

    for sym in syms_to_add {
        obj.add_symbol(sym, false)?;
    }

    Ok(())
}

// Scan for RTTI objects, before any CFA is performed.
// Allows us to mark them as known_symbols ahead of time, we have control over what the symbol sizes/scopes should be,
// and by stepping through vftables, we have more known function start addresses we can provide to our object.
pub fn process_rtti(obj: &mut ObjInfo) -> Result<()> {
    let mut rtti_metadata = RTTIMetadata { discovered_classes: vec![] };
    // when adding symbol, use replace = false

    // find all the RTTI structs you can
    if !find_all_rtti_structs(obj, &mut rtti_metadata)? {
        log::info!("No RTTI found!");
        return Ok(());
    }

    log::info!("Found {} classes from RTTI!\n", rtti_metadata.discovered_classes.len());

    // if we've reached this point, we have a full set of RTTI objects and their relationships
    // and everything except for COLs and vftables have been labeled
    // so, compute superclass information to get the remaining context needed to label those
    compute_superclass_info(obj, &mut rtti_metadata)?;

    Ok(())
}
