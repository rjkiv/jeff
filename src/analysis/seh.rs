use std::collections::btree_map::Entry;

use anyhow::{bail, Result};

use crate::{
    analysis::{cfa::SectionAddress, read_u32},
    obj::{ObjInfo, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind},
};

struct CScopeTableEntry {
    pub begin: u32,
    pub end: u32,
    pub handler: u32,
    pub target: u32,
}

pub fn process_pdata(obj: &mut ObjInfo) -> Result<()> {
    // add known function boundaries from pdata
    // FIXME: Some of these are SEH-related labels, not function entrypoints
    let (_pdata_sec_idx, pdata_section) = obj
        .sections
        .by_name(".pdata")?
        .expect(".pdata section not found. Is that even possible for an xex?");

    // if this is Some, we can reliably parse exceptions
    // if for whatever reason this is None (like you're analyzing a raw exe), we cannot,
    // because we cannot confidently tell which is the C handler versus the CXX handler at this point
    let c_handler_addr: Option<SectionAddress> =
        obj.symbols.by_name("__C_specific_handler")?.map(|(_, sym)| {
            SectionAddress::new(
                sym.section.expect("C handler should have a section specified!"),
                sym.address as u32,
            )
        });
    let mut cxx_handler_addr: Option<SectionAddress> = None;

    let mut syms_to_add: Vec<ObjSymbol> = vec![];
    let mut num_discovered_funcs = 0;
    let data = &pdata_section.data;
    for chunk in data.chunks_exact(8) {
        let start_addr = u32::from_be_bytes(chunk[0..4].try_into()?);
        // if we encounter 0's, that's the end of usable pdata entries
        if start_addr == 0 {
            break;
        }

        // some metadata for this function, including function size
        let word = u32::from_be_bytes(chunk[4..8].try_into()?);
        // let num_prologue_insts = word & 0xFF; // The number of instructions in the function's prolog.
        let num_insts_in_func = (word >> 8) & 0x3FFFFF; // The number of instructions in the function.
        let func_type = word >> 30; // The function type.

        let func_start_addr =
            SectionAddress::new(obj.sections.at_address(start_addr)?.0, start_addr);
        obj.known_functions.insert(func_start_addr, Some(num_insts_in_func * 4));
        obj.pdata_funcs.push(func_start_addr);
        num_discovered_funcs += 1;

        // if func_type == 3, there's an 8 byte struct (with 2 words) just before the function start that contains exception data
        if func_type == 3 {
            // println!("Exception handler at {:08X}, record at {:08X}", start_addr - 8, start_addr - 4);
            syms_to_add.push(ObjSymbol {
                name: format!("except_data_{:08X}", start_addr),
                address: (start_addr - 8) as u64,
                section: Some(func_start_addr.section),
                size: 8,
                size_known: true,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Object,
                ..Default::default()
            });

            let mut cur_func_except_data: (SectionAddress, SectionAddress) =
                (func_start_addr, func_start_addr); // func_start_addr should be overwritten anyway

            // word 1: the address of the function's exception handler
            if let Some(except_func) =
                read_u32(obj.sections.at_address(start_addr - 8)?.1, start_addr - 8)
            {
                let except_func_section =
                    SectionAddress::new(obj.sections.at_address(except_func)?.0, except_func);
                // check to see if the addr is already part of a known function - if it's not, add it to known_functions
                if let Entry::Vacant(e) = obj.known_functions.entry(except_func_section) {
                    e.insert(None);
                    num_discovered_funcs += 1;
                }
                cur_func_except_data.0 = except_func_section;
            } else {
                bail!("Invalid exception handler address listed at {}!", start_addr - 8)
            }
            // word 2: the address of the function's exception handler data record
            if let Some(except_record) =
                read_u32(obj.sections.at_address(start_addr - 4)?.1, start_addr - 4)
            {
                // one specific exception handler can have no record (a nullptr in the exception data)
                if except_record != 0 {
                    let except_record_section = SectionAddress::new(
                        obj.sections.at_address(except_record)?.0,
                        except_record,
                    );
                    syms_to_add.push(ObjSymbol {
                        name: format!("except_record_{:08X}", start_addr),
                        address: except_record as u64,
                        section: Some(except_record_section.section),
                        size: 4,
                        size_known: false, // we don't know exactly how big this particular exception record may be
                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                        kind: ObjSymbolKind::Object,
                        ..Default::default()
                    });
                    cur_func_except_data.1 = except_record_section;
                } else {
                    // There is only one known except_data pair that won't have an exception record pointer,
                    // and that's for the func _CallCatchBlock, whose exception handler is _SkipUnwoundFrames
                    syms_to_add.push(ObjSymbol {
                        name: String::from("_CallCatchBlock"),
                        address: func_start_addr.address as u64,
                        section: Some(func_start_addr.section),
                        // change this to size: 0x24 once you're sure it's the same size throughout all xexes
                        size_known: false,
                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                        kind: ObjSymbolKind::Function,
                        ..Default::default()
                    });
                    syms_to_add.push(ObjSymbol {
                        name: String::from("_SkipUnwoundFrames"),
                        address: cur_func_except_data.0.address as u64,
                        section: Some(cur_func_except_data.0.section),
                        // change this to size: 0x28 once you're sure it's the same size throughout all xexes
                        size_known: false,
                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                        kind: ObjSymbolKind::Function,
                        ..Default::default()
                    });

                    continue;
                }
            } else {
                bail!("Invalid exception record address listed at {}!", start_addr - 4)
            }

            // parse the exception data if we can reliably do so (see reasoning above)
            if let Some(c_handler) = c_handler_addr {
                if c_handler == cur_func_except_data.0 {
                    // C handler
                    obj.funcs_with_c_handlers.insert(func_start_addr, cur_func_except_data.1);
                } else {
                    // CXX handler - set it or check it
                    match cxx_handler_addr {
                        Some(addr) => {
                            assert_eq!(addr, cur_func_except_data.0, "Unequal CXX handler addrs!")
                        }
                        None => cxx_handler_addr = Some(cur_func_except_data.0),
                    };
                    obj.funcs_with_cxx_handlers.insert(func_start_addr, cur_func_except_data.1);
                }
            }
        }
    }
    log::info!("Found {} known funcs from pdata!", num_discovered_funcs);
    if c_handler_addr.is_some() {
        log::info!("Found {} funcs with C exception handlers!", obj.funcs_with_c_handlers.len());
        log::info!(
            "Found {} funcs with CXX exception handlers!",
            obj.funcs_with_cxx_handlers.len()
        );
    }

    // add Cxx handler symbol here
    if let Some(cxx_handler) = cxx_handler_addr {
        obj.add_symbol(
            ObjSymbol {
                name: String::from("__CxxFrameHandler"),
                address: cxx_handler.address as u64,
                section: Some(cxx_handler.section),
                size_known: false,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Function,
                ..Default::default()
            },
            false,
        )?;
    }

    // then for each except_data/except_record symbol (might remove later idk)
    for sym in syms_to_add {
        obj.add_symbol(sym, false)?;
    }

    process_exception_data(obj)?;

    Ok(())
}

fn process_exception_data(obj: &mut ObjInfo) -> Result<()> {
    // exception records will be in .rdata
    let (rdata_sec_idx, rdata_section) =
        obj.sections.by_name(".rdata")?.expect("No .rdata section!");

    for (c_func, c_except_record) in &obj.funcs_with_c_handlers {
        println!("Func {:?} has C scope table at {:?}", c_func, c_except_record);
        // parse the scope table to get the size
        // save the size? because we'd want to rename the symbol later to match the name of the func?
    }

    // for (cxx_func, cxx_except_record) in &obj.funcs_with_cxx_handlers {
    //     println!("Func {:?} has __ehfuncinfo at {:?}", cxx_func, cxx_except_record);
    // }

    Ok(())
}
