use std::collections::btree_map::Entry;

use anyhow::{bail, Result};

use crate::{
    analysis::{
        cfa::SectionAddress,
        read_u32,
        seh::CHandlerType::{Except, Finally},
    },
    obj::{ObjInfo, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind},
    util::read::read_word,
};
// info on the C scope table: https://blog.talosintelligence.com/exceptional-behavior-windows-81-x64-seh/

#[derive(Debug, Clone)]
pub enum CHandlerType {
    Except { addr: SectionAddress },
    Finally { addr: SectionAddress },
}

#[derive(Debug, Clone)]
pub struct CScopeTableInfo {
    // The address of the scope table itself
    pub addr: SectionAddress,
    // The addresses of each scope table entry's handler types
    pub handler_addrs: Vec<CHandlerType>,
    // ScopeTableEntry contents:
    // DWORD 1 - Begin; // where the try starts
    // DWORD 2 - End; // where the try ends
    // DWORD 3 - Handler; // the __finally handler if Target is 0, else, the __except handler
    // DWORD 4 - Target; // the code inside the __except block

    // size of scope table: 16 * num_scope_entries + 4
    // 16 = size of scope table entry
    // 4 = the word that contains the number of scope entries
}

pub fn process_pdata(obj: &mut ObjInfo) -> Result<()> {
    // add known function boundaries from pdata
    // FIXME: Some of these are SEH-related labels, not function entrypoints
    let (_pdata_sec_idx, pdata_section) = obj
        .sections
        .by_name(".pdata")?
        .expect(".pdata section not found. Is that even possible for an xex?");

    // We need this to parse C/C++ exception info structs
    let (rdata_sec_idx, rdata_section) =
        obj.sections.by_name(".rdata")?.expect("No .rdata section!");

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
            let cur_func_except_handler: SectionAddress;
            let cur_func_except_record: SectionAddress;

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
                cur_func_except_handler = except_func_section;
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
                    cur_func_except_record = except_record_section;
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
                        address: cur_func_except_handler.address as u64,
                        section: Some(cur_func_except_handler.section),
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
                if c_handler == cur_func_except_handler {
                    // C handler

                    let mut handlers: Vec<CHandlerType> = vec![];

                    // parse the C Scope table that's located at cur_func_except_record
                    assert_eq!(
                        rdata_sec_idx, cur_func_except_record.section,
                        "Except record not in .rdata?"
                    );
                    let offset_into_sec =
                        cur_func_except_record.address - rdata_section.address as u32;
                    let num_scope_entries =
                        read_word(&rdata_section.data, offset_into_sec as usize);
                    let entry_offsets_begin = offset_into_sec + 4;
                    for i in 0..num_scope_entries {
                        let handler = read_word(
                            &rdata_section.data,
                            (entry_offsets_begin + (i * 16) + 8) as usize,
                        );
                        let target = read_word(
                            &rdata_section.data,
                            (entry_offsets_begin + (i * 16) + 12) as usize,
                        );
                        if target == 0 {
                            let addr =
                                SectionAddress::new(obj.sections.at_address(handler)?.0, handler);
                            // check to see if the addr is already part of a known function - if it's not, add it to known_functions
                            if let Entry::Vacant(e) = obj.known_functions.entry(addr) {
                                e.insert(None);
                                num_discovered_funcs += 1;
                            }
                            log::debug!(
                                "Func {:08X}: Handler at {:08X} is a __finally!",
                                func_start_addr,
                                addr
                            );
                            handlers.push(Finally { addr });
                        } else {
                            let addr =
                                SectionAddress::new(obj.sections.at_address(handler)?.0, handler);
                            // check to see if the addr is already part of a known function - if it's not, add it to known_functions
                            if let Entry::Vacant(e) = obj.known_functions.entry(addr) {
                                e.insert(None);
                                num_discovered_funcs += 1;
                            }
                            log::debug!(
                                "Func {:08X}: Handler at {:08X} is an __except!",
                                func_start_addr,
                                addr
                            );
                            handlers.push(Except { addr });
                        }
                    }
                    assert_eq!(handlers.len(), num_scope_entries as usize);
                    obj.funcs_with_c_handlers.insert(func_start_addr, CScopeTableInfo {
                        addr: cur_func_except_record,
                        handler_addrs: handlers,
                    });
                } else {
                    // CXX handler - set it or check it
                    match cxx_handler_addr {
                        Some(addr) => {
                            assert_eq!(addr, cur_func_except_handler, "Unequal CXX handler addrs!")
                        }
                        None => cxx_handler_addr = Some(cur_func_except_handler),
                    };
                    obj.funcs_with_cxx_handlers.insert(func_start_addr, cur_func_except_record);
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

    // process_exception_data(obj)?;

    Ok(())
}

// fn process_exception_data(obj: &mut ObjInfo) -> Result<()> {
//     // exception records will be in .rdata
//     let (rdata_sec_idx, rdata_section) =
//         obj.sections.by_name(".rdata")?.expect("No .rdata section!");
//
//     let mut syms_to_add: Vec<ObjSymbol> = vec![];
//
//     // info on the C scope table: https://blog.talosintelligence.com/exceptional-behavior-windows-81-x64-seh/
//     for (c_func, c_except_record) in &obj.funcs_with_c_handlers {
//         // println!("Func {:?} has C scope table at {:?}", c_func, c_except_record);
//         assert_eq!(rdata_sec_idx, c_except_record.section, "Except record not in .rdata?");
//         // parse the scope table to get the size
//         let offset_into_sec = c_except_record.address - rdata_section.address as u32;
//         let num_scope_entries = read_word(&rdata_section.data, offset_into_sec as usize);
//         // size of scope table: 16 * num_scope_entries + 4
//         // 16 = size of scope table entry
//         // 4 = the word that contains the number of scope entries
//         // TODO: add relocs for each of the entries?
//
//         // ScopeTable contents:
//         // DWORD 1 - Begin; // where the try starts
//         // DWORD 2 - End; // where the try ends
//         // DWORD 3 - Handler; // the __finally handler if Target is 0, else, the __except handler
//         // DWORD 4 - Target; // the code inside the __except block
//         let entry_offsets_begin = offset_into_sec + 4;
//         for i in 0..num_scope_entries {
//             let handler =
//                 read_word(&rdata_section.data, (entry_offsets_begin + (i * 4) + 8) as usize);
//             let target =
//                 read_word(&rdata_section.data, (entry_offsets_begin + (i * 4) + 12) as usize);
//             if target == 0 {
//                 println!("Handler at {:08X} is a __finally!", handler);
//             } else {
//                 println!("Handler at {:08X} is an __except!", handler);
//             }
//         }
//
//         // if Target == 0, Handler == __finally
//         // if Target != 0, Handler == __except
//         // get the right .text section for the finally/except label
//
//         syms_to_add.push(ObjSymbol {
//             name: format!("__scopetable${}", c_except_record.address),
//             address: c_except_record.address as u64,
//             section: Some(c_except_record.section),
//             size: (num_scope_entries * 16 + 4) as u64,
//             size_known: true,
//             flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
//             kind: ObjSymbolKind::Object,
//             ..Default::default()
//         });
//     }
//
//     // TODO: check for:
//     // "__RTDynamicCast"
//     // "_CxxThrowException"
//     // __unwind$
//     // __catch$
//     // __annotation$
//     // __catch$%s$%d
//     // "__ehfuncinfo$%s"
//     // "__estypeinfo$%s$%d"
//     // "__catchsym$%s$%d"
//     // "__estypeinfo$%s"
//     // "__tryblocktable$%s"
//     // "__unwindtable$%s"
//     // "__unwindfunclet$%s$%d"
//     // "__unwind$%s$%d"
//     // "__tryend$%s$%d"
//
//     // if the handler is CxxFrameHandler, exception data is __ehfuncinfo
//
//     // for (cxx_func, cxx_except_record) in &obj.funcs_with_cxx_handlers {
//     //     println!("Func {:?} has __ehfuncinfo at {:?}", cxx_func, cxx_except_record);
//     // }
//
//     for sym in syms_to_add {
//         obj.add_symbol(sym, false)?;
//     }
//
//     Ok(())
// }
