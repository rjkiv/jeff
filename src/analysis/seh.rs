use std::collections::{btree_map::Entry, BTreeSet};

use anyhow::{bail, Result};

use crate::{
    analysis::{cfa::SectionAddress, read_u32},
    obj::{ObjInfo, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind},
};

// info on the C scope table: https://blog.talosintelligence.com/exceptional-behavior-windows-81-x64-seh/
#[derive(Debug, Clone)]
pub struct CScopeTableInfo {
    // The address of the scope table itself
    pub addr: SectionAddress,
    // The exception handlers from this scope table
    pub handlers: Vec<SectionAddress>,
    // ScopeTableEntry contents:
    // DWORD 1 - Begin; // where the try starts
    // DWORD 2 - End; // where the try ends
    // DWORD 3 - Handler; // the __finally handler if Target is 0, else, the __except handler
    // DWORD 4 - Target; // the code inside the __except block
}

// info on CXX exception info structs: https://www.openrce.org/articles/full_view/21
#[derive(Debug, Clone)]
pub struct CXXEhFuncInfo {
    // The address of the __ehfuncinfo$ itself
    pub addr: SectionAddress,
    // unwind map addr and its entries - __unwindtable$
    pub unwind_map_addr: Option<SectionAddress>,
    pub unwinds: Vec<Option<SectionAddress>>,
    // try map addr, and number of entries - __tryblocktable$, which contains __catchsym$
    pub num_tries: u32,
    pub try_map_addr: Option<SectionAddress>,
    pub catches: Vec<Option<SectionAddress>>,
    // iptostate map addr, and number of entries - parsing this map likely not needed for the purposes of labeling functions/eh objects
    pub num_ip_to_states: u32,
    pub ip_to_state_map_addr: Option<SectionAddress>,
}

pub fn process_seh(obj: &mut ObjInfo) -> Result<()> {
    // add known function boundaries from pdata
    let (_, pdata_section) = obj
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

    let mut catch_addrs: BTreeSet<SectionAddress> = BTreeSet::new();
    let mut c_except_addrs: BTreeSet<SectionAddress> = BTreeSet::new();
    // addrs that are confirmed to be unwinds/catches/excepts/finallys
    let mut known_exception_addrs: BTreeSet<SectionAddress> = BTreeSet::new();
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

        // unwinds/catches/etc will always come AFTER their main function,
        // so at this point, we should've parsed the main function for its exception structures.
        if known_exception_addrs.contains(&func_start_addr) {
            if catch_addrs.contains(&func_start_addr) {
                let end_addr = func_start_addr + (num_insts_in_func * 4);
                obj.catches.insert(func_start_addr, end_addr);
            } else if c_except_addrs.contains(&func_start_addr) {
                let end_addr = func_start_addr + (num_insts_in_func * 4);
                obj.c_except_addrs.insert(func_start_addr, end_addr);
            }
            continue;
        }

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
                // C handler
                if c_handler == cur_func_except_handler {
                    // parse the C Scope table that's located at cur_func_except_record
                    assert_eq!(
                        rdata_sec_idx, cur_func_except_record.section,
                        "Except record not in .rdata?"
                    );
                    let num_scope_entries = read_u32(rdata_section, cur_func_except_record.address)
                        .expect("No exception record here!");
                    let entry_addrs_begin = cur_func_except_record.address + 4;
                    let mut handlers: Vec<SectionAddress> = Vec::new();
                    for i in 0..num_scope_entries {
                        let handler = read_u32(rdata_section, entry_addrs_begin + (i * 16) + 8)
                            .expect("No handler here!");
                        // let target = read_u32(rdata_section, entry_addrs_begin + (i * 16) + 12)
                        //     .expect("No target here!");
                        let addr =
                            SectionAddress::new(obj.sections.at_address(handler)?.0, handler);
                        // add a label for this except structure - could remove this tbh, verify against real objs
                        syms_to_add.push(ObjSymbol {
                            name: format!(
                                "$LN{:08X}",
                                // if target == 0 { "__finally" } else { "__except" },
                                addr.address
                            ),
                            address: addr.address as u64,
                            section: Some(addr.section),
                            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                            ..Default::default()
                        });
                        c_except_addrs.insert(addr);
                        known_exception_addrs.insert(addr);
                        handlers.push(addr);
                        // log::debug!(
                        //     "Func {:08X}: Handler at {:08X} is {}!",
                        //     func_start_addr,
                        //     addr,
                        //     if target == 0 { "a __finally" } else { "an __except" }
                        // );
                    }
                    assert_eq!(handlers.len(), num_scope_entries as usize);
                    obj.funcs_with_c_handlers.insert(func_start_addr, CScopeTableInfo {
                        addr: cur_func_except_record,
                        handlers,
                    });

                    // this is a known C function, but exceptions make it hard to deduce the ending
                    obj.known_functions.insert(func_start_addr, None);
                    obj.pdata_funcs.insert(func_start_addr);
                    num_discovered_funcs += 1;
                }
                // C++
                else {
                    // CXX handler - set it or check it
                    match cxx_handler_addr {
                        Some(addr) => {
                            assert_eq!(addr, cur_func_except_handler, "Unequal CXX handler addrs!")
                        }
                        None => cxx_handler_addr = Some(cur_func_except_handler),
                    };

                    // parse the C++ __ehfuncinfo that's located at cur_func_except_record
                    assert_eq!(
                        rdata_sec_idx, cur_func_except_record.section,
                        "Except record not in .rdata?"
                    );
                    // the first word needs to be __ehfuncinfo magic, otherwise this isn't a valid exception record
                    assert_eq!(
                        read_u32(rdata_section, cur_func_except_record.address)
                            .expect("No exception record here!"),
                        0x19930522,
                        "Bad __ehfuncinfo magic!"
                    );
                    let num_unwinds = read_u32(rdata_section, cur_func_except_record.address + 4)
                        .expect("No unwind count here");
                    let mut unwinds: Vec<Option<SectionAddress>> = Vec::new();
                    let unwind_map_addr = {
                        let unwind_map_addr =
                            read_u32(rdata_section, cur_func_except_record.address + 8)
                                .expect("No unwind map here!");
                        if unwind_map_addr != 0 {
                            // at this point, we know an unwind map exists - parse its entries
                            assert!(num_unwinds > 0);
                            for i in 0..num_unwinds {
                                let maybe_unwind_addr =
                                    read_u32(rdata_section, unwind_map_addr + (i * 8) + 4)
                                        .expect("No unwind entry here!");
                                if maybe_unwind_addr != 0 {
                                    let addr = SectionAddress::new(
                                        obj.sections.at_address(maybe_unwind_addr)?.0,
                                        maybe_unwind_addr,
                                    );
                                    syms_to_add.push(ObjSymbol {
                                        name: format!("__unwind${:08X}", addr.address),
                                        address: addr.address as u64,
                                        section: Some(addr.section),
                                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                                        ..Default::default()
                                    });
                                    known_exception_addrs.insert(addr);
                                    unwinds.push(Some(addr));
                                    obj.unwinds.insert(addr);
                                } else {
                                    unwinds.push(None);
                                }
                            }
                            Some(SectionAddress::new(rdata_sec_idx, unwind_map_addr))
                        } else {
                            None
                        }
                    };
                    assert_eq!(unwinds.len(), num_unwinds as usize);
                    let num_tries = read_u32(rdata_section, cur_func_except_record.address + 12)
                        .expect("No try count here!");
                    let mut catches: Vec<Option<SectionAddress>> = Vec::new();
                    let try_map_addr = {
                        let try_map_addr =
                            read_u32(rdata_section, cur_func_except_record.address + 16)
                                .expect("No try count here!");
                        if try_map_addr != 0 {
                            // at this point, we know a try map exists - parse its entries
                            assert!(num_tries > 0);
                            for i in 0..num_tries {
                                let cur_catch_sym =
                                    read_u32(rdata_section, try_map_addr + (i * 20) + 16)
                                        .expect("No catch symbol here!");
                                if cur_catch_sym != 0 {
                                    // parse THAT to get the catch
                                    let maybe_catch_addr =
                                        read_u32(rdata_section, cur_catch_sym + 12)
                                            .expect("No catch addr here!");
                                    if maybe_catch_addr != 0 {
                                        let addr = SectionAddress::new(
                                            obj.sections.at_address(maybe_catch_addr)?.0,
                                            maybe_catch_addr,
                                        );
                                        syms_to_add.push(ObjSymbol {
                                            name: format!("__catch${:08X}", addr.address),
                                            address: addr.address as u64,
                                            section: Some(addr.section),
                                            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                                            ..Default::default()
                                        });
                                        known_exception_addrs.insert(addr);
                                        catches.push(Some(addr));
                                        catch_addrs.insert(addr);
                                    } else {
                                        catches.push(None);
                                    }
                                } else {
                                    catches.push(None);
                                }
                            }
                            Some(SectionAddress::new(rdata_sec_idx, try_map_addr))
                        } else {
                            None
                        }
                    };
                    assert_eq!(catches.len(), num_tries as usize);
                    let num_ip_to_states =
                        read_u32(rdata_section, cur_func_except_record.address + 20)
                            .expect("No IP to state count here!");
                    let ip_to_state_map_addr = {
                        let ip_to_state_map_addr =
                            read_u32(rdata_section, cur_func_except_record.address + 24)
                                .expect("No IP to state map here!");
                        if ip_to_state_map_addr != 0 {
                            Some(SectionAddress::new(rdata_sec_idx, ip_to_state_map_addr))
                        } else {
                            None
                        }
                    };

                    obj.funcs_with_cxx_handlers.insert(func_start_addr, CXXEhFuncInfo {
                        addr: cur_func_except_record,
                        unwind_map_addr,
                        unwinds,
                        num_tries,
                        try_map_addr,
                        catches,
                        num_ip_to_states,
                        ip_to_state_map_addr,
                    });

                    // this is a known C++ function, but exceptions make it hard to deduce the ending
                    obj.known_functions.insert(func_start_addr, None);
                    obj.pdata_funcs.insert(func_start_addr);
                    num_discovered_funcs += 1;
                }
            } else {
                // we can't deduce if there is exception handling
                todo!("No exception handling in this raw exe?")
            }
        } else {
            // no exception data for this func, we can safely mark down its ending
            obj.known_functions.insert(func_start_addr, Some(num_insts_in_func * 4));
            obj.pdata_funcs.insert(func_start_addr);
            num_discovered_funcs += 1;
        }
    }
    log::info!("Found {} known funcs from SEH!", num_discovered_funcs);
    // if c_handler_addr.is_some() {
    //     log::info!("\tC   exception handlers: {}", obj.excepts.len() + obj.finallys.len());
    //     log::info!("\tC++ exception handlers: {}", obj.unwinds.len() + obj.catches.len());
    // }

    // sanity checks
    for addr in &obj.pdata_funcs {
        // We should not have any known exception addrs in our listed pdata funcs
        assert!(!known_exception_addrs.contains(addr));
    }
    for (addr, ending) in &obj.known_functions {
        // We should not have any known exception addrs in our listed known_functions
        assert!(!known_exception_addrs.contains(addr));
        // and if our function has unwinds and such, we should not have a confirmed ending
        if obj.funcs_with_c_handlers.contains_key(addr)
            || obj.funcs_with_cxx_handlers.contains_key(addr)
        {
            assert!(ending.is_none());
        }
    }
    // every catch should've had an entry in pdata
    for catch in catch_addrs {
        assert!(obj.catches.contains_key(&catch));
    }
    // ditto with C excepts
    for except in c_except_addrs {
        assert!(obj.c_except_addrs.contains_key(&except));
    }

    // add Cxx handler symbol here
    if let Some(cxx_handler) = cxx_handler_addr {
        obj.cxx_handler = Some(cxx_handler);
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

    Ok(())
}
