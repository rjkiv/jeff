use std::collections::{btree_map::Entry, BTreeMap, BTreeSet};

use anyhow::{bail, Result};

use crate::{
    analysis::{cfa::SectionAddress, read_u32},
    obj::{
        ExceptionType::{Normal, C, CXX},
        ObjInfo, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind,
    },
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
                sym.address,
            )
        });
    let mut cxx_handler_addr: Option<SectionAddress> = None;

    // key = the func that has C exceptions, value = each of the exception handlers' start addrs
    let mut tmp_c_funcs: BTreeMap<SectionAddress, Vec<SectionAddress>> = BTreeMap::new();
    // key = exception handler start addr, value = exception handler end addr
    let mut tmp_c_except_addrs: BTreeMap<SectionAddress, SectionAddress> = BTreeMap::new();

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
                // obj.c_except_addrs.insert(func_start_addr, end_addr);
                tmp_c_except_addrs.insert(func_start_addr, end_addr);
            }
            continue;
        }

        // if func_type == 3, there's an 8 byte struct (with 2 words) just before the function start that contains exception data
        if func_type == 3 {
            // break glass in case of emergency
            // syms_to_add.push(ObjSymbol {
            //     name: format!("except_data_{:08X}", start_addr - 8),
            //     address: (start_addr - 8) ,
            //     section: Some(func_start_addr.section),
            //     size: 8,
            //     size_known: true,
            //     flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            //     kind: ObjSymbolKind::Object,
            //     ..Default::default()
            // });
            obj.exception_data_infos.insert(func_start_addr - 8);
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
                        address: func_start_addr.address,
                        section: Some(func_start_addr.section),
                        // change this to size: 0x24 once you're sure it's the same size throughout all xexes
                        size_known: false,
                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                        kind: ObjSymbolKind::Function,
                        ..Default::default()
                    });
                    syms_to_add.push(ObjSymbol {
                        name: String::from("_SkipUnwoundFrames"),
                        address: cur_func_except_handler.address,
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
                        let addr =
                            SectionAddress::new(obj.sections.at_address(handler)?.0, handler);
                        syms_to_add.push(ObjSymbol {
                            name: format!("$LN{:08X}", addr.address),
                            address: addr.address,
                            section: Some(addr.section),
                            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                            ..Default::default()
                        });
                        c_except_addrs.insert(addr);
                        known_exception_addrs.insert(addr);
                        handlers.push(addr);
                    }
                    assert_eq!(handlers.len(), num_scope_entries as usize);
                    syms_to_add.push(ObjSymbol {
                        name: format!("T${:08X}", cur_func_except_record.address),
                        address: cur_func_except_record.address,
                        section: Some(cur_func_except_record.section),
                        // size of scope table: 16 * num_scope_entries + 4
                        // where 16 = size of scope table entry, 4 = the word that contains the number of scope entries
                        size: (handlers.len() * 16 + 4) as u32,
                        size_known: true,
                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                        kind: ObjSymbolKind::Object,
                        ..Default::default()
                    });
                    tmp_c_funcs.insert(func_start_addr, handlers.clone());

                    // this is a known C function, but exceptions make it hard to deduce the ending
                    obj.known_functions.insert(func_start_addr, None);
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
                                        address: addr.address,
                                        section: Some(addr.section),
                                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                                        ..Default::default()
                                    });
                                    known_exception_addrs.insert(addr);
                                    unwinds.push(Some(addr));
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
                                            address: addr.address,
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
                    obj.pdata_funcs.insert(func_start_addr, CXX {
                        info: CXXEhFuncInfo {
                            addr: cur_func_except_record,
                            unwind_map_addr,
                            unwinds,
                            num_tries,
                            try_map_addr,
                            catches,
                            num_ip_to_states,
                            ip_to_state_map_addr,
                        },
                    });
                    // this is a known C++ function, but exceptions make it hard to deduce the ending
                    // Note: if a func has both unwinds and catches, catches come first, then unwinds
                    // unwinds don't always show up in pdata, so we can't reliably deduce the full func ending
                    obj.known_functions.insert(func_start_addr, None);
                    num_discovered_funcs += 1;
                }
            } else {
                // we can't deduce if there is exception handling
                todo!("No exception handling in this raw exe?")
            }
        } else {
            // no exception data for this func, we can safely mark down its ending
            obj.known_functions.insert(func_start_addr, Some(num_insts_in_func * 4));
            obj.pdata_funcs
                .insert(func_start_addr, Normal { end: func_start_addr + num_insts_in_func * 4 });
            num_discovered_funcs += 1;
        }
    }

    for (c_func, c_func_handler_addrs) in &tmp_c_funcs {
        let mut c_func_handler_bounds: BTreeMap<SectionAddress, SectionAddress> = BTreeMap::new();
        for handler in c_func_handler_addrs {
            c_func_handler_bounds.insert(*handler, tmp_c_except_addrs[handler]);
        }
        // this whole func's ending is at the end of the last C handler
        let ending = c_func_handler_bounds.values().max().expect("No handlers?");
        let full_c_func_size = ending.address - c_func.address;
        // update the now-known ending of this C func
        obj.known_functions.insert(*c_func, Some(full_c_func_size));
        obj.pdata_funcs.insert(*c_func, C { handlers: c_func_handler_bounds });
    }

    log::info!("Found {} known funcs from SEH!", num_discovered_funcs);
    log::info!(
        "\tFuncs with C   exceptions: {}",
        obj.pdata_funcs.values().filter(|e| matches!(e, C { handlers: _ })).count()
    );
    log::info!(
        "\tFuncs with CXX exceptions: {}",
        obj.pdata_funcs.values().filter(|e| matches!(e, CXX { info: _ })).count()
    );

    // sanity checks
    for addr in obj.pdata_funcs.keys() {
        // We should not have any known exception addrs in our listed pdata funcs
        assert!(!known_exception_addrs.contains(addr));
    }
    for (addr, ending) in &obj.known_functions {
        // We should not have any known exception addrs in our listed known_functions
        assert!(!known_exception_addrs.contains(addr));
        // and if our function has unwinds and such, we should not have a confirmed ending
        if matches!(obj.pdata_funcs.get(addr), Some(CXX { .. })) {
            assert!(ending.is_none());
        }
    }
    // every catch should've had an entry in pdata
    for catch in catch_addrs {
        assert!(obj.catches.contains_key(&catch));
    }
    // ditto with C excepts
    // for except in c_except_addrs {
    //     assert!(obj.c_except_addrs.contains_key(&except));
    // }

    // add Cxx handler symbol here
    if let Some(cxx_handler) = cxx_handler_addr {
        obj.cxx_handler = Some(cxx_handler);
        obj.add_symbol(
            ObjSymbol {
                name: String::from("__CxxFrameHandler"),
                address: cxx_handler.address,
                section: Some(cxx_handler.section),
                size: 0x38,
                size_known: true,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Function,
                ..Default::default()
            },
            false,
        )?;
        // traverse call chain from __CxxFrameHandler?
    }

    // then for each except_data/except_record symbol (might remove later idk)
    for sym in syms_to_add {
        obj.add_symbol(sym, false)?;
    }

    Ok(())
}
