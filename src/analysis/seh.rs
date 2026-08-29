use std::collections::BTreeMap;

use anyhow::{Result, bail};

use crate::{
    analysis::{cfa::SectionAddress, read_u32},
    obj::{ObjInfo, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind, PdataFuncInfo},
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
pub struct CxxEhFuncInfo {
    // The address of the __ehfuncinfo$ itself
    pub addr: SectionAddress,
    // unwind map addr and number of entries - __unwindtable$
    pub unwind_map: Option<(SectionAddress, u32)>,

    // try map addr, and number of entries - __tryblocktable$, which contains __catchsym$
    // we can only have one try block table...
    pub try_block_map: Option<(SectionAddress, u32)>,
    // TODO mark the catchsyms
    // but we can have multiple catchsyms
    // pub catch_map: Vec<(SectionAddress, u32)>

    // iptostate map addr, and number of entries - parsing this map likely not needed for the purposes of labeling functions/eh objects
    pub ip_to_state_map: Option<(SectionAddress, u32)>,
}

pub fn process_seh(obj: &mut ObjInfo) -> Result<()> {
    // add known function boundaries from pdata
    let (_, pdata_section) = obj.sections.by_name(".pdata")?.expect("No .pdata section!");

    // We need this to parse C/C++ exception info structs
    let (rdata_sec_idx, rdata_section) =
        obj.sections.by_name(".rdata")?.expect("No .rdata section!");

    // We need this to reliably distinguish C exceptions from C++ exceptions
    let c_handler_addr = {
        let (_, c_sym) = obj
            .symbols
            .by_name("__C_specific_handler")?
            .expect("No C exception handling in this raw exe?");
        SectionAddress::new(
            c_sym
                .section
                .expect("C handler should have a section specified!"),
            c_sym.address,
        )
    };
    let mut cxx_handler_addr: Option<SectionAddress> = None;
    // C/CXX exception handler start addresses, and their sizes
    let mut known_exceptions: BTreeMap<SectionAddress, u32> = BTreeMap::new();

    for chunk in pdata_section.data.as_chunks::<8>().0 {
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
        if let Some(size) = known_exceptions.get_mut(&func_start_addr) {
            *size = num_insts_in_func * 4;
            if func_type == 3 {
                obj.exception_data_infos.insert(func_start_addr - 8);
            }
            continue;
        }

        // if func_type == 3, there's an 8 byte struct (with 2 words) just before the function start that contains exception data
        if func_type == 3 {
            obj.exception_data_infos.insert(func_start_addr - 8);
            let cur_func_except_handler: SectionAddress;
            let cur_func_except_record: SectionAddress;

            obj.symbols.add(
                ObjSymbol {
                    name: format!("except_data_{:08X}", func_start_addr.address - 8),
                    address: func_start_addr.address - 8,
                    section: Some(func_start_addr.section),
                    size: 8,
                    size_known: true,
                    flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                    kind: ObjSymbolKind::Object,
                    ..Default::default()
                },
                false,
            )?;

            // word 1: the address of the function's exception handler
            if let Some(except_func) =
                read_u32(obj.sections.at_address(start_addr - 8)?.1, start_addr - 8)
            {
                cur_func_except_handler =
                    SectionAddress::new(obj.sections.at_address(except_func)?.0, except_func);
            } else {
                bail!(
                    "Invalid exception handler address listed at {}!",
                    start_addr - 8
                )
            }
            // word 2: the address of the function's exception handler data record
            if let Some(except_record) =
                read_u32(obj.sections.at_address(start_addr - 4)?.1, start_addr - 4)
            {
                // one specific exception handler can have no record (a nullptr in the exception data)
                if except_record != 0 {
                    cur_func_except_record = SectionAddress::new(
                        obj.sections.at_address(except_record)?.0,
                        except_record,
                    );
                } else {
                    // There is only one known except_data pair that won't have an exception record pointer,
                    // and that's for the func _CallCatchBlock, whose exception handler is _SkipUnwoundFrames
                    obj.symbols.add(
                        ObjSymbol {
                            name: String::from("_CallCatchBlock"),
                            address: func_start_addr.address,
                            section: Some(func_start_addr.section),
                            size: 0x24,
                            size_known: true,
                            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                            kind: ObjSymbolKind::Function,
                            ..Default::default()
                        },
                        false,
                    )?;
                    obj.symbols.add(
                        ObjSymbol {
                            name: String::from("_SkipUnwoundFrames"),
                            address: cur_func_except_handler.address,
                            section: Some(cur_func_except_handler.section),
                            size: 0x28,
                            size_known: true,
                            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                            kind: ObjSymbolKind::Function,
                            ..Default::default()
                        },
                        false,
                    )?;
                    continue;
                }
            } else {
                bail!(
                    "Invalid exception record address listed at {}!",
                    start_addr - 4
                )
            }

            // C handler
            if c_handler_addr == cur_func_except_handler {
                // parse the C Scope table that's located at cur_func_except_record
                assert_eq!(
                    rdata_sec_idx, cur_func_except_record.section,
                    "Except record not in .rdata?"
                );
                let num_scope_entries = read_u32(rdata_section, cur_func_except_record.address)
                    .expect("No exception record here!");
                let entry_addrs_begin = cur_func_except_record.address + 4;
                let mut handlers: BTreeMap<SectionAddress, u32> = BTreeMap::new();
                for i in 0..num_scope_entries {
                    let handler = read_u32(rdata_section, entry_addrs_begin + (i * 16) + 8)
                        .expect("No handler here!");
                    let addr = SectionAddress::new(obj.sections.at_address(handler)?.0, handler);
                    obj.symbols.add(
                        ObjSymbol {
                            name: format!("$LN{:08X}", addr.address),
                            address: addr.address,
                            section: Some(addr.section),
                            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                            ..Default::default()
                        },
                        false,
                    )?;
                    known_exceptions.entry(addr).or_default();
                    handlers.entry(addr).or_default();
                }
                assert_eq!(handlers.len(), num_scope_entries as usize);
                obj.symbols.add(
                    ObjSymbol {
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
                    },
                    false,
                )?;
                obj.pdata_funcs.insert(
                    func_start_addr,
                    PdataFuncInfo {
                        main_size: num_insts_in_func * 4,
                        full_size: num_insts_in_func * 4,
                        handlers,
                        exception_info: None,
                    },
                );
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

                let mut cur_exceptions: BTreeMap<SectionAddress, u32> = BTreeMap::new();
                let unwind_map: Option<(SectionAddress, u32)> = {
                    let num_unwinds = read_u32(rdata_section, cur_func_except_record.address + 4)
                        .expect("No unwind count here");
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
                                obj.symbols.add(
                                    ObjSymbol {
                                        name: format!("__unwind${:08X}", addr.address),
                                        address: addr.address,
                                        section: Some(addr.section),
                                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                                        ..Default::default()
                                    },
                                    false,
                                )?;
                                known_exceptions.entry(addr).or_default();
                                cur_exceptions.entry(addr).or_default();
                            }
                        }
                        Some((
                            SectionAddress::new(rdata_sec_idx, unwind_map_addr),
                            num_unwinds,
                        ))
                    } else {
                        None
                    }
                };

                let try_block_map: Option<(SectionAddress, u32)> = {
                    let num_try_blocks =
                        read_u32(rdata_section, cur_func_except_record.address + 12)
                            .expect("No try block count here!");
                    let try_block_map_addr =
                        read_u32(rdata_section, cur_func_except_record.address + 16)
                            .expect("No try block map here!");
                    if try_block_map_addr != 0 {
                        // at this point, we know a try map exists - parse its entries
                        assert!(num_try_blocks > 0);
                        for i in 0..num_try_blocks {
                            let num_catches =
                                read_u32(rdata_section, try_block_map_addr + (i * 20) + 12)
                                    .expect("No catch count here!");
                            let catch_handler_array_addr =
                                read_u32(rdata_section, try_block_map_addr + (i * 20) + 16)
                                    .expect("No catch symbol here!");
                            if catch_handler_array_addr != 0 {
                                // at this point, we know catches exist - parse its entries
                                assert!(num_catches > 0);
                                for j in 0..num_catches {
                                    // RTTI Type Descriptor at catch_handler_array_addr + (j * 16) + 8 - should we mark it down?

                                    let catch_handler = read_u32(
                                        rdata_section,
                                        catch_handler_array_addr + (j * 16) + 12,
                                    )
                                    .expect("No catch handler here!");
                                    if catch_handler != 0 {
                                        // println!("Catch at {:08X}", catch_handler);
                                        let addr = SectionAddress::new(
                                            obj.sections.at_address(catch_handler)?.0,
                                            catch_handler,
                                        );
                                        obj.symbols.add(
                                            ObjSymbol {
                                                name: format!("__catch${:08X}", addr.address),
                                                address: addr.address,
                                                section: Some(addr.section),
                                                flags: ObjSymbolFlagSet(
                                                    ObjSymbolFlags::Global.into(),
                                                ),
                                                ..Default::default()
                                            },
                                            false,
                                        )?;
                                        cur_exceptions.entry(addr).or_default();
                                        known_exceptions.entry(addr).or_default();
                                    }
                                }
                            }
                        }
                        Some((
                            SectionAddress::new(rdata_sec_idx, try_block_map_addr),
                            num_try_blocks,
                        ))
                    } else {
                        None
                    }
                };
                let ip_to_state_map = {
                    let num_ip_to_states =
                        read_u32(rdata_section, cur_func_except_record.address + 20)
                            .expect("No IP to state count here!");
                    let ip_to_state_map_addr =
                        read_u32(rdata_section, cur_func_except_record.address + 24)
                            .expect("No IP to state map here!");
                    if ip_to_state_map_addr != 0 {
                        Some((
                            SectionAddress::new(rdata_sec_idx, ip_to_state_map_addr),
                            num_ip_to_states,
                        ))
                    } else {
                        None
                    }
                };

                obj.pdata_funcs.insert(
                    func_start_addr,
                    PdataFuncInfo {
                        main_size: num_insts_in_func * 4,
                        full_size: num_insts_in_func * 4,
                        handlers: cur_exceptions,
                        exception_info: Some(CxxEhFuncInfo {
                            addr: cur_func_except_record,
                            unwind_map,
                            try_block_map,
                            ip_to_state_map,
                        }),
                    },
                );
            }
        } else {
            obj.pdata_funcs.insert(
                func_start_addr,
                PdataFuncInfo {
                    main_size: num_insts_in_func * 4,
                    full_size: num_insts_in_func * 4,
                    handlers: BTreeMap::default(),
                    exception_info: None,
                },
            );
        }
    }

    for (func, info) in obj.pdata_funcs.iter_mut() {
        for (start, size) in info.handlers.iter_mut() {
            // set size = the lookup from known_exceptions
            *size = *known_exceptions.get(start).unwrap();
        }
        // set full size from handlers, if it's not empty
        if !info.handlers.is_empty() {
            let (last_start, last_size) = info.handlers.last_key_value().unwrap();
            let last_end_addr = *last_start + *last_size;
            info.full_size = last_end_addr.address - func.address;
        }
        obj.known_functions.insert(*func, Some(info.full_size));
    }

    log::info!("Found {} known funcs from SEH!", obj.pdata_funcs.len());
    log::info!(
        "\tFuncs with C   exceptions: {}",
        obj.pdata_funcs.values().filter(|info| info.is_c()).count()
    );
    log::info!(
        "\tFuncs with CXX exceptions: {}",
        obj.pdata_funcs
            .values()
            .filter(|info| info.is_cxx())
            .count()
    );

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
    }

    Ok(())
}
