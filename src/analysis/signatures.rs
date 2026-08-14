use std::collections::HashMap;

use anyhow::{ensure, Ok, Result};
use base64::{engine::general_purpose::STANDARD, Engine};
use memchr::memmem;
use serde::{Deserialize, Serialize};

use crate::{
    analysis::{
        cfa::SectionAddress,
        read_u32,
        tracker::{Relocation, Tracker},
        RelocationTarget,
    },
    obj::{
        ExceptionType::{Normal, C, CXX},
        ObjDataKind, ObjInfo, ObjSectionKind, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags,
        ObjSymbolKind, SymbolIndex,
    },
};

fn add_known_function_symbol(
    obj: &mut ObjInfo,
    name: &str,
    addr: &SectionAddress,
    size_override: Option<u32>, // useful if not in pdata but you know the size ahead of time
) -> Result<SymbolIndex> {
    // deduce a symbol size from our known_functions (or pdata for C++)
    let symbol_size = match size_override {
        Some(size) => Some(size),
        None => {
            // Normal and C funcs should have a size value in known_functions
            match obj.known_functions.get(addr) {
                Some(size_option) => {
                    match size_option {
                        Some(size) => Some(*size),
                        None => {
                            // we have to search for C++ info from pdata
                            if let Some(CXX { info }) = obj.pdata_funcs.get(addr) {
                                let first_unwind = info.unwinds.iter().filter_map(|x| *x).max();
                                let first_catch = info.catches.iter().filter_map(|x| *x).max();
                                // if there are catches and zero unwinds, we have a known ending
                                if let (None, Some(catch)) = (first_unwind, first_catch) {
                                    Some(obj.catches.get(&catch).unwrap().address - addr.address)
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        }
                    }
                }
                None => None,
            }
        }
    };

    obj.add_symbol(
        ObjSymbol {
            name: String::from(name),
            address: addr.address,
            section: Some(addr.section),
            size: symbol_size.unwrap_or_default(),
            size_known: symbol_size.is_some(),
            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            kind: ObjSymbolKind::Function,
            ..Default::default()
        },
        false,
    )
}

// you pass in a function's name and address, and this'll give you the relevant relocs for mapping/labeling
fn get_relocs_for_function(
    obj: &ObjInfo,
    name: &str,
    addr: &SectionAddress,
) -> Result<(Vec<SectionAddress>, Vec<SectionAddress>)> {
    let mut tracker = Tracker::new(obj);
    // the symbol being passed into process_function only needs a name, address, section, and size
    let tracker_sym = ObjSymbol {
        name: String::from(name),
        address: addr.address,
        section: Some(addr.section),
        size: match &obj.pdata_funcs.get(addr) {
            Some(Normal { end }) => end.address - addr.address,
            Some(C { handlers }) => {
                // the end of the main function body == the start of the first C handler
                let Some((k, _)) = handlers.first_key_value() else {
                    panic!("entry doesn't have C handlers?");
                };
                k.address - addr.address
            }
            Some(CXX { info }) => {
                let first_unwind = info.unwinds.iter().filter_map(|x| *x).min();
                let first_catch = info.catches.iter().filter_map(|x| *x).min();
                let main_body_ending = match (first_unwind, first_catch) {
                    (Some(unwind), Some(catch)) => unwind.min(catch),
                    (Some(unwind), None) => unwind,
                    (None, Some(catch)) => catch,
                    _ => return Ok((vec![], vec![])),
                };
                main_body_ending.address - addr.address
            }
            None => {
                // check obj's symbols - we might've added this symbol in beforehand
                // otherwise, we can't reliably deduce function end at this point - empty vecs returned
                if let Some((_, sym)) =
                    obj.symbols.at_section_address(addr.section, addr.address).next()
                {
                    if sym.size_known {
                        sym.size
                    } else {
                        return Ok((vec![], vec![]));
                    }
                } else {
                    return Ok((vec![], vec![]));
                }
            }
        },
        ..Default::default()
    };
    tracker.process_function(obj, &tracker_sym)?;
    let mut rel24s: Vec<SectionAddress> = Vec::new();
    let mut los: Vec<SectionAddress> = Vec::new();
    for reloc in tracker.relocations.values() {
        match reloc {
            Relocation::Rel24(RelocationTarget::Address(a)) => {
                rel24s.push(*a);
            }
            Relocation::Lo(RelocationTarget::Address(a)) => {
                los.push(*a);
            }
            _ => {}
        }
    }
    Ok((rel24s, los))
}

fn parse_entry(obj: &mut ObjInfo, lookup: &mut HashMap<&str, SectionAddress>) -> Result<bool> {
    if let Some(entry) = obj.entry {
        let entry_addr = SectionAddress::new(obj.sections.at_address(entry)?.0, entry);
        let (rel24s, los) = get_relocs_for_function(obj, "entry", &entry_addr)?;

        // we should have 14 rel24s and 4 los for the entry point
        if rel24s.len() != 14 || los.len() != 4 {
            return Ok(false);
        }

        // mark down entrypoint
        add_known_function_symbol(obj, "mainCRTStartup", &entry_addr, None)?;

        // check los[3] - it should be "[XAPI RETURN VALUE] %d\n"
        {
            let data = obj.sections[los[3].section].data_range(los[3].address, 0)?;
            let api_str = data.iter().position(|&b| b == 0).map(|pos| &data[..pos]).unwrap_or(data);
            if api_str != b"[XAPI RETURN VALUE] %d\n" {
                return Ok(false);
            }
        }

        // we're probably good to add the los now
        const LOS_INFOS: [(&str, u32, ObjDataKind); 4] = [
            ("__onexitend", 4, ObjDataKind::Unknown),
            ("__onexitbegin", 4, ObjDataKind::Unknown),
            ("_CRTCommandLineArgs", 4, ObjDataKind::Unknown),
            (
                "??_C@_0BI@IDEPEPLM@?$FLXAPI?5RETURN?5VALUE?$FN?5?$CFd?6?$AA@",
                0x18,
                ObjDataKind::String,
            ),
        ];
        for i in 0..4 {
            obj.add_symbol(
                ObjSymbol {
                    name: String::from(LOS_INFOS[i].0),
                    address: los[i].address,
                    section: Some(los[i].section),
                    size: LOS_INFOS[i].1,
                    size_known: true,
                    flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                    kind: ObjSymbolKind::Object,
                    data_kind: LOS_INFOS[i].2,
                    ..Default::default()
                },
                false,
            )?;
        }

        add_known_function_symbol(obj, "XapiInitProcess", &rel24s[1], None)?;
        add_known_function_symbol(obj, "XapiCallThreadNotifyRoutines", &rel24s[2], None)?;
        add_known_function_symbol(obj, "XapiPAL50Incompatible", &rel24s[3], None)?;
        add_known_function_symbol(obj, "_mtinit", &rel24s[5], None)?;
        add_known_function_symbol(obj, "_rtinit", &rel24s[6], None)?;
        lookup.insert("_rtinit", rel24s[6]);
        add_known_function_symbol(obj, "_cinit", &rel24s[7], None)?;
        lookup.insert("_cinit", rel24s[7]);
        add_known_function_symbol(obj, "GetCommandLineA", &rel24s[8], None)?;
        add_known_function_symbol(obj, "main", &rel24s[9], None)?;
        add_known_function_symbol(obj, "_cexit", &rel24s[10], Some(0xC))?;
        lookup.insert("_cexit", rel24s[10]);
        add_known_function_symbol(obj, "UnhandledExceptionFilter", &rel24s[13], None)?;

        let (r, l) = get_relocs_for_function(obj, "XapiInitProcess", &rel24s[1])?;
        let (r, l) = get_relocs_for_function(obj, "XapiInitHeap", &r[0])?;
        println!("{} {}", r.len(), l.len());

        // Reloc at 4:0x82335EE4: Rel24(Address(4:0x8299D928)) - savegpr 28
        // Reloc at 4:0x82335F14: Rel24(Address(4:0x82336AF0)) - XapiInitProcess
        // Reloc at 4:0x82335F1C: Rel24(Address(4:0x82336920)) - XapiCallThreadNotifyRoutines
        // Reloc at 4:0x82335F20: Rel24(Address(4:0x82335CF0)) - XapiPAL50Incompatible
        // Reloc at 4:0x82335F2C: Rel24(Address(4:0x82EE5624)) - XamTerminateTitle
        // Reloc at 4:0x82335F34: Rel24(Address(4:0x8299F7A0)) - _mtinit
        // Reloc at 4:0x82335F38: Rel24(Address(4:0x823368B0)) - _rtinit
        // Reloc at 4:0x82335F40: Rel24(Address(4:0x823367C8)) - _cinit
        // Reloc at 4:0x82335F68: Rel24(Address(4:0x82336798)) - GetCommandLineA
        // Reloc at 4:0x8233606C: Rel24(Address(4:0x82334268)) - main
        // Reloc at 4:0x82336074: Rel24(Address(4:0x8299F490)) - _cexit
        // Reloc at 4:0x82336084: Rel24(Address(4:0x82EE5764)) - DbgPrint
        // Reloc at 4:0x82336094: Rel24(Address(4:0x82EE5624)) - XamTerminateTitle
        // Reloc at 4:0x823360A4: Rel24(Address(4:0x823355F0)) - UnhandledExceptionFilter

        Ok(true)
    } else {
        Ok(false)
    }
}

fn parse_crt(obj: &mut ObjInfo, lookup: &mut HashMap<&str, SectionAddress>) -> Result<()> {
    // will be called if entry point was successfully parsed
    // so we should be able to further analyze _rtinit, _cinit, _cexit - all in pdata

    // _rtinit will give us __xri_a and __xri_z
    let (_, los) = get_relocs_for_function(obj, "_rtinit", &lookup["_rtinit"])?;
    // should be 2 los (__xri_a/z)
    ensure!(los.len() == 2, "bad _rtinit!");
    let xri_a_addr = los[0];
    let xri_z_addr = los[1];

    obj.add_symbol(
        ObjSymbol {
            name: String::from("__xri_a"),
            address: xri_a_addr.address,
            section: Some(xri_a_addr.section),
            size: xri_z_addr.address - xri_a_addr.address,
            size_known: true,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            kind: ObjSymbolKind::Object,
            ..Default::default()
        },
        false,
    )?;
    obj.add_symbol(
        ObjSymbol {
            name: String::from("__xri_z"),
            address: xri_z_addr.address,
            section: Some(xri_z_addr.section),
            size: 4,
            size_known: true,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            kind: ObjSymbolKind::Object,
            ..Default::default()
        },
        false,
    )?;

    for addr in (xri_a_addr.address..xri_z_addr.address).step_by(4) {
        match addr - xri_a_addr.address {
            0 => {
                // first entry of xri_a - must be 0
                ensure!(
                    read_u32(&obj.sections[xri_a_addr.section], addr).unwrap() == 0,
                    "bad __xri_a!"
                );
            }
            4 => {
                // second entry of xri_a - must be __onexitinit
                let exitinit_addr = {
                    let addr = read_u32(&obj.sections[xri_a_addr.section], addr).unwrap();
                    SectionAddress::new(obj.sections.at_address(addr)?.0, addr)
                };
                add_known_function_symbol(obj, "__onexitinit", &exitinit_addr, None)?;
            }
            8 => {
                // third entry of xri_a - must be _ioinit
                let ioinit_addr = {
                    let addr = read_u32(&obj.sections[xri_a_addr.section], addr).unwrap();
                    SectionAddress::new(obj.sections.at_address(addr)?.0, addr)
                };
                add_known_function_symbol(obj, "_ioinit", &ioinit_addr, None)?;
                let pioinit_addr = SectionAddress::new(xri_a_addr.section, addr);
                obj.add_symbol(
                    ObjSymbol {
                        name: String::from("__pioinit"),
                        address: pioinit_addr.address,
                        section: Some(pioinit_addr.section),
                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                        ..Default::default()
                    },
                    false,
                )?;
            }
            _ => {
                // any further entries are unknown to us, except for the fact they're functions
                let func_addr = {
                    let addr = read_u32(&obj.sections[xri_a_addr.section], addr).unwrap();
                    SectionAddress::new(obj.sections.at_address(addr)?.0, addr)
                };
                obj.known_functions.entry(func_addr).or_default();
            }
        };
    }

    // _cinit will give us __xi_a, __xi_z, __xc_a and __xc_z in that order
    let (_, los) = get_relocs_for_function(obj, "_cinit", &lookup["_cinit"])?;
    // should be 5 los (1 to rdata, __xi_a, __xi_z, __xc_a and __xc_z in that order)
    ensure!(los.len() == 5, "bad _cinit!");
    let xi_a_addr = los[1];
    let xi_z_addr = los[2];
    let xc_a_addr = los[3];
    let xc_z_addr = los[4];

    obj.add_symbol(
        ObjSymbol {
            name: String::from("__xc_a"),
            address: xc_a_addr.address,
            section: Some(xc_a_addr.section),
            size: xc_z_addr.address - xc_a_addr.address,
            size_known: true,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            kind: ObjSymbolKind::Object,
            ..Default::default()
        },
        false,
    )?;
    obj.add_symbol(
        ObjSymbol {
            name: String::from("__xc_z"),
            address: xc_z_addr.address,
            section: Some(xc_z_addr.section),
            size: 4,
            size_known: true,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            kind: ObjSymbolKind::Object,
            ..Default::default()
        },
        false,
    )?;
    obj.add_symbol(
        ObjSymbol {
            name: String::from("__xi_a"),
            address: xi_a_addr.address,
            section: Some(xi_a_addr.section),
            size: xi_z_addr.address - xi_a_addr.address,
            size_known: true,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            kind: ObjSymbolKind::Object,
            ..Default::default()
        },
        false,
    )?;
    obj.add_symbol(
        ObjSymbol {
            name: String::from("__xi_z"),
            address: xi_z_addr.address,
            section: Some(xi_z_addr.section),
            size: 4,
            size_known: true,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            kind: ObjSymbolKind::Object,
            ..Default::default()
        },
        false,
    )?;

    let mut num_sinits = 0;
    for addr in (xc_a_addr.address..xc_z_addr.address).step_by(4) {
        let sinit_addr = read_u32(&obj.sections[xc_a_addr.section], addr).unwrap();
        if sinit_addr != 0 {
            let sinit_sec_addr =
                SectionAddress::new(obj.sections.at_address(sinit_addr)?.0, sinit_addr);
            obj.known_functions.entry(sinit_sec_addr).or_default();
            num_sinits += 1;
        }
    }
    log::info!("Found {} known static initializer funcs!", num_sinits);

    // TODO: add funcs from __xi_a/__xi_z and determine if we can give them hard names

    // _cexit -> doexit (in pdata), which will give us __xp_a, __xp_z, __xt_a, __xt_z

    let (doexitrel, _) = get_relocs_for_function(obj, "_cexit", &lookup["_cexit"])?;
    // should only be 1 rel to doexit
    ensure!(doexitrel.len() == 1, "bad _cexit!");
    add_known_function_symbol(obj, "doexit", &doexitrel[0], None)?;
    let (_, los) = get_relocs_for_function(obj, "doexit", &doexitrel[0])?;
    ensure!(los.len() >= 4, "bad doexit!"); // we only want the last 4, those are our xp/xt's
    let remaining_vars = &los[los.len() - 4..];
    let xp_a_addr = remaining_vars[0].min(remaining_vars[1]);
    let xp_z_addr = remaining_vars[0].max(remaining_vars[1]);
    let xt_a_addr = remaining_vars[2].min(remaining_vars[3]);
    let xt_z_addr = remaining_vars[2].max(remaining_vars[3]);

    obj.add_symbol(
        ObjSymbol {
            name: String::from("__xp_a"),
            address: xp_a_addr.address,
            section: Some(xp_a_addr.section),
            size: xp_z_addr.address - xp_a_addr.address,
            size_known: true,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            kind: ObjSymbolKind::Object,
            ..Default::default()
        },
        false,
    )?;
    obj.add_symbol(
        ObjSymbol {
            name: String::from("__xp_z"),
            address: xp_z_addr.address,
            section: Some(xp_z_addr.section),
            size: 4,
            size_known: true,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            kind: ObjSymbolKind::Object,
            ..Default::default()
        },
        false,
    )?;
    obj.add_symbol(
        ObjSymbol {
            name: String::from("__xt_a"),
            address: xt_a_addr.address,
            section: Some(xt_a_addr.section),
            size: xt_z_addr.address - xt_a_addr.address,
            size_known: true,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            kind: ObjSymbolKind::Object,
            ..Default::default()
        },
        false,
    )?;
    obj.add_symbol(
        ObjSymbol {
            name: String::from("__xt_z"),
            address: xt_z_addr.address,
            section: Some(xt_z_addr.section),
            size: 4,
            size_known: true,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            kind: ObjSymbolKind::Object,
            ..Default::default()
        },
        false,
    )?;

    // todo mark addrs in xp/xt

    Ok(())
}

const FUNCTION_SIGNATURES: [(&str, u32, &str); 3] = [
    ("_CxxThrowException", 0x84, "fYgCpv////+Rgf/4//////vB/+j/////++H/8P////+UIf9w/////z1gAAD//wAAfH4beP////98nyN4/////zgAAAD8AAAAOAAAAPwAAAA4oAAg/////0gAAAH8AAADk8EAaP////+T4QBs/////ysfAAD/////QZoAHP////+BfwAA/////1VrBzn/////QYIAEP////89YAGZ/////2FrQAD/////kWEAZP////84wQBk/////4ChAGD/////gIEAVP////+AYQBQ/////0gAAAH8AAADOCEAkP////+Bgf/4/////32IA6b/////68H/6P/////r4f/w/////06AACD/////"),
    ("_initterm", 0x58, "fYgCpv////+Rgf/4//////vB/+j/////++H/8P////+UIf+Q/////3x/G3j/////fJ4jeP////9IAAAc/////4F/AAD/////KAsAAPw///9BggAM/+f//31pA6b/////ToAEIf////87/wAE/////38f8ED/////QZj/5P////84IQBw/////4GB//j/////fYgDpv/////rwf/o/////+vh//D/////ToAAIP////8="),
    ("memset", 0xA0, "OAUAAf////98CQOm/////2BmAAD/////SAAAEP////84pf///////5iGAAD/////OMYAAf////9wwAAD/////0AC//D/////UIRELv////9UoOE//////1CEgB7/////QeIAIP////98CQOm/////5CGAAD/////kIYABP////+QhgAI/////5CGAAz/////OMYAEP////9DIP/s/////1Sg97//////QcIAKP////98CQOm/////5CGAAD/////OMYABP////9DQAAY/////5CGAAD/////OMYABP////9DQAAM/////5CGAAD/////OMYABP////9woAAD/////3wJA6b/////TeIAIP////+YhgAA/////09AACD/////mIYAAf////9PQAAg/////5iGAAL/////ToAAIP////8=")
];

// will probably modify these to go into FUNCTION_SIGNATURES, dunno yet, still experimenting
const FUNCTION_BYTES: [(&str, u32, &str); 3] = [
    ("memset", 0xA0, "OAUAAXwJA6ZgZgAASAAAEDil//+YhgAAOMYAAXDAAANAAv/wUIRELlSg4T9QhIAeQeIAIHwJA6aQhgAAkIYABJCGAAiQhgAMOMYAEEMg/+xUoPe/QcIAKHwJA6aQhgAAOMYABENAABiQhgAAOMYABENAAAyQhgAAOMYABHCgAAN8CQOmTeIAIJiGAABPQAAgmIYAAU9AACCYhgACToAAIA=="),
    ("_initterm", 0x58, "fYgCppGB//j7wf/o++H/8JQh/5B8fxt4fJ4jeEgAAByBfwAAKwsAAEGaAAx9aQOmToAEITv/AAR/H/BAQZj/5DghAHCBgf/4fYgDpuvB/+jr4f/wToAAIA=="),
    ("_initterm", 0x58, "fYgCppGB//j7wf/o++H/8JQh/5B8fxt4fJ4jeEgAAByBfwAAKAsAAEGCAAx9aQOmToAEITv/AAR/H/BAQZj/5DghAHCBgf/4fYgDpuvB/+jr4f/wToAAIA=="),
];

fn match_function_bytes(obj: &mut ObjInfo) -> Result<()> {
    let mut syms_to_add: Vec<(&str, u32, SectionAddress)> = vec![];
    for (func_name, func_size, func_str) in FUNCTION_BYTES {
        let func_bytes = STANDARD.decode(func_str)?;
        for (section_index, section) in obj.sections.by_kind(ObjSectionKind::Code) {
            if let Some(pos) = memmem::find(&section.data, &func_bytes) {
                let func_start_addr =
                    SectionAddress::new(section_index, section.address + pos as u32);
                syms_to_add.push((func_name, func_size, func_start_addr));
                break;
            }
        }
    }
    for (func_name, func_size, func_start_addr) in syms_to_add {
        add_known_function_symbol(obj, func_name, &func_start_addr, Some(func_size))?;
    }
    Ok(())
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
struct OutReference {
    pub name: String,
    #[serde(default)]
    pub kind: ObjSymbolKind,
    #[serde(default)]
    pub size: u32,
    #[serde(default)]
    pub optional: bool,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
struct FunctionSignature {
    pub name: String,
    #[serde(default)]
    pub pdata_type: u8,
    #[serde(default)]
    pub num_handlers: u8,
    #[serde(default)]
    pub size: u32,
    #[serde(default)]
    pub signature: String,
    #[serde(default)]
    pub references: Vec<OutReference>,
}

// you pass in a function's name and address, and this'll give you the relevant relocs for mapping/labeling
fn get_function_references(
    obj: &ObjInfo,
    name: &str,
    addr: &SectionAddress,
) -> Result<Vec<SectionAddress>> {
    let mut tracker = Tracker::new(obj);
    // the symbol being passed into process_function only needs a name, address, section, and size
    let tracker_sym = ObjSymbol {
        name: String::from(name),
        address: addr.address,
        section: Some(addr.section),
        size: match &obj.pdata_funcs.get(addr) {
            Some(Normal { end }) => end.address - addr.address,
            Some(C { handlers }) => {
                // the end of the main function body == the start of the first C handler
                let Some((k, _)) = handlers.first_key_value() else {
                    panic!("entry doesn't have C handlers?");
                };
                k.address - addr.address
            }
            Some(CXX { info }) => {
                let first_unwind = info.unwinds.iter().filter_map(|x| *x).min();
                let first_catch = info.catches.iter().filter_map(|x| *x).min();
                let main_body_ending = match (first_unwind, first_catch) {
                    (Some(unwind), Some(catch)) => unwind.min(catch),
                    (Some(unwind), None) => unwind,
                    (None, Some(catch)) => catch,
                    _ => return Ok(vec![]),
                };
                main_body_ending.address - addr.address
            }
            None => {
                // check obj's symbols - we might've added this symbol in beforehand
                // otherwise, we can't reliably deduce function end at this point - empty vecs returned
                if let Some((_, sym)) =
                    obj.symbols.at_section_address(addr.section, addr.address).next()
                {
                    if sym.size_known {
                        sym.size
                    } else {
                        return Ok(vec![]);
                    }
                } else {
                    return Ok(vec![]);
                }
            }
        },
        ..Default::default()
    };
    tracker.process_function(obj, &tracker_sym)?;
    let mut refs = vec![];
    for reloc in tracker.relocations.values() {
        match reloc {
            Relocation::Rel24(RelocationTarget::Address(a)) => {
                refs.push(*a);
            }
            Relocation::Lo(RelocationTarget::Address(a)) => {
                refs.push(*a);
            }
            _ => {}
        }
    }
    Ok(refs)
}

fn add_symbol_from_reference(
    obj: &mut ObjInfo,
    addr: &SectionAddress,
    reference: &OutReference,
) -> Result<SymbolIndex> {
    // deduce a symbol size from our known_functions (or pdata for C++)
    let symbol_size = {
        let mut size = reference.size;
        if size == 0 {
            // Normal and C funcs should have a size value in known_functions
            if let Some(size_option) = obj.known_functions.get(addr) {
                if let Some(s) = size_option {
                    size = *s;
                }
                // we have to search for C++ info from pdata
                else if let Some(CXX { info }) = obj.pdata_funcs.get(addr) {
                    let first_unwind = info.unwinds.iter().filter_map(|x| *x).max();
                    let first_catch = info.catches.iter().filter_map(|x| *x).max();
                    // if there are catches and zero unwinds, we have a known ending
                    if let (None, Some(catch)) = (first_unwind, first_catch) {
                        size = obj.catches.get(&catch).unwrap().address - addr.address;
                    }
                }
            }
        }
        size
    };
    obj.add_symbol(
        ObjSymbol {
            name: reference.name.clone(),
            address: addr.address,
            section: Some(addr.section),
            size: symbol_size,
            size_known: symbol_size != 0,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            kind: reference.kind,
            ..Default::default()
        },
        false,
    )
}

fn try_parse_entry(obj: &mut ObjInfo) -> Result<bool> {
    let Some(entry) = obj.entry else {
        return Ok(false);
    };
    let entry_yml = include_str!("../../assets/signatures_x360/entry.yml");
    let entry_sig = {
        let sigs: Vec<FunctionSignature> = serde_yaml::from_str(entry_yml)?;
        sigs[0].clone()
    };
    let entry_addr = SectionAddress::new(obj.sections.at_address(entry)?.0, entry);
    let refs = get_function_references(obj, "entry", &entry_addr)?;
    if entry_sig.references.len() != refs.len() || refs.len() != 18 {
        return Ok(false);
    }

    // skip 0, 6, 15, 16
    for i in 1..refs.len() {
        // skipped 0 because it's a reg intrinsic that we'll find later
        // 6, 15 and 16 are all xex imports
        if i == 6 || i == 15 || i == 16 {
            continue;
        }
        add_symbol_from_reference(obj, &refs[i], &entry_sig.references[i])?;
    }

    Ok(true)
}

pub fn apply_signatures(obj: &mut ObjInfo) -> Result<()> {
    let mut funcs_to_analyze: HashMap<&str, SectionAddress> = HashMap::new();

    if try_parse_entry(obj)? {
        println!("Entry successfully parsed!");
    }

    return Ok(());

    // parse the entry point
    if parse_entry(obj, &mut funcs_to_analyze)? {
        // then CRT objects using the funcs we found from the entry point
        parse_crt(obj, &mut funcs_to_analyze)?;

        // get calloc and _errno from what we've parsed up to this point
    }

    // NOTE: a lot of these come from pdata, we can use that as a starting point or reference
    // like, filter by exception type, size range, a set of instructions you know will appear in there

    // _initterm is also in pdata
    // _purecall is in pdata, size:0x4C
    // strstr, atexit
    // isalpha and all the other char checkers

    // match funcs with exact bytes here
    match_function_bytes(obj)?;
    // match funcs with looser signatures here

    // parse throw info and RTTI here?
    // if, after the C scope tables, there's still .rdata left, check for _CxxThrowException, then throw info
    // _CxxThrowException is in pdata, Normal exception type

    // more common funcs to search patterns of:
    // memmove, strncmp
    // in pdata: malloc, free, errno, printf

    // if we have RTTI, these two *should* exist somewhere:
    // typeid - is a C except func with one exception
    // dynamic_cast - is a C except func with one exception
    // look for the strings "Bad dynamic_cast!" and "no RTTI data!"

    // XGetOverlappedResult
    // CreateThread

    // move _RtlCheckStack/12 check here

    Ok(())
}
