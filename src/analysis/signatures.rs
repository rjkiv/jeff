use anyhow::{Ok, Result};

use crate::{
    analysis::{
        cfa::SectionAddress,
        tracker::{Relocation, Tracker},
        RelocationTarget,
    },
    obj::{
        ExceptionType::C, ObjDataKind, ObjInfo, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags,
        ObjSymbolKind,
    },
};

fn parse_entry(obj: &mut ObjInfo) -> Result<bool> {
    if let Some(entry) = obj.entry {
        let mut tracker = Tracker::new(obj);
        {
            // the symbol being passed into process_function only needs a name, address, section, and size
            let entry_addr = SectionAddress::new(obj.sections.at_address(entry)?.0, entry);
            let entry_sym = ObjSymbol {
                name: String::from("entry"),
                address: entry,
                section: Some(entry_addr.section),
                size: {
                    let Some(C { handlers }) = &obj.pdata_funcs.get(&entry_addr) else {
                        panic!("entry doesn't have C handlers?");
                    };
                    // the end of the main function body == the start of the first C handler
                    let Some((k, _)) = handlers.first_key_value() else {
                        panic!("entry doesn't have C handlers?");
                    };
                    k.address - entry
                },
                ..Default::default()
            };
            tracker.process_function(obj, &entry_sym)?;
        }

        // rel24s = direct function calls; los = references to data
        let (rel24s, los) = {
            let mut rel24s: Vec<SectionAddress> = Vec::new();
            let mut los: Vec<SectionAddress> = Vec::new();
            for (_reloc_addr, reloc) in &tracker.relocations {
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
            (rel24s, los)
        };

        // we should have 14 rel24s and 4 los for the entry point
        if rel24s.len() != 14 || los.len() != 4 {
            return Ok(false);
        }

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

        obj.add_symbol(
            ObjSymbol {
                name: String::from("XapiInitProcess"), // in pdata
                address: rel24s[1].address,
                section: Some(rel24s[1].section),
                size_known: false,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Function,
                ..Default::default()
            },
            false,
        )?;
        obj.add_symbol(
            ObjSymbol {
                name: String::from("XapiCallThreadNotifyRoutines"), // in pdata
                address: rel24s[2].address,
                section: Some(rel24s[2].section),
                size_known: false,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Function,
                ..Default::default()
            },
            false,
        )?;
        obj.add_symbol(
            ObjSymbol {
                name: String::from("XapiPAL50Incompatible"), // in pdata
                address: rel24s[3].address,
                section: Some(rel24s[3].section),
                size_known: false,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Function,
                ..Default::default()
            },
            false,
        )?;
        obj.add_symbol(
            ObjSymbol {
                name: String::from("_mtinit"), // in pdata
                address: rel24s[5].address,
                section: Some(rel24s[5].section),
                size_known: false,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Function,
                ..Default::default()
            },
            false,
        )?;
        obj.add_symbol(
            ObjSymbol {
                name: String::from("_rtinit"), // in pdata
                address: rel24s[6].address,
                section: Some(rel24s[6].section),
                size_known: false,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Function,
                ..Default::default()
            },
            false,
        )?;
        obj.add_symbol(
            ObjSymbol {
                name: String::from("_cinit"), // in pdata
                address: rel24s[7].address,
                section: Some(rel24s[7].section),
                size_known: false,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Function,
                ..Default::default()
            },
            false,
        )?;
        obj.add_symbol(
            ObjSymbol {
                name: String::from("GetCommandLineA"), // in pdata
                address: rel24s[8].address,
                section: Some(rel24s[8].section),
                size_known: false,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Function,
                ..Default::default()
            },
            false,
        )?;
        obj.add_symbol(
            ObjSymbol {
                name: String::from("main"), // in pdata
                address: rel24s[9].address,
                section: Some(rel24s[9].section),
                size_known: false,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Function,
                ..Default::default()
            },
            false,
        )?;
        obj.add_symbol(
            ObjSymbol {
                name: String::from("_cexit"), // NOT in pdata
                address: rel24s[10].address,
                section: Some(rel24s[10].section),
                size_known: false,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Function,
                ..Default::default()
            },
            false,
        )?;
        obj.add_symbol(
            ObjSymbol {
                name: String::from("UnhandledExceptionFilter"), // in pdata
                address: rel24s[13].address,
                section: Some(rel24s[13].section),
                size_known: false,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Function,
                ..Default::default()
            },
            false,
        )?;

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

        return Ok(true);
    } else {
        return Ok(false);
    }
}

pub fn apply_signatures(obj: &mut ObjInfo) -> Result<()> {
    // parse the entry point
    if parse_entry(obj)? {
        println!("Let's keep going!");
    }

    // more common funcs to search patterns of:
    // memset, memmove

    Ok(())
}
