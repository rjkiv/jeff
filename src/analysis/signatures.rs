use anyhow::{Ok, Result};

use crate::{
    analysis::{
        cfa::SectionAddress,
        tracker::{Relocation, Tracker},
        RelocationTarget,
    },
    obj::{ObjDataKind, ObjInfo, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind},
};

fn parse_entry(obj: &mut ObjInfo) -> Result<bool> {
    if let Some(entry) = obj.entry {
        let mut tracker = Tracker::new(obj);
        {
            let (_sym_idx, sym) = obj.symbols.by_name("mainCRTStartup")?.unwrap();
            assert_eq!(sym.address, entry);
            tracker.process_function(obj, sym)?;
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

        // we should have 14 rel24s and 4 los
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
