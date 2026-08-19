use std::{fs, fs::File, io::Read, num::NonZeroU32};

use anyhow::{bail, ensure, Result};
use base64::{engine::general_purpose::STANDARD, Engine};
use memchr::memmem;
use object::{read::pe::PeFile32, Object, ObjectSection, SectionKind};
use typed_path::Utf8NativePathBuf;

use crate::{
    analysis::{
        cfa::SectionAddress, read_u32, rtti::process_rtti, seh::process_seh,
        signatures::apply_signature,
    },
    obj::{
        ExceptionType::Normal, ObjInfo, ObjKind, ObjSection, ObjSectionKind, ObjSymbol,
        ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind, SymbolIndex,
    },
    util::{
        read::read_word,
        xex::XexInfo,
        xex_imports::replace_ordinal,
        xex_optional_headers::{ImportLibrary, XexOptionalHeader},
    },
};

// the type of the executable binary initially passed in
enum ExeType {
    Exe,
    Xex { import_libraries: Option<Vec<ImportLibrary>> },
}

// an executable binary passed in from a config.yml
// this class exists to allow the user the option to enter either an xex or an X360 compatible exe in their yml
pub struct InputtedExecutable {
    exe_name: String,
    exe_bytes: Vec<u8>,
    exe_type: ExeType,
}

impl InputtedExecutable {
    pub fn new(
        base_path: &Utf8NativePathBuf,
        // path to title update xexp, currently unimplemented
        patch_path: Option<Utf8NativePathBuf>,
    ) -> Result<Self> {
        let mut magic_bytes = [0u8; 4];
        {
            let mut file = File::open(base_path)?;
            ensure!(file.metadata()?.len() >= 4, "File too small to be a valid executable");
            file.read_exact(&mut magic_bytes)?;
        }
        // if xex, call XexInfo::from_file
        if magic_bytes == *b"XEX2" {
            let xex = XexInfo::from_files(base_path, patch_path)?;

            let orig_name = xex
                .optional_headers
                .iter()
                .find_map(|h| match h {
                    XexOptionalHeader::OriginalPEName { name } if !name.is_empty() => {
                        Some(name.clone())
                    }
                    _ => None,
                })
                .unwrap_or_else(|| String::from("output.exe"));

            let import_libraries = xex.optional_headers.into_iter().find_map(|h| match h {
                XexOptionalHeader::ImportLibraries { libraries } => Some(libraries),
                _ => None,
            });

            Ok(Self {
                exe_name: orig_name,
                exe_bytes: xex.exe_bytes,
                exe_type: ExeType::Xex { import_libraries },
            })
        }
        // if exe, just pass in name/bytes and that's that
        else if magic_bytes.starts_with(b"MZ") {
            Ok(Self {
                exe_name: base_path.file_name().expect("Missing executable name!").to_string(),
                exe_bytes: fs::read(base_path)?,
                exe_type: ExeType::Exe,
            })
        } else {
            bail!("Unrecognized executable type!");
        }
    }

    pub fn is_xex(&self) -> bool { matches!(self.exe_type, ExeType::Xex { import_libraries: _ }) }

    pub fn extract(&self) -> (String, &Vec<u8>) { (self.exe_name.clone(), &self.exe_bytes) }

    // everything that occurs in here, is before map/pdb symbols/splits are applied
    pub fn process(&mut self) -> Result<ObjInfo> {
        let obj_file = PeFile32::parse(&*self.exe_bytes).expect("Failed to parse object file");

        let mut sections: Vec<ObjSection> = vec![];
        let mut embsec_counter = 0;
        for section in obj_file.sections() {
            log::debug!("PE section {}: 0x{:X}", section.name()?, section.address());
            let section_name = if section.name()? == ".embsec_" {
                embsec_counter += 1;
                format!(".embsec{}", embsec_counter - 1).to_string()
            } else {
                section.name()?.to_string()
            };
            let section_kind = match section.kind() {
                SectionKind::Text => ObjSectionKind::Code,
                SectionKind::Data => ObjSectionKind::Data,
                SectionKind::ReadOnlyData => ObjSectionKind::ReadOnlyData,
                SectionKind::UninitializedData => ObjSectionKind::Bss,
                _ => ObjSectionKind::Data,
            };
            // because some exes like to give us data whose size < the virtual size
            let mut section_data = section.uncompressed_data()?.to_vec();
            section_data.resize(section.size() as usize, 0);
            // should we do anything with section.flags()? xex uses COFF
            sections.push(ObjSection {
                name: section_name,
                kind: section_kind,
                address: section.address() as u32,
                size: section.size() as u32,
                data: section_data,
                align: section.align(),
                relocations: Default::default(),
                virtual_address: None, // Loaded from section symbol
                file_offset: section.file_range().map(|(v, _)| v).unwrap_or_default(),
                splits: Default::default(),
            });
        }

        // Create object
        let mut obj =
            ObjInfo::new(ObjKind::Executable, self.exe_name.to_string(), vec![], sections);
        obj.entry = NonZeroU32::new(obj_file.entry() as u32).map(|n| n.get());

        // inspect the ImportLibraries if we have them
        if let ExeType::Xex { import_libraries: Some(imports) } = &self.exe_type {
            let mut num_imps = 0;
            let mut num_thunks = 0;
            let mut min_imp_addr: Option<u32> = None;
            let mut max_imp_addr: Option<u32> = None;
            let mut min_api_addr: Option<u32> = None;
            let mut max_api_addr: Option<u32> = None;
            let mut captured_imps: Vec<u32> = vec![];

            // to unstrip an __imp_,
            // swap the endianness of the last two bytes (so 00 01 01 90 becomes 90 01 00 00, we only care about the last two bytes)
            // then slap an 80 at the end (90 01 00 80) - the 80 tells the system that we're importing by ordinal
            fn unstrip_imp(imp: &mut [u8]) {
                imp[0] = imp[3];
                imp[1] = imp[2];
                imp[2] = 0;
                imp[3] = 0x80;
            }
            fn add_imp(
                obj: &mut ObjInfo,
                name: String,
                addr: SectionAddress,
            ) -> Result<SymbolIndex> {
                obj.add_symbol(
                    ObjSymbol {
                        name,
                        address: addr.address,
                        section: Some(addr.section),
                        size: 4,
                        size_known: true,
                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                        kind: ObjSymbolKind::Object,
                        ..Default::default()
                    },
                    false,
                )
            }
            // to unstrip a thunk,
            // you need the address of the __imp_ (i.e. __imp_XamInputGetCapabilities at 0x827103c4)
            // then add it into the first two words via an lis/addi
            // (example: XamInputGetCapabilities: 01 00 01 90 02 00 01 90 7D 69 03 A6 4E 80 04 20)
            // (change the first two words to lis/addi r11 to 0x827103c4: 3D 60 82 71 81 6B 03 C4)
            // (then it becomes: 3D 60 82 71 81 6B 03 C4 7D 69 03 A6 4E 80 04 20)
            fn unstrip_thunk(thunk: &mut [u8], imp_addr: u32) {
                thunk[0] = 0x3D;
                thunk[1] = 0x60;
                thunk[2] = ((imp_addr & 0xFF000000) >> 24) as u8;
                thunk[3] = ((imp_addr & 0xFF0000) >> 16) as u8;
                thunk[4] = 0x81;
                thunk[5] = 0x6B;
                thunk[6] = ((imp_addr & 0xFF00) >> 8) as u8;
                thunk[7] = (imp_addr & 0xFF) as u8;
            }
            fn add_thunk(
                obj: &mut ObjInfo,
                name: String,
                addr: SectionAddress,
            ) -> Result<SymbolIndex> {
                obj.known_functions.insert(addr, Some(0x10));
                obj.add_symbol(
                    ObjSymbol {
                        name,
                        address: addr.address,
                        section: Some(addr.section),
                        size: 0x10,
                        size_known: true,
                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                        kind: ObjSymbolKind::Function,
                        ..Default::default()
                    },
                    false,
                )
            }

            // now, process them (add funcs/symbols and unstrip)
            for lib in imports.iter() {
                // println!("Imports for {}:", lib.name);
                for func in lib.functions.iter() {
                    // println!("  Func: addr 0x{:08X}, ordinal 0x{:04X}, thunk 0x{:08X}", func.address, func.ordinal, func.thunk);
                    assert_ne!(func.address, 0, "Should not have an empty import func address!");
                    min_imp_addr = Some(min_imp_addr.unwrap_or(func.address).min(func.address));
                    max_imp_addr = Some(max_imp_addr.unwrap_or(func.address).max(func.address));

                    let (sec_idx, sec) = obj.sections.at_address_mut(func.address)?;
                    let lookup_name = replace_ordinal(&lib.name, func.ordinal as usize);
                    let sym_name = format!("__imp_{}", lookup_name);

                    let offset_within_sec: usize = func.address as usize - sec.address as usize;
                    unstrip_imp(&mut sec.data[offset_within_sec..offset_within_sec + 4]);
                    // println!("  Adding symbol {} at 0x{:08X}", sym_name, func.address);
                    add_imp(&mut obj, sym_name, SectionAddress::new(sec_idx, func.address))?;
                    captured_imps.push(func.address);
                    num_imps += 1;

                    if func.thunk != 0 {
                        min_api_addr = Some(min_api_addr.unwrap_or(func.thunk).min(func.thunk));
                        max_api_addr = Some(max_api_addr.unwrap_or(func.thunk).max(func.thunk));
                        // println!("thunk at 0x{:08X}", func.thunk);
                        // create a symbol/func for the thunk - will always be size 0x10
                        let (thunk_idx, thunk_sec) = obj.sections.at_address_mut(func.thunk)?;
                        let offset_within_sec: usize =
                            func.thunk as usize - thunk_sec.address as usize;
                        unstrip_thunk(
                            &mut thunk_sec.data[offset_within_sec..offset_within_sec + 8],
                            func.address,
                        );
                        // println!("  Adding symbol {} at 0x{:08X}", lookup_name, func.thunk);
                        add_thunk(
                            &mut obj,
                            lookup_name,
                            SectionAddress::new(thunk_idx, func.thunk),
                        )?;
                        num_thunks += 1;
                    }
                }
            }

            // for SOME reason, microsoft can have imports/thunks that aren't referenced in the import libraries
            // but can be referenced in xidata later on
            // so, this block of code serves to search for and capture them
            if let (Some(min_addr), Some(max_addr)) = (min_imp_addr, max_imp_addr) {
                // i had to write things this way because of how rust handles borrowing...thank you rust, very cool
                let (import_idx, offset_within_sec) = {
                    let (idx, sec) = obj.sections.at_address(min_addr)?;
                    (idx, (min_addr - sec.address) as usize)
                };
                let mut i = min_addr;
                loop {
                    let data_idx = offset_within_sec + (i - min_addr) as usize;
                    let cur_imp = {
                        let sec = &obj.sections[import_idx];
                        if data_idx >= sec.data.len() {
                            break;
                        }
                        read_word(&sec.data, data_idx)
                    };
                    if i > max_addr && cur_imp == 0 {
                        break;
                    }

                    if cur_imp != 0 && !captured_imps.contains(&i) {
                        let sym_name = format!(
                            "__imp_{}",
                            replace_ordinal(
                                &imports[((cur_imp & 0x00FF0000) >> 16) as usize].name,
                                (cur_imp & 0xFFFF) as usize
                            )
                        );
                        // println!("Found missing imp {} at 0x{:08X}", sym_name, i);
                        {
                            // obj borrowing scope moment
                            let sec = &mut obj.sections[import_idx];
                            unstrip_imp(&mut sec.data[data_idx..data_idx + 4]);
                        }
                        add_imp(&mut obj, sym_name, SectionAddress::new(import_idx, i))?;
                        num_imps += 1;
                    }

                    i += 4;
                }
            }
            if let (Some(min_addr), Some(max_addr)) = (min_api_addr, max_api_addr) {
                // i had to write things this way because of how rust handles borrowing...thank you rust, very cool
                let (thunk_idx, offset_within_sec) = {
                    let (idx, sec) = obj.sections.at_address(min_addr)?;
                    (idx, (min_addr - sec.address) as usize)
                };

                let mut i = min_addr;
                loop {
                    let data_idx = offset_within_sec + (i - min_addr) as usize;
                    let cur_thunk = {
                        let sec = &obj.sections[thunk_idx];
                        if data_idx >= sec.data.len() {
                            break;
                        }
                        read_word(&sec.data, data_idx)
                    };
                    if i > max_addr && cur_thunk == 0 {
                        break;
                    } else if i < max_addr && cur_thunk == 0 {
                        i += 4;
                        continue;
                    }

                    if cur_thunk != 0 {
                        let cur_addr = SectionAddress::new(thunk_idx, i);
                        if !obj.known_functions.contains_key(&cur_addr) {
                            let sym_name = replace_ordinal(
                                &imports[((cur_thunk & 0x00FF0000) >> 16) as usize].name,
                                (cur_thunk & 0xFFFF) as usize,
                            );
                            // println!("Found missing thunk {} at 0x{:08X}", sym_name, i);
                            if let Some((_, imp_sym)) =
                                obj.symbols.by_name(&format!("__imp_{}", sym_name))?
                            {
                                // println!("found sym {}", maybe_imp_sym.unwrap().1.name);
                                unstrip_thunk(
                                    &mut obj.sections[thunk_idx].data[data_idx..data_idx + 8],
                                    imp_sym.address,
                                );
                            }
                            add_thunk(&mut obj, sym_name, cur_addr)?;
                            num_thunks += 1;
                        }
                    }
                    i += 0x10;
                }
            }
            log::info!(
                "Found {} imps and {} import thunks from import data!",
                num_imps,
                num_thunks
            );
        }

        // you would be amazed just how much we can infer from an Xbox 360 exe before CFA can even begin
        process_seh(&mut obj)?;
        process_xidata(&mut obj)?;

        // process the entrypoint
        if let Some(entry) = obj.entry {
            // label entry as mainCRTStartup
            obj.add_symbol(
                ObjSymbol {
                    name: String::from("mainCRTStartup"),
                    address: entry,
                    section: Some(obj.sections.at_address(entry)?.0),
                    size_known: false,
                    flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                    kind: ObjSymbolKind::Function,
                    ..Default::default()
                },
                false,
            )?;
            // traverse through entrypoint's call chain
            if apply_signature(&mut obj, "entry")? && apply_signature(&mut obj, "post-entry")? {
                process_crt(&mut obj)?;
            }
        }

        process_rtti(&mut obj)?;

        const RTL_CHECK_STACK: &str = "fYMA0H1sANA4Cw//fABmcUyBACB8Kwt4fAkDpoQL8ABCAP/8ToAAIA==";
        let rtl_bytes = STANDARD.decode(RTL_CHECK_STACK)?;

        let mut api_syms: Vec<ObjSymbol> = vec![];
        for (section_index, section) in obj.sections.by_kind(ObjSectionKind::Code) {
            let Some(pos) = memmem::find(&section.data, &rtl_bytes) else {
                continue;
            };
            let start = SectionAddress::new(section_index, section.address + pos as u32);
            api_syms.push(ObjSymbol {
                name: String::from("_RtlCheckStack"),
                address: start.address,
                section: Some(start.section),
                size: 4,
                size_known: true,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Function,
                ..Default::default()
            });
            api_syms.push(ObjSymbol {
                name: String::from("_RtlCheckStack12"),
                address: start.address + 4,
                section: Some(start.section),
                size: 36,
                size_known: true,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Function,
                ..Default::default()
            });
        }
        for sym in api_syms {
            obj.add_symbol(sym, false)?;
        }

        // TODO: mark subsections within sections, so that in splits.txt they're renamed as such

        // .rdata subsections:
        // -.idata$5: __imps
        // -.rdata: the regular ole .rdata we all know and love
        // -.rdata$r: RTTI structures
        // -.xdata: C exception scope table infos
        // -.xdata$x: throw infos

        // .text subsections:
        // -.text: the regular ole .text we all know and love
        // -.text$yc: static ctors - supposedly get this from CRT, but the first entry in __xc_a isn't always in yc (security init cookie)
        //      -first entry is either security init cookie, or the first func in yc
        // -.text$yd: static dtors - after the last entry in __xc_a
        // -.xidata: xdk imports (the ones we add/unstrip when we first process the exe)
        // -.xedata: currently unknown

        // .data subsections:
        // -.CRT: C runtime info
        // some NUI thing
        // -.data: the regular ole .data we all know and love
        // bss is contained somewhere in .data but i don't know how to get the start of it at this time

        // .XBMOVIE: matches up with ground truth...but it's mostly a sea of 0's
        // .idata: partially zero'ed out and offsetted from ground truth in debug, completely gone from release
        //      xidata/its relevant info seems to be covered, making idata a non-issue...i guess?
        // .XBLD: zero'ed out in debug, completely gone from release
        // .reloc: zero'ed out regardless

        Ok(obj)
    }
}

fn process_xidata(obj: &mut ObjInfo) -> Result<()> {
    // if this xex has an explicit .xidata section (most exes i've seen have .xidata as a subection of .text), mark down the funcs in there
    if let Some((xidata_idx, xidata_sec)) = obj.sections.by_name(".xidata")? {
        let mut num_xidatas = 0;
        for (i, chunk) in xidata_sec.data.chunks_exact(16).enumerate() {
            if i == 0 {
                continue;
            } // the first entry appears to be all 0's...but is every xidata like this?
            let inst1 = u32::from_be_bytes(chunk[0..4].try_into()?);
            // if we've reached 0's, that's the end of usable xidata info
            if inst1 == 0 {
                break;
            }

            assert_eq!(inst1 & 0xFFFF0000, 0x3D600000, "First instruction MUST be an lis to r11!");
            let inst2 = u32::from_be_bytes(chunk[4..8].try_into()?);
            assert_eq!(
                inst2 & 0xFFFF0000,
                0x396B0000,
                "Second instruction MUST be an addi to r11!"
            );
            assert_eq!(
                u32::from_be_bytes(chunk[8..12].try_into()?),
                0x7d6903a6,
                "Third instruction MUST be mtspr CTR, r11!"
            );
            assert_eq!(
                u32::from_be_bytes(chunk[12..16].try_into()?),
                0x4e800420,
                "Fourth and final instruction MUST be bctr!"
            );

            let func_addr = (xidata_sec.address as usize + (i * 16)) as u32;
            // println!("This xidata func's address: 0x{:08X}", func_addr);
            obj.known_functions.insert(SectionAddress::new(xidata_idx, func_addr), Some(0x10));
            num_xidatas += 1;
        }
        log::info!("Found {} known funcs from xidata!", num_xidatas);
    }
    Ok(())
}

fn process_crt(obj: &mut ObjInfo) -> Result<()> {
    let data_sec_idx = obj.sections.by_name(".data")?.expect("where data").0;

    // xri - runtime initializers?
    let (xri_start, xri_end) = {
        let (xria_sym_idx, xria_sym) =
            obj.symbols.by_name("__xri_a")?.expect("we should've found __xri_a at this point!");
        let xriz_sym =
            obj.symbols.by_name("__xri_z")?.expect("we should've found __xri_z at this point!").1;
        let xri_start = xria_sym.address;
        let xri_end = xriz_sym.address;
        let mut new_sym = xria_sym.clone();
        new_sym.size = xri_end - xri_start;
        new_sym.size_known = true;
        obj.symbols.replace(xria_sym_idx, new_sym)?;
        (xri_start, xri_end)
    };

    for addr in (xri_start..xri_end).step_by(4) {
        match addr - xri_start {
            0 => {
                // first entry of xri_a - must be 0
                ensure!(read_u32(&obj.sections[data_sec_idx], addr).unwrap() == 0, "bad __xri_a!");
            }
            4 => {
                // second entry of xri_a - must be __onexitinit
                let exitinit_addr = {
                    let addr = read_u32(&obj.sections[data_sec_idx], addr).unwrap();
                    SectionAddress::new(obj.sections.at_address(addr)?.0, addr)
                };
                obj.add_symbol(
                    ObjSymbol {
                        name: String::from("__onexitinit"),
                        address: exitinit_addr.address,
                        section: Some(exitinit_addr.section),
                        size: {
                            let Some(Normal { end }) = obj.pdata_funcs.get(&exitinit_addr) else {
                                panic!("__onexitinit should be a Normal pdata type!")
                            };
                            end.address - exitinit_addr.address
                        },
                        size_known: true,
                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                        kind: ObjSymbolKind::Function,
                        ..Default::default()
                    },
                    false,
                )?;
            }
            8 => {
                // third entry of xri_a - must be _ioinit
                let ioinit_addr = {
                    let addr = read_u32(&obj.sections[data_sec_idx], addr).unwrap();
                    SectionAddress::new(obj.sections.at_address(addr)?.0, addr)
                };
                obj.add_symbol(
                    ObjSymbol {
                        name: String::from("_ioinit"),
                        address: ioinit_addr.address,
                        section: Some(ioinit_addr.section),
                        size: {
                            let Some(Normal { end }) = obj.pdata_funcs.get(&ioinit_addr) else {
                                panic!("_ioinit should be a Normal pdata type!")
                            };
                            end.address - ioinit_addr.address
                        },
                        size_known: true,
                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                        kind: ObjSymbolKind::Function,
                        ..Default::default()
                    },
                    false,
                )?;
                let pioinit_addr = SectionAddress::new(data_sec_idx, addr);
                obj.add_symbol(
                    ObjSymbol {
                        name: String::from("__pioinit"),
                        address: pioinit_addr.address,
                        section: Some(pioinit_addr.section),
                        size: 4,
                        size_known: true,
                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                        kind: ObjSymbolKind::Object,
                        ..Default::default()
                    },
                    false,
                )?;
            }
            _ => {
                // any further entries are unknown to us, except for the fact they're functions
                let func_addr = {
                    let addr = read_u32(&obj.sections[data_sec_idx], addr).unwrap();
                    SectionAddress::new(obj.sections.at_address(addr)?.0, addr)
                };
                obj.known_functions.entry(func_addr).or_default();
            }
        }
    }

    // xc - static constructors
    let (xc_start, xc_end) = {
        let (xca_sym_idx, xca_sym) =
            obj.symbols.by_name("__xc_a")?.expect("we should've found __xc_a at this point!");
        let xcz_sym =
            obj.symbols.by_name("__xc_z")?.expect("we should've found __xc_z at this point!").1;
        let xc_start = xca_sym.address;
        let xc_end = xcz_sym.address;
        let mut new_sym = xca_sym.clone();
        new_sym.size = xc_end - xc_start;
        new_sym.size_known = true;
        obj.symbols.replace(xca_sym_idx, new_sym)?;
        (xc_start, xc_end)
    };

    let mut num_sinits = 0;
    for addr in (xc_start..xc_end).step_by(4) {
        let sinit_addr = read_u32(&obj.sections[data_sec_idx], addr).unwrap();
        if sinit_addr != 0 {
            let sinit_sec_addr =
                SectionAddress::new(obj.sections.at_address(sinit_addr)?.0, sinit_addr);
            obj.known_functions.entry(sinit_sec_addr).or_default();
            num_sinits += 1;
        }
    }
    log::info!("Found {} known static initializer funcs!", num_sinits);

    let (xi_start, xi_end) = {
        let (xia_sym_idx, xia_sym) =
            obj.symbols.by_name("__xi_a")?.expect("we should've found __xi_a at this point!");
        let xiz_sym =
            obj.symbols.by_name("__xi_z")?.expect("we should've found __xi_z at this point!").1;
        let xi_start = xia_sym.address;
        let xi_end = xiz_sym.address;
        let mut new_sym = xia_sym.clone();
        new_sym.size = xi_end - xi_start;
        new_sym.size_known = true;
        obj.symbols.replace(xia_sym_idx, new_sym)?;
        (xi_start, xi_end)
    };

    // TODO adjust the logic of this loop to match xri, namely other funcs than __initstdio and __initmbctable
    for addr in (xi_start..xi_end).step_by(4) {
        let cur_addr = read_u32(&obj.sections[data_sec_idx], addr).unwrap();
        if cur_addr != 0 {
            let cur_sec_addr = SectionAddress::new(obj.sections.at_address(cur_addr)?.0, cur_addr);
            obj.known_functions.entry(cur_sec_addr).or_default();
        }
    }

    let (xp_start, xp_end) = {
        let (xpa_sym_idx, xpa_sym) =
            obj.symbols.by_name("__xp_a")?.expect("we should've found __xp_a at this point!");
        let xpz_sym =
            obj.symbols.by_name("__xp_z")?.expect("we should've found __xp_z at this point!").1;
        let xp_start = xpa_sym.address;
        let xp_end = xpz_sym.address;
        let mut new_sym = xpa_sym.clone();
        new_sym.size = xp_end - xp_start;
        new_sym.size_known = true;
        obj.symbols.replace(xpa_sym_idx, new_sym)?;
        (xp_start, xp_end)
    };
    for addr in (xp_start..xp_end).step_by(4) {
        let cur_addr = read_u32(&obj.sections[data_sec_idx], addr).unwrap();
        if cur_addr != 0 {
            let cur_sec_addr = SectionAddress::new(obj.sections.at_address(cur_addr)?.0, cur_addr);
            obj.known_functions.entry(cur_sec_addr).or_default();
        }
    }

    let (xt_start, xt_end) = {
        let (xta_sym_idx, xta_sym) =
            obj.symbols.by_name("__xt_a")?.expect("we should've found __xt_a at this point!");
        let xtz_sym =
            obj.symbols.by_name("__xt_z")?.expect("we should've found __xt_z at this point!").1;
        let xt_start = xta_sym.address;
        let xt_end = xtz_sym.address;
        let mut new_sym = xta_sym.clone();
        new_sym.size = xt_end - xt_start;
        new_sym.size_known = true;
        obj.symbols.replace(xta_sym_idx, new_sym)?;
        (xt_start, xt_end)
    };
    for addr in (xt_start..xt_end).step_by(4) {
        let cur_addr = read_u32(&obj.sections[data_sec_idx], addr).unwrap();
        if cur_addr != 0 {
            let cur_sec_addr = SectionAddress::new(obj.sections.at_address(cur_addr)?.0, cur_addr);
            obj.known_functions.entry(cur_sec_addr).or_default();
        }
    }

    Ok(())
}
