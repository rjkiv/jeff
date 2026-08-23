use std::{fs, fs::File, io::Read, num::NonZeroU32};

use anyhow::{Result, bail, ensure};
use base64::{Engine, engine::general_purpose::STANDARD};
use memchr::memmem;
use object::{Object, ObjectSection, SectionKind, read::pe::PeFile32};
use typed_path::Utf8NativePathBuf;

use crate::{
    analysis::{cfa::SectionAddress, rtti::process_rtti, seh::process_seh},
    obj::{
        ObjInfo, ObjKind, ObjSection, ObjSectionKind, ObjSplit, ObjSymbol, ObjSymbolFlagSet,
        ObjSymbolFlags, ObjSymbolKind, ObjUnit, SymbolIndex,
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
    Xex {
        import_libraries: Option<Vec<ImportLibrary>>,
    },
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
            ensure!(
                file.metadata()?.len() >= 4,
                "File too small to be a valid executable"
            );
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
                exe_name: base_path
                    .file_name()
                    .expect("Missing executable name!")
                    .to_string(),
                exe_bytes: fs::read(base_path)?,
                exe_type: ExeType::Exe,
            })
        } else {
            bail!("Unrecognized executable type!");
        }
    }

    pub fn is_xex(&self) -> bool {
        matches!(
            self.exe_type,
            ExeType::Xex {
                import_libraries: _
            }
        )
    }

    pub fn extract(&self) -> (String, &Vec<u8>) {
        (self.exe_name.clone(), &self.exe_bytes)
    }

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

            // NOTE: to calculate bss start within .data, do virtual address + size of raw data

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
        let mut obj = ObjInfo::new(
            ObjKind::Executable,
            self.exe_name.to_string(),
            vec![],
            sections,
        );
        obj.entry = NonZeroU32::new(obj_file.entry() as u32).map(|n| n.get());

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
        }

        // inspect the ImportLibraries if we have them
        if let ExeType::Xex {
            import_libraries: Some(imports),
        } = &self.exe_type
        {
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
                let (b2, b3) = (imp[2], imp[3]);
                imp[0..4].copy_from_slice(&[b3, b2, 0, 0x80]);
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
                let [b0, b1, b2, b3] = imp_addr.to_be_bytes();
                thunk[0..8].copy_from_slice(&[0x3D, 0x60, b0, b1, 0x81, 0x6B, b2, b3]);
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
                    assert_ne!(
                        func.address, 0,
                        "Should not have an empty import func address!"
                    );
                    min_imp_addr = Some(min_imp_addr.unwrap_or(func.address).min(func.address));
                    max_imp_addr = Some(max_imp_addr.unwrap_or(func.address).max(func.address));

                    let (sec_idx, sec) = obj.sections.at_address_mut(func.address)?;
                    let lookup_name = replace_ordinal(&lib.name, func.ordinal as usize);
                    let sym_name = format!("__imp_{}", lookup_name);

                    let offset_within_sec: usize = func.address as usize - sec.address as usize;
                    unstrip_imp(&mut sec.data[offset_within_sec..offset_within_sec + 4]);
                    // println!("  Adding symbol {} at 0x{:08X}", sym_name, func.address);
                    add_imp(
                        &mut obj,
                        sym_name,
                        SectionAddress::new(sec_idx, func.address),
                    )?;
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
        process_xidata(&mut obj)?; // needs to be done before SEH, because of the possibility of having a thunk to the C handler
        process_seh(&mut obj)?;
        process_rtti(&mut obj)?;
        process_reg_intrinsics(&mut obj)?;

        const RTL_CHECK_STACK: &str = "fYMA0H1sANA4Cw//fABmcUyBACB8Kwt4fAkDpoQL8ABCAP/8ToAAIA==";
        let rtl_check_stack_addr = find_func_addr(&obj, RTL_CHECK_STACK)?;
        obj.symbols.add(
            ObjSymbol {
                name: String::from("_RtlCheckStack"),
                address: rtl_check_stack_addr.address,
                section: Some(rtl_check_stack_addr.section),
                size: 0x28,
                size_known: true,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: ObjSymbolKind::Function,
                ..Default::default()
            },
            false,
        )?;
        obj.symbols.add(
            ObjSymbol {
                name: String::from("_RtlCheckStack12"),
                address: rtl_check_stack_addr.address + 4,
                section: Some(rtl_check_stack_addr.section),
                size_known: true,
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                ..Default::default()
            },
            false,
        )?;
        obj.link_order.push(ObjUnit {
            name: String::from("xdk/LIBCMT/chkstk.cpp"),
            autogenerated: false,
            order: None,
        });
        obj.add_split(
            rtl_check_stack_addr.section,
            rtl_check_stack_addr.address,
            ObjSplit {
                unit: String::from("xdk/LIBCMT/chkstk.cpp"),
                end: rtl_check_stack_addr.address + 0x28,
                align: None,
                ..Default::default()
            },
        )?;

        // NOTE: if the exe has a physical .xidata section:
        // imps will be in .idata, and thunks will be in the lower part of .xidata
        // otherwise, imps will be at the start of .rdata (.idata$5 subsection),
        // and thunks will be in .text, after all the functions (.text, then .xidata subsection)

        // .XBMOVIE: matches up with ground truth...but it's mostly a sea of 0's
        // .idata: partially zero'ed out and offsetted from ground truth in debug, completely gone from release
        //      xidata/its relevant info seems to be covered, making idata a non-issue...i guess?
        // .XBLD: zero'ed out in debug, completely gone from release
        // .reloc: zero'ed out regardless

        Ok(obj)
    }
}

fn process_reg_intrinsics(obj: &mut ObjInfo) -> Result<()> {
    // first 8 bytes, full func name, full func size, label name start, label start, label end, step size, and an optional split name/size
    #[rustfmt::skip]
    const SLEDS_XBOX: [([u8; 8], &str, Option<u32>, &str, u32, u32, u32, Option<(&str, u32)>); 8] = [
        ([0xf9, 0xc1, 0xff, 0x68, 0xf9, 0xe1, 0xff, 0x70], "__savegprlr", Some(0x50), "__savegprlr_", 14, 32, 4, Some(("xdk/LIBCMT/crtgpr.cpp", 0xB0))),
        ([0xe9, 0xc1, 0xff, 0x68, 0xe9, 0xe1, 0xff, 0x70], "__restgprlr", Some(0x54), "__restgprlr_", 14, 32, 4, None),
        ([0xd9, 0xcc, 0xff, 0x70, 0xd9, 0xec, 0xff, 0x78], "__savefpr", Some(0x4C), "__savefpr_", 14, 32, 4, Some(("xdk/LIBCMT/crtfpr.cpp", 0x98))),
        ([0xc9, 0xcc, 0xff, 0x70, 0xc9, 0xec, 0xff, 0x78], "__restfpr",  Some(0x4C),"__restfpr_", 14, 32, 4, None),
        ([0x39, 0x60, 0xfe, 0xe0, 0x7d, 0xcb, 0x61, 0xce], "__savevmx", Some(0x298), "__savevmx_", 14, 32, 8, Some(("xdk/LIBCMT/crtvmx.cpp", 0x530))),
        ([0x39, 0x60, 0xfc, 0x00, 0x10, 0x0b, 0x61, 0xcb], "__savevmx_upper", None, "__savevmx_", 64, 128, 8, None),
        ([0x39, 0x60, 0xfe, 0xe0, 0x7d, 0xcb, 0x60, 0xce], "__restvmx", Some(0x298), "__restvmx_", 14, 32, 8, None),
        ([0x39, 0x60, 0xfc, 0x00, 0x10, 0x0b, 0x60, 0xcb], "__restvmx_upper", None, "__restvmx_", 64, 128, 8, None),
    ];

    let mut splits: Vec<(&str, SectionAddress, u32)> = Vec::new();

    let (text_idx, text_section) = obj.sections.by_name(".text")?.expect("no text?");
    for (needle, func, func_size, label, reg_start, reg_end, step_size, split_info) in SLEDS_XBOX {
        let Some(pos) = memmem::find(&text_section.data, &needle) else {
            panic!("No reg intrinsic?");
        };
        let start = SectionAddress::new(text_idx, text_section.address + pos as u32);
        log::debug!("Found {} @ {:#010X}", func, start);

        // add function for main reg intrinsic if applicable
        if let Some(func_size) = func_size {
            obj.symbols.add(
                ObjSymbol {
                    name: String::from(func),
                    address: start.address,
                    section: Some(start.section),
                    size: func_size,
                    size_known: true,
                    flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                    kind: ObjSymbolKind::Function,
                    ..Default::default()
                },
                false,
            )?;
        }
        // add number labels
        for i in reg_start..reg_end {
            let addr = start + (i - reg_start) * step_size;
            obj.symbols.add(
                ObjSymbol {
                    name: format!("{label}{i}"),
                    address: addr.address,
                    section: Some(addr.section),
                    size_known: true,
                    flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                    ..Default::default()
                },
                false,
            )?;
        }
        // if split, add it
        if let Some((split_name, split_size)) = split_info {
            splits.push((split_name, start, split_size));
        }
    }

    for (split_name, start, split_size) in splits {
        obj.link_order.push(ObjUnit {
            name: String::from(split_name),
            autogenerated: false,
            order: None,
        });
        obj.add_split(
            start.section,
            start.address,
            ObjSplit {
                unit: String::from(split_name),
                end: start.address + split_size,
                align: None,
                ..Default::default()
            },
        )?;
    }

    Ok(())
}

fn find_func_addr(obj: &ObjInfo, func_bytes: &str) -> Result<SectionAddress> {
    let func_bytes_decoded = STANDARD.decode(func_bytes)?;
    let (text_idx, text_section) = obj.sections.by_name(".text")?.expect("no text?");
    if let Some(pos) = memmem::find(&text_section.data, &func_bytes_decoded) {
        Ok(SectionAddress::new(
            text_idx,
            text_section.address + pos as u32,
        ))
    } else {
        panic!("Function not found in .text!");
    }
}

fn process_xidata(obj: &mut ObjInfo) -> Result<()> {
    // if this xex has an .xidata section, mark down the funcs in there
    if let Some((xidata_idx, xidata_sec)) = obj.sections.by_name(".xidata")? {
        let mut num_xidatas = 0;
        for (i, chunk) in xidata_sec.data.as_chunks::<16>().0.iter().enumerate() {
            if i == 0 {
                continue;
            } // the first entry appears to be all 0's...but is every xidata like this?
            let inst1 = u32::from_be_bytes(chunk[0..4].try_into()?);
            // if we've reached 0's, that's the end of usable xidata info
            if inst1 == 0 {
                break;
            }

            assert_eq!(
                inst1 & 0xFFFF0000,
                0x3D600000,
                "First instruction MUST be an lis to r11!"
            );
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
            obj.known_functions
                .insert(SectionAddress::new(xidata_idx, func_addr), Some(0x10));
            num_xidatas += 1;
        }
        log::info!("Found {} known funcs from xidata!", num_xidatas);
    }
    Ok(())
}
