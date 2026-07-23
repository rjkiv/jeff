use std::{borrow::Cow, cmp::min, collections::BTreeMap, fs};

use anyhow::{bail, ensure, Result};
use lzxd::Lzxd;
use object::{
    endian,
    read::pe::PeFile32,
    write::{SectionId, SymbolId},
    Architecture, BinaryFormat, Endianness, RelocationFlags, SectionKind, SymbolFlags, SymbolKind,
    SymbolScope,
};
use typed_path::{Utf8NativePathBuf, Utf8UnixPath};

use crate::{
    obj::{
        ObjInfo, ObjRelocKind, ObjSectionKind, ObjSymbolKind, ObjSymbolScope, SectionIndex,
        SymbolIndex,
    },
    util::{
        crypto::decrypt_aes128_cbc_no_padding,
        read::read_word,
        xex_optional_headers::{
            parse_xex_optional_headers, BaseFileFormat, XexCompression, XexOptionalHeader,
        },
    },
};
// ----------------------------------------------------------------------
// XEXHEADER
// ----------------------------------------------------------------------

// header documentation: https://free60.org/System-Software/Formats/XEX/
pub struct XexHeader {
    // magic u32 here - must be "XEX2"
    pub module_flags: u32,
    pub pe_offset: u32,
    // reserved u32 here, but it goes unused so who cares
    pub security_info_offset: u32,
}

impl XexHeader {
    fn parse(data: &[u8]) -> Result<Self> {
        let magic = read_word(data, 0);
        ensure!(magic == 0x58455832, "XEX2 magic header not found!");
        let module_flags = read_word(data, 4);
        let pe_offset = read_word(data, 8);
        // reserved is at data index 12, but it's unused so who cares
        let security_info_offset = read_word(data, 16);
        Ok(Self { module_flags, pe_offset, security_info_offset })
    }
}

// ----------------------------------------------------------------------
// XEXLOADERINFO
// ----------------------------------------------------------------------

pub struct XexLoaderInfo {
    pub header_size: u32,
    pub image_size: u32,
    pub rsa_signature: [u8; 256],
    pub unknown: u32,
    pub image_flags: u32,
    pub load_address: u32,
    pub section_digest: [u8; 20],
    pub import_table_count: u32,
    pub import_table_digest: [u8; 20],
    pub media_id: [u8; 16],
    pub file_key: [u8; 16],
    pub export_table: u32,
    pub header_digest: [u8; 20],
    pub game_regions: u32,
    pub media_flags: u32,
}

impl XexLoaderInfo {
    fn parse(data: &[u8], security_offset: u32) -> Result<Self> {
        let mut pos = security_offset as usize;
        let header_size = read_word(data, pos);
        let image_size = read_word(data, pos + 4);
        pos += 8;
        let rsa_signature = data[pos..pos + 256].try_into()?;
        pos += 256;
        let unknown = read_word(data, pos);
        let image_flags = read_word(data, pos + 4);
        let load_address = read_word(data, pos + 8);
        pos += 12;
        let section_digest = data[pos..pos + 20].try_into()?;
        pos += 20;
        let import_table_count = read_word(data, pos);
        pos += 4;
        let import_table_digest = data[pos..pos + 20].try_into()?;
        pos += 20;
        let media_id = data[pos..pos + 16].try_into()?;
        pos += 16;
        let file_key = data[pos..pos + 16].try_into()?;
        pos += 16;
        let export_table = read_word(data, pos);
        pos += 4;
        let header_digest = data[pos..pos + 20].try_into()?;
        pos += 20;
        let game_regions = read_word(data, pos);
        let media_flags = read_word(data, pos + 4);
        Ok(Self {
            header_size,
            image_size,
            rsa_signature,
            unknown,
            image_flags,
            load_address,
            section_digest,
            import_table_count,
            import_table_digest,
            media_id,
            file_key,
            export_table,
            header_digest,
            game_regions,
            media_flags,
        })
    }
}

// ----------------------------------------------------------------------
// XEXSESSIONKEYS
// ----------------------------------------------------------------------
const RETAIL_KEY: [u8; 16] = [
    0x20, 0xB1, 0x85, 0xA5, 0x9D, 0x28, 0xFD, 0xC3, 0x40, 0x58, 0x3F, 0xBB, 0x08, 0x96, 0xBF, 0x91,
];
const DEVKIT_KEY: [u8; 16] = [
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
];

// ----------------------------------------------------------------------
// XEXINFO
// ----------------------------------------------------------------------

pub struct XexInfo {
    pub header: XexHeader,
    pub optional_headers: Vec<XexOptionalHeader>,
    pub loader_info: XexLoaderInfo,
    pub session_key: [u8; 16],
    pub is_dev_kit: bool,
    pub exe_bytes: Vec<u8>,
}

impl XexInfo {
    pub fn from_files(
        base_path: &Utf8NativePathBuf,
        patch_path: Option<Utf8NativePathBuf>,
    ) -> Result<Self> {
        let base_data = fs::read(base_path.to_path_buf()).expect("Failed to read file");

        if let Some(_patch_path) = patch_path {
            // this is where you apply the patch xexp on top of the base xex, resulting in a new data Vec<u8> to process
            // see apply_patch below
        }

        let xex_header = XexHeader::parse(&base_data)?;
        let xex_optional_headers = parse_xex_optional_headers(&base_data)?;
        let xex_loader_info = XexLoaderInfo::parse(&base_data, xex_header.security_info_offset)?;

        let retail_key: [u8; 16] =
            decrypt_aes128_cbc_no_padding(&RETAIL_KEY, &xex_loader_info.file_key)?
                .try_into()
                .expect("Failed to deduce a retail key!");

        let devkit_key: [u8; 16] =
            decrypt_aes128_cbc_no_padding(&DEVKIT_KEY, &xex_loader_info.file_key)?
                .try_into()
                .expect("Failed to deduce a devkit key!");

        let confirmed_session_key: [u8; 16];
        let is_dev_kit: bool;
        let exe_bytes: Vec<u8>;

        // this is where we'd parse xexsection related info...but it might not be needed?

        let pe_vec = &base_data[xex_header.pe_offset as usize..base_data.len()].to_vec();

        let Some(bff) = xex_optional_headers.iter().find_map(|h| match h {
            XexOptionalHeader::BaseFileFormat { format } => Some(format),
            _ => None,
        }) else {
            panic!("We need to have a BaseFileFormat at this point!")
        };

        let try_get_exe = |key| {
            let exe_bytes = XexInfo::decompress(pe_vec, &key, bff, xex_loader_info.image_size)?;
            ensure!(exe_bytes.starts_with(b"MZ"));
            Ok(exe_bytes)
        };

        if let Ok(exe_bytes_retail) = try_get_exe(retail_key) {
            confirmed_session_key = retail_key;
            is_dev_kit = false;
            exe_bytes = exe_bytes_retail;
        } else if let Ok(exe_bytes_devkit) = try_get_exe(devkit_key) {
            confirmed_session_key = devkit_key;
            is_dev_kit = true;
            exe_bytes = exe_bytes_devkit;
        } else {
            bail!("Could not deduce exe type!");
        }

        let pe_file_finalized = XexInfo::finalize_exe(&exe_bytes);

        Ok(Self {
            header: xex_header,
            optional_headers: xex_optional_headers,
            loader_info: xex_loader_info,
            session_key: confirmed_session_key,
            is_dev_kit,
            exe_bytes: pe_file_finalized,
        })
    }

    fn decompress(
        input: &[u8],
        session_key: &[u8; 16],
        bff: &BaseFileFormat,
        img_size: u32,
    ) -> Result<Vec<u8>> {
        let compressed: Cow<[u8]> = match bff.encrypted {
            false => Cow::Borrowed(input),
            true => Cow::Owned(decrypt_aes128_cbc_no_padding(session_key, input)?),
        };

        let mut output_bytes: Vec<u8> = vec![0; img_size as usize];
        let mut pos_in: usize = 0;
        let mut pos_out: usize = 0;

        match &bff.compression {
            XexCompression::None => {
                output_bytes = compressed.to_vec();
            }
            XexCompression::Raw { basics } => {
                for bc in basics {
                    for i in 0..(bc.data_size as usize) {
                        if pos_in + i >= compressed.len() {
                            break;
                        }
                        output_bytes[i + pos_out] = compressed[pos_in + i];
                    }
                    pos_out += (bc.data_size + bc.zero_size) as usize;
                    pos_in += bc.data_size as usize;
                }
            }
            XexCompression::Compressed { normal: comp } => {
                let window_size = comp.window_size as usize;
                let lzx_window = lzxd::WindowSize::KB32;
                let mut lzxd_state = Lzxd::new(lzx_window);
                let mut current_block_size = comp.block_size as usize;

                while current_block_size != 0 {
                    if pos_in + current_block_size > compressed.len() {
                        bail!(
                            "LZX: block needs {} bytes at 0x{:X} but only {} remain",
                            current_block_size,
                            pos_in,
                            compressed.len() - pos_in
                        );
                    }
                    let block = &compressed[pos_in..pos_in + current_block_size];
                    pos_in += current_block_size;
                    if block.len() < 24 {
                        bail!("LZX: block too small for header: {} bytes", block.len());
                    }
                    let next_block_size =
                        u32::from_be_bytes([block[0], block[1], block[2], block[3]]) as usize;
                    let mut off = 24usize;
                    while off + 2 <= block.len() {
                        let chunk_len = u16::from_be_bytes([block[off], block[off + 1]]) as usize;
                        off += 2;

                        if chunk_len == 0 {
                            break;
                        }

                        if off + chunk_len > block.len() {
                            bail!(
                                "LZX: sub-chunk at offset {} wants {} bytes but only {} remain",
                                off,
                                chunk_len,
                                block.len() - off
                            );
                        }
                        let chunk_data = &block[off..off + chunk_len];
                        off += chunk_len;
                        let expected = min(window_size, output_bytes.len().saturating_sub(pos_out));
                        if expected == 0 {
                            break;
                        }
                        let decompressed =
                            lzxd_state.decompress_next(chunk_data, expected).map_err(|e| {
                                anyhow::anyhow!(
                                    "LZX: decompress failed at pos_out=0x{:X} \
                            (chunk_len={}, expected={}, block_off={}): {:?}",
                                    pos_out,
                                    chunk_len,
                                    expected,
                                    off - chunk_len,
                                    e
                                )
                            })?;

                        if decompressed.is_empty() {
                            bail!(
                                "LZX: decompression returned zero bytes at pos_out=0x{:X}",
                                pos_out
                            );
                        }

                        let copy_len = min(decompressed.len(), output_bytes.len() - pos_out);
                        output_bytes[pos_out..pos_out + copy_len]
                            .copy_from_slice(&decompressed[..copy_len]);
                        pos_out += copy_len;
                    }
                    current_block_size = next_block_size;
                }
                if pos_out == 0 {
                    bail!("LZX: produced zero output bytes");
                }
            }
            XexCompression::DeltaCompressed { normal: _ } => {
                output_bytes = compressed.to_vec();
            }
        };
        Ok(output_bytes)
    }

    // fn apply_patch(
    //     base_path: &Utf8NativePathBuf,
    //     patch_path: &Utf8NativePathBuf,
    // ) -> Result<Vec<u8>> {
    //     // see: https://github.com/zeroKilo/XEXLoaderWV/blob/master/XEXLoaderWV/src/main/java/xexloaderwv/XEXLoaderWVLoader.java#L128
    //
    //     // Parses everything in the base xex, including the PE image
    //     let base_data = fs::read(base_path.to_path_buf()).expect("Failed to read file");
    //     let xex_header = XexHeader::parse(&base_data)?;
    //     assert_ne!(xex_header.module_flags & 1, 0, "Not a base game xex!");
    //
    //     // Parses everything in the patch xexp...up until the "PE image"
    //
    //     todo!("actually fill this function out");
    //
    //     let mut patched_xex_bytes: Vec<u8> = Vec::new();
    //     Ok(patched_xex_bytes)
    // }

    fn finalize_exe(exe_bytes: &Vec<u8>) -> Vec<u8> {
        let pe_file = PeFile32::parse(exe_bytes.as_slice())
            .expect("Failed to parse newly pulled out exe file");
        let mut pe_file_adjusted: Vec<u8> = vec![];
        let mut first_flag = false;

        // adjust the byte offsets, because virtual addresses have been thrown off in the initial exe reconstruction process
        for sec in pe_file.section_table().iter() {
            if !first_flag {
                for i in 0..sec.pointer_to_raw_data.get(endian::LittleEndian) {
                    pe_file_adjusted.push(exe_bytes[i as usize]);
                }
                first_flag = true;
            }
            // if this section is NOT bss (no uninitialized data)
            if (sec.characteristics.get(endian::LittleEndian) & 0x80) == 0 {
                assert_eq!(
                    pe_file_adjusted.len() as u32,
                    sec.pointer_to_raw_data.get(endian::LittleEndian),
                    "Unexpected PE size at this point!"
                );
                for j in 0..sec.size_of_raw_data.get(endian::LittleEndian) {
                    let offset = (j + sec.virtual_address.get(endian::LittleEndian)) as usize;
                    if offset >= exe_bytes.len() {
                        pe_file_adjusted.push(0);
                    } else {
                        pe_file_adjusted.push(exe_bytes[offset]);
                    }
                }
            }
        }

        // TODO: fill out the ImportLibrary info and unstrip here

        pe_file_adjusted
    }
}

pub fn write_coff(obj: &ObjInfo) -> Result<Vec<u8>> {
    // let root_name = obj.name.split('.').next().unwrap();
    // println!("Writing {}.obj", root_name);

    // for each obj:
    let mut cur_coff =
        object::write::Object::new(BinaryFormat::Coff, Architecture::PowerPc, Endianness::Big);
    let mut sect_map: BTreeMap<SectionIndex, SectionId> = Default::default();
    let mut sym_map: BTreeMap<SymbolIndex, SymbolId> = Default::default();

    // insert the sections
    for (idx, sect) in obj.sections.iter() {
        // println!("Section: {}", sect.name);
        let sect_id =
            cur_coff.add_section(Vec::new(), sect.name.clone().into_bytes(), match sect.kind {
                ObjSectionKind::Code => SectionKind::Text,
                ObjSectionKind::Data => SectionKind::Data,
                ObjSectionKind::ReadOnlyData => SectionKind::ReadOnlyData,
                ObjSectionKind::Bss => SectionKind::UninitializedData,
            });
        if sect.kind != ObjSectionKind::Bss {
            cur_coff.append_section_data(sect_id, &sect.data, sect.align);
        }
        sect_map.insert(idx, sect_id);
    }

    // insert the symbols
    for (idx, sym) in obj.symbols.iter() {
        let sym_id = cur_coff.add_symbol(object::write::Symbol {
            name: sym.name.clone().into_bytes(),
            value: match sym.section {
                Some(idx) => match obj.sections.get(idx) {
                    Some(sect) => sym.address - sect.address,
                    None => bail!("Could not find section for symbol {}!", sym.name),
                },
                None => 0,
            },
            size: 0,
            kind: match sym.kind {
                ObjSymbolKind::Function => SymbolKind::Text,
                ObjSymbolKind::Object => SymbolKind::Data,
                ObjSymbolKind::Section => SymbolKind::Section,
                ObjSymbolKind::Unknown => match sym.section {
                    Some(_) => SymbolKind::Label,
                    None => SymbolKind::Unknown,
                },
            },
            scope: match sym.flags.scope() {
                ObjSymbolScope::Local => SymbolScope::Compilation,
                _ => SymbolScope::Linkage,
                // ObjSymbolScope::Global => SymbolScope::Linkage,
                // ObjSymbolScope::Weak => SymbolScope::Linkage, // verify this
                // ObjSymbolScope::Unknown => SymbolScope::Unknown,
            },
            weak: false, // sym.flags.scope() == ObjSymbolScope::Weak,
            section: match sym.section {
                Some(idx) => object::write::SymbolSection::Section(*sect_map.get(&idx).unwrap()),
                None => object::write::SymbolSection::Undefined,
            },
            flags: SymbolFlags::None,
        });
        sym_map.insert(idx, sym_id);
    }

    // insert the relocs
    for (sect_idx, sect) in obj.sections.iter() {
        for (addr, reloc) in sect.relocations.iter() {
            let sym_id = match sym_map.get(&reloc.target_symbol) {
                Some(id) => id,
                None => bail!("Could not find symbol ID for index {}", reloc.target_symbol),
            };
            cur_coff.add_relocation(
                *sect_map.get(&sect_idx).unwrap(),
                object::write::Relocation {
                    offset: addr as u64,
                    symbol: *sym_id,
                    addend: 0,
                    flags: RelocationFlags::Coff { typ: reloc.to_coff() },
                },
            )?;
            // MSVC requires an extra relocation to pair up high and low ones
            match reloc.kind {
                ObjRelocKind::PpcAddr16Ha | ObjRelocKind::PpcAddr16Lo => {
                    cur_coff.add_relocation(
                        *sect_map.get(&sect_idx).unwrap(),
                        object::write::Relocation {
                            offset: addr as u64,
                            symbol: *sym_id,
                            addend: 0,
                            flags: RelocationFlags::Coff { typ: object::pe::IMAGE_REL_PPC_PAIR },
                        },
                    )?;
                }
                _ => {}
            }
        }
    }

    // finally, write the COFF
    let coff_data = cur_coff.write()?;
    Ok(coff_data)
}

pub fn coff_path_for_unit(unit: &str) -> Utf8NativePathBuf {
    Utf8UnixPath::new(unit).with_encoding().with_extension("obj")
}

// debug only, lists section bounds
pub fn list_exe_sections(exe: &PeFile32) {
    println!("Sections:");
    for sec in exe.section_table().iter() {
        let name = std::str::from_utf8(&sec.name).unwrap_or("").trim_end_matches('\0');
        println!("Name: {}", name);
        println!("  VirtualSize: 0x{:08X}", sec.virtual_size.get(endian::LittleEndian));
        println!("  VirtualAddress: 0x{:08X}", sec.virtual_address.get(endian::LittleEndian));
        println!("  SizeOfRawData: 0x{:08X}", sec.size_of_raw_data.get(endian::LittleEndian));
        println!("  PointerToRawData: 0x{:08X}", sec.pointer_to_raw_data.get(endian::LittleEndian));
        println!(
            "  Has uninitialized data? {}",
            sec.characteristics.get(endian::LittleEndian) & 0x80 != 0
        );
        println!();
    }
}
