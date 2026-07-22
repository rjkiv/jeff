use std::{borrow::Cow, cmp::min, collections::BTreeMap, fs};

use anyhow::{bail, ensure, Result};
use lzxd::Lzxd;
use num_enum::{IntoPrimitive, TryFromPrimitive};
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
    util::crypto::decrypt_aes128_cbc_no_padding,
};

// quick and ez ways to read data from a block of bytes
pub fn read_halfword(data: &[u8], index: usize) -> u16 {
    u16::from_be_bytes([data[index], data[index + 1]])
}

pub fn read_word(data: &[u8], index: usize) -> u32 {
    u32::from_be_bytes([data[index], data[index + 1], data[index + 2], data[index + 3]])
}

// ----------------------------------------------------------------------
// BASEFILEFORMAT
// ----------------------------------------------------------------------

pub struct BasicCompression {
    pub data_size: u32,
    pub zero_size: u32,
}

pub struct NormalCompression {
    pub window_size: u32,
    pub block_size: u32,
    pub block_hash: [u8; 20],
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, TryFromPrimitive, IntoPrimitive)]
#[repr(u16)]
pub enum XexEncryption {
    No = 0,
    Yes = 1,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, TryFromPrimitive, IntoPrimitive)]
#[repr(u16)]
pub enum XexCompression {
    None = 0,
    Raw = 1,
    Compressed = 2,
    DeltaCompressed = 3,
}

pub struct BaseFileFormat {
    pub encryption: XexEncryption,
    pub compression: XexCompression,
    pub basics: Vec<BasicCompression>,
    pub normal: Option<NormalCompression>,
}

impl BaseFileFormat {
    fn parse(data: &[u8]) -> Result<Self> {
        let encryption = XexEncryption::try_from(read_halfword(data, 0))?;
        let compression = XexCompression::try_from(read_halfword(data, 2))?;
        let mut basics: Vec<BasicCompression> = vec![];
        let mut normal = None;
        match compression {
            XexCompression::None => {}
            XexCompression::Raw => {
                let count = (data.len() - 4) / 8;
                for i in 0..count {
                    basics.push(BasicCompression {
                        data_size: read_word(data, 4 + i * 8),
                        zero_size: read_word(data, 8 + i * 8),
                    });
                }
            }
            XexCompression::Compressed | XexCompression::DeltaCompressed => {
                normal = Some(NormalCompression {
                    window_size: read_word(data, 4),
                    block_size: read_word(data, 8),
                    block_hash: data[12..32].try_into()?,
                });
            }
        }
        Ok(Self { encryption, compression, basics, normal })
    }
}

// ----------------------------------------------------------------------
// IMPORTLIBRARIES
// ----------------------------------------------------------------------

pub struct ImportLibraries {
    pub libraries: Vec<ImportLibrary>,
}

pub struct ImportFunction {
    pub address: u32,
    pub ordinal: u32,
    pub thunk: u32,
}

pub struct ImportLibrary {
    pub name: String,
    pub records: Vec<u32>,
    pub functions: Vec<ImportFunction>,
}

impl ImportLibraries {
    fn parse(data: &[u8]) -> Result<Self> {
        let string_size = read_word(data, 0);
        let lib_count = read_word(data, 4);

        // populate the string table
        let mut string_table: Vec<String> = vec![];
        let mut pos: usize = 8;
        let mut cur_str = String::new();
        let cap: usize = (string_size + 8) as usize;
        while pos < cap {
            if data[pos] != 0 {
                cur_str += &(data[pos] as char).to_string();
            } else {
                // the values in between strings SHOULD be just zeros
                // but some games have super small non-zero values (tomb raider legend)
                while data[pos + 1] < 5 && pos < cap - 1 {
                    pos += 1;
                }
                string_table.push(cur_str.clone());
                cur_str.clear();
            }
            pos += 1;
        }

        // actually parse the import libraries
        pos = cap;
        let mut libraries: Vec<ImportLibrary> = vec![];
        for _ in 0..lib_count {
            pos += 0x24;
            let name_idx = read_halfword(data, pos) as usize;
            let count = read_halfword(data, pos + 2) as usize;
            pos += 4;
            let lib_name = &string_table[name_idx];
            let mut records: Vec<u32> = vec![];
            for i in 0..count {
                records.push(read_word(data, pos + (i * 4)));
            }
            pos += count * 4;
            libraries.push(ImportLibrary {
                name: lib_name.clone(),
                records,
                functions: Vec::new(),
            });
        }
        Ok(Self { libraries })
    }
}

// ----------------------------------------------------------------------
// RESOURCEINFO
// ----------------------------------------------------------------------

pub struct ResourceInfos {
    pub info: Vec<ResourceInfo>,
}

pub struct ResourceInfo {
    pub title_id: String,
    pub rsrc_start: u32,
    pub rsrc_end: u32,
}

impl ResourceInfos {
    pub fn parse(data: &[u8]) -> Result<Self> {
        ensure!(
            data.len() % 16 == 0,
            "Resource info has unexpected length! (expected a multiple of 16)"
        );
        let _num_resources = data.len() / 16;
        let mut info: Vec<ResourceInfo> = vec![];
        for chunk in data.chunks_exact(16) {
            let title_id = String::from_utf8(chunk[0..8].to_vec())?;
            let rsrc_start = u32::from_be_bytes(chunk[8..12].try_into()?);
            let rsrc_end = rsrc_start + u32::from_be_bytes(chunk[12..16].try_into()?);
            info.push(ResourceInfo { title_id, rsrc_start, rsrc_end });
        }
        Ok(Self { info })
    }
}

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
// STATICLIBRARY
// ----------------------------------------------------------------------

pub struct StaticLibrary {
    pub name: String,
    pub major: u16,
    pub minor: u16,
    pub build: u16,
    pub qfe: u8,
    pub approval_type: u8,
}

// ----------------------------------------------------------------------
// XEXOPTIONALHEADERDATA
// ----------------------------------------------------------------------

pub struct XexOptionalHeaderData {
    // Vec<XexOptionalHeader>? should we keep the vector of optional headers we find?
    pub original_name: String,
    pub entry_point: u32,
    pub image_base: u32,
    pub file_timestamp: u32,
    pub resource_info: Option<ResourceInfos>,
    pub base_file_format: Option<BaseFileFormat>,
    // PatchDescriptor
    pub static_libs: Vec<StaticLibrary>,
    pub import_libs: Option<ImportLibraries>,
}

impl XexOptionalHeaderData {
    fn parse(data: &[u8]) -> Result<Self> {
        // read in the optional headers
        let num_optional_headers = read_word(data, 20);
        let mut opt_headers: Vec<XexOptionalHeader> = vec![];
        for n in 0..num_optional_headers {
            opt_headers.push(XexOptionalHeader::new(data, (24 + n * 8) as usize));
        }

        // some games (kameo cough cough) don't include an original name
        // so, we'll provide this as a default
        let mut original_name = String::from("output.exe");
        let mut entry_point = 0;
        let mut image_base = 0;
        let mut file_timestamp = 0;
        let mut import_libs = None;
        let mut resource_info = None;
        let mut base_file_format = None;
        let mut static_libs: Vec<StaticLibrary> = vec![];

        // and now, process them
        for header in opt_headers {
            ensure!(!header.data.is_empty(), "No data found in optional header!");
            match header.id {
                XexOptionalHeaderID::ResourceInfo => {
                    resource_info = Some(ResourceInfos::parse(&header.data)?);
                }
                XexOptionalHeaderID::BaseFileFormat => {
                    base_file_format = Some(BaseFileFormat::parse(&header.data)?);
                }
                XexOptionalHeaderID::DeltaPatchDescriptor => {
                    log::debug!("TODO: handle patch descriptor");
                    println!(
                        "Target version: v{}.{}.{}.{}",
                        header.data[0], header.data[1], header.data[2], header.data[3]
                    );
                    println!(
                        "Source version: v{}.{}.{}.{}",
                        header.data[4], header.data[5], header.data[6], header.data[7]
                    );
                    let mut pos = 8;
                    print!("Source digest: ");
                    for i in 0..20 {
                        print!("{:02X} ", header.data[pos]);
                        pos += 1;
                    }
                    // at this point, pos = 28 = 0x1C
                    print!("\n");
                    print!("Source image key: ");
                    for i in 0..16 {
                        print!("{:02X} ", header.data[pos]);
                        pos += 1;
                    }
                    print!("\n");
                    // at this point, pos = 44 = 0x2C
                    println!(
                        "Word at pos={:X}: {:08X} (target header size)",
                        pos,
                        read_word(&header.data, pos)
                    );
                    pos += 4;
                    println!(
                        "Word at pos={:X}: {:08X} (delta headers source offset)",
                        pos,
                        read_word(&header.data, pos)
                    );
                    pos += 4;
                    println!(
                        "Word at pos={:X}: {:08X} (delta headers source size)",
                        pos,
                        read_word(&header.data, pos)
                    );
                    pos += 4;
                    println!(
                        "Word at pos={:X}: {:08X} (delta headers target offset)",
                        pos,
                        read_word(&header.data, pos)
                    );
                    pos += 4;
                    println!(
                        "Word at pos={:X}: {:08X} (delta image source offset)",
                        pos,
                        read_word(&header.data, pos)
                    );
                    pos += 4;
                    println!(
                        "Word at pos={:X}: {:08X} (delta image source size)",
                        pos,
                        read_word(&header.data, pos)
                    );
                    pos += 4;
                    println!(
                        "Word at pos={:X}: {:08X} (delta image target offset)",
                        pos,
                        read_word(&header.data, pos)
                    );
                }
                XexOptionalHeaderID::BoundingPath => {
                    log::debug!("TODO: handle bounding path");
                }
                XexOptionalHeaderID::EntryPoint => {
                    entry_point = read_word(&header.data, 0);
                }
                XexOptionalHeaderID::ImageBaseAddress => {
                    image_base = read_word(&header.data, 0);
                }
                XexOptionalHeaderID::ImportLibraries => {
                    import_libs = Some(ImportLibraries::parse(&header.data)?);
                }
                XexOptionalHeaderID::OriginalPEName => {
                    // trim off the 0's
                    let mut name = header.data.clone();
                    if let Some(i) = name.iter().rposition(|&x| x != 0) {
                        let new_len = i + 1;
                        name.truncate(new_len);
                    }
                    original_name = String::from_utf8(name)?;
                }
                XexOptionalHeaderID::ChecksumTimestamp => {
                    file_timestamp = read_word(&header.data, 0);
                }
                XexOptionalHeaderID::StaticLibraries => {
                    let num_libs = header.data.len() / 16;
                    for i in 0..num_libs {
                        let start = i * 16;
                        let mut name = header.data[start..start + 8].to_vec();
                        name.retain(|&x| x != 0);
                        static_libs.push(StaticLibrary {
                            name: String::from_utf8(name)?,
                            major: read_halfword(&header.data, start + 8),
                            minor: read_halfword(&header.data, start + 10),
                            build: read_halfword(&header.data, start + 12),
                            qfe: header.data[start + 15],
                            approval_type: header.data[start + 14],
                        });
                    }
                }
                _ => {
                    log::warn!("unhandled header ID {:?}", header.id);
                }
            }
        }
        // at the very minimum, we should have a base file format, as that contains encryption/compression information
        ensure!(base_file_format.is_some(), "Base file format not found!");
        Ok(Self {
            original_name,
            entry_point,
            image_base,
            file_timestamp,
            resource_info,
            base_file_format,
            static_libs,
            import_libs,
        })
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, TryFromPrimitive, IntoPrimitive)]
#[repr(u32)]
pub enum XexOptionalHeaderID {
    ResourceInfo = 0x2FF,
    BaseFileFormat = 0x3FF,
    BaseReference = 0x405,
    DeltaPatchDescriptor = 0x5FF,
    BoundingPath = 0x80FF,
    DeviceID = 0x8105,
    OriginalBaseAddress = 0x10001,
    EntryPoint = 0x10100,
    ImageBaseAddress = 0x10201,
    ImportLibraries = 0x103FF,
    ChecksumTimestamp = 0x18002,
    EnabledForCallcap = 0x18102,
    EnabledForFastcap = 0x18200,
    OriginalPEName = 0x183FF,
    StaticLibraries = 0x200FF,
    TLSInfo = 0x20104,
    DefaultStackSize = 0x20200,
    DefaultFilesystemCacheSize = 0x20301,
    DefaultHeapSize = 0x20401,
    PageHeapSizeAndFlags = 0x28002,
    SystemFlags = 0x30000,
    Unknown30100 = 0x30100,
    ExecutionID = 0x40006,
    ServiceIDList = 0x401FF,
    TitleWorkspaceSize = 0x40201,
    GameRatings = 0x40310,
    LANKey = 0x40404,
    Xbox360Logo = 0x405FF,
    MultidiscMediaIDs = 0x406FF,
    AlternateTitleIDs = 0x407FF,
    AdditionalTitleMemory = 0x40801,
    ExportsByName = 0xE10402,
}

pub struct XexOptionalHeader {
    pub id: XexOptionalHeaderID,
    pub value: u32,
    pub data: Vec<u8>,
}

impl XexOptionalHeader {
    pub fn new(data: &[u8], index: usize) -> Self {
        let mut hdr = Self {
            id: XexOptionalHeaderID::try_from(read_word(data, index)).unwrap(),
            value: read_word(data, index + 4),
            data: Vec::new(),
        };

        let id_as_u32: u32 = hdr.id.into();
        let mask = id_as_u32 & 0xFF;
        if mask == 0xFF {
            // seek the binstream to hdr.value, read the word (that's your len)
            let len = read_word(data, hdr.value as usize);
            let start: usize = (hdr.value + 4) as usize;
            let end: usize = (hdr.value + len) as usize;
            hdr.data = data[start..end].to_vec();
        } else if mask < 2 {
            // data = value as a Vec<u8>
            // println!("for ID 0x{:X}, value = 0x{:X}", id_as_u32, hdr.value);
            hdr.data = data[index + 4..index + 8].to_vec();
        } else {
            let len = mask * 4;
            let start: usize = (hdr.value + 4) as usize;
            let end: usize = (hdr.value + len) as usize;
            hdr.data = data[start..end].to_vec();
        }
        hdr
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
    pub opt_header_data: XexOptionalHeaderData,
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
        // parse the base xex first
        let base_data = fs::read(base_path.to_path_buf()).expect("Failed to read file");

        // TODO: get rid of this struct, we can just use the raw vars here and don't use them anywhere else
        let xex_header = XexHeader::parse(&base_data)?;
        assert_ne!(xex_header.module_flags & 1, 0, "Not a base game xex!");
        let xex_optional_header_data = XexOptionalHeaderData::parse(&base_data)?;
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
        let Some(bff) = &xex_optional_header_data.base_file_format else {
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

        // adjust the byte offsets, because virtual addresses have been thrown off in the initial exe reconstruction process
        let pe_file =
            PeFile32::parse(&*exe_bytes).expect("Failed to parse newly pulled out exe file");
        let mut pe_file_adjusted: Vec<u8> = vec![];
        let mut first_flag = false;

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

        // we have an adjusted, base exe at this point
        // if we've got a patch xex, parse it and apply it on top
        if let Some(patch_path) = patch_path {
            // parse the base xex first
            let xexp_data = fs::read(patch_path.to_path_buf()).expect("Failed to read file");
            let xexp_header = XexHeader::parse(&xexp_data)?;
            assert_ne!(xexp_header.module_flags & 16, 0, "Not an xex patch file!");
            let xexp_optional_header_data = XexOptionalHeaderData::parse(&xexp_data)?;
            let xexp_loader_info =
                XexLoaderInfo::parse(&xexp_data, xexp_header.security_info_offset)?;
            if xexp_header.module_flags & 32 != 0 {
                todo!("Full patch not implemented yet! If your game has a full patch file, please let me know on Github issues!");
            }
            if xexp_header.module_flags & 64 != 0 {
                println!("Delta patch!");
                let patch_vec =
                    &xexp_data[xexp_header.pe_offset as usize..xexp_data.len()].to_vec();
                let Some(bff) = &xexp_optional_header_data.base_file_format else {
                    panic!("We need to have a BaseFileFormat at this point!")
                };
                let patch_decompressed = XexInfo::decompress(
                    patch_vec,
                    &confirmed_session_key,
                    bff,
                    xexp_header.security_info_offset,
                )?;
                println!("Decompressed patch size: {}", patch_decompressed.len());
            }
        }

        Ok(Self {
            header: xex_header,
            opt_header_data: xex_optional_header_data,
            loader_info: xex_loader_info,
            session_key: confirmed_session_key,
            is_dev_kit,
            exe_bytes: pe_file_adjusted,
        })
    }

    fn decompress(
        input: &[u8],
        session_key: &[u8; 16],
        bff: &BaseFileFormat,
        img_size: u32,
    ) -> Result<Vec<u8>> {
        let compressed: Cow<[u8]> = match bff.encryption {
            XexEncryption::No => Cow::Borrowed(input),
            XexEncryption::Yes => Cow::Owned(decrypt_aes128_cbc_no_padding(session_key, input)?),
        };

        let mut output_bytes: Vec<u8> = vec![0; img_size as usize];
        let mut pos_in: usize = 0;
        let mut pos_out: usize = 0;

        match bff.compression {
            XexCompression::Raw => {
                for bc in &bff.basics {
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
            XexCompression::None | XexCompression::DeltaCompressed => {
                output_bytes = compressed.to_vec();
            }
            XexCompression::Compressed => {
                let comp = bff.normal.as_ref().unwrap();
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
        }
        Ok(output_bytes)
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
