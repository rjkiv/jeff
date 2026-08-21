use anyhow::{Result, ensure};

use crate::util::read::{read_halfword, read_word};

pub struct ResourceInfo {
    pub title_id: String,
    pub rsrc_start: u32,
    pub rsrc_end: u32,
}

pub struct BasicCompression {
    pub data_size: u32,
    pub zero_size: u32,
}

pub struct NormalCompression {
    pub window_size: u32,
    pub block_size: u32,
    pub block_hash: [u8; 20],
}

pub enum XexCompression {
    None,
    Raw { basics: Vec<BasicCompression> },
    Compressed { normal: NormalCompression },
    DeltaCompressed { normal: NormalCompression },
}

pub struct BaseFileFormat {
    pub encrypted: bool,
    pub compression: XexCompression,
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

pub struct StaticLibrary {
    pub name: String,
    pub major: u16,
    pub minor: u16,
    pub build: u16,
    pub qfe: u8,
    pub approval_type: u8,
}

pub struct DeltaPatch {
    pub old_addr: u32,
    pub new_addr: u32,
    pub uncompressed_len: u16,
    pub compressed_len: u16,
    pub patch_data: Vec<u8>,
}

impl DeltaPatch {
    pub fn parse(data: &[u8], offset: usize) -> Self {
        let compressed_len = read_halfword(data, offset + 10);
        Self {
            old_addr: read_word(data, offset),
            new_addr: read_word(data, offset + 4),
            uncompressed_len: read_halfword(data, offset + 8),
            compressed_len,
            patch_data: data[offset + 12..offset + 12 + compressed_len as usize].to_vec(),
        }
    }
}
pub struct DeltaPatchDescriptor {
    // pub target_version: [u8; 4],
    // pub source_version: [u8; 4],
    // pub source_digest: [u8; 20],
    // pub source_image_key: [u8; 16],
    pub size_of_target_headers: u32,
    pub delta_headers_source_offset: u32,
    pub delta_headers_source_size: u32,
    pub delta_headers_target_offset: u32,
    pub delta_image_source_offset: u32,
    pub delta_image_source_size: u32,
    pub delta_image_target_offset: u32,
    pub delta_patch: DeltaPatch,
}

struct XexOptionalHeaderData {
    pub id: u32,
    pub data: Vec<u8>,
}

impl XexOptionalHeaderData {
    pub fn new(data: &[u8], index: usize) -> Self {
        let id = read_word(data, index);
        let value = read_word(data, index + 4);

        let mask = id & 0xFF;
        let hdr_data = if mask == 0xFF {
            // seek the binstream to value, read the word (that's your len)
            let len = read_word(data, value as usize);
            let start: usize = (value + 4) as usize;
            let end: usize = (value + len) as usize;
            data[start..end].to_vec()
        } else if mask < 2 {
            // data = value as a Vec<u8>
            // println!("for ID 0x{:X}, value = 0x{:X}", id_as_u32, value);
            data[index + 4..index + 8].to_vec()
        } else {
            let len = mask * 4;
            let start: usize = (value + 4) as usize;
            let end: usize = (value + len) as usize;
            data[start..end].to_vec()
        };
        Self { id, data: hdr_data }
    }
}

pub enum XexOptionalHeader {
    ResourceInfo { info: Vec<ResourceInfo> },
    BaseFileFormat { format: BaseFileFormat },
    // BaseReference = 0x405,
    DeltaPatchDescriptor { descriptor: DeltaPatchDescriptor },
    // BoundingPath = 0x80FF,
    // DeviceID = 0x8105,
    // OriginalBaseAddress = 0x10001,
    EntryPoint { entry: u32 },
    ImageBaseAddress { image_base: u32 },
    ImportLibraries { libraries: Vec<ImportLibrary> },
    ChecksumTimestamp { timestamp: u32 },
    // EnabledForCallcap = 0x18102,
    // EnabledForFastcap = 0x18200,
    OriginalPEName { name: String },
    StaticLibraries { libraries: Vec<StaticLibrary> },
    // TLSInfo = 0x20104,
    // DefaultStackSize = 0x20200,
    // DefaultFilesystemCacheSize = 0x20301,
    // DefaultHeapSize = 0x20401,
    // PageHeapSizeAndFlags = 0x28002,
    // SystemFlags = 0x30000,
    // Unknown30100 = 0x30100,
    // ExecutionID = 0x40006,
    // ServiceIDList = 0x401FF,
    // TitleWorkspaceSize = 0x40201,
    // GameRatings = 0x40310,
    // LANKey = 0x40404,
    // Xbox360Logo = 0x405FF,
    // MultidiscMediaIDs = 0x406FF,
    // AlternateTitleIDs = 0x407FF,
    // AdditionalTitleMemory = 0x40801,
    // ExportsByName = 0xE10402,
}

pub fn parse_xex_optional_headers(xex_data: &[u8]) -> Result<Vec<XexOptionalHeader>> {
    // read in the optional headers
    let num_optional_headers = read_word(xex_data, 20);
    let mut opt_headers: Vec<XexOptionalHeaderData> = vec![];
    for n in 0..num_optional_headers {
        opt_headers.push(XexOptionalHeaderData::new(xex_data, (24 + n * 8) as usize));
    }

    let mut xex_optional_headers: Vec<XexOptionalHeader> = Vec::new();

    for header in opt_headers {
        ensure!(!header.data.is_empty(), "No data found in optional header!");
        match header.id {
            0x2FF => {
                ensure!(
                    header.data.len() % 16 == 0,
                    "Resource info has unexpected length! (expected a multiple of 16)"
                );
                let mut info: Vec<ResourceInfo> = vec![];
                for chunk in header.data.as_chunks::<16>().0 {
                    let title_id = String::from_utf8(chunk[0..8].to_vec())?;
                    let rsrc_start = u32::from_be_bytes(chunk[8..12].try_into()?);
                    let rsrc_end = rsrc_start + u32::from_be_bytes(chunk[12..16].try_into()?);
                    info.push(ResourceInfo { title_id, rsrc_start, rsrc_end });
                }
                xex_optional_headers.push(XexOptionalHeader::ResourceInfo { info });
            }
            0x3FF => {
                let encrypted = match read_halfword(&header.data, 0) {
                    0 => false,
                    1 => true,
                    _ => unreachable!(),
                };
                let compression = match read_halfword(&header.data, 2) {
                    0 => XexCompression::None,
                    1 => {
                        let mut basics: Vec<BasicCompression> = vec![];
                        let count = (&header.data.len() - 4) / 8;
                        for i in 0..count {
                            basics.push(BasicCompression {
                                data_size: read_word(&header.data, 4 + i * 8),
                                zero_size: read_word(&header.data, 8 + i * 8),
                            });
                        }
                        XexCompression::Raw { basics }
                    }
                    2 => XexCompression::Compressed {
                        normal: NormalCompression {
                            window_size: read_word(&header.data, 4),
                            block_size: read_word(&header.data, 8),
                            block_hash: header.data[12..32].try_into()?,
                        },
                    },
                    3 => XexCompression::DeltaCompressed {
                        normal: NormalCompression {
                            window_size: read_word(&header.data, 4),
                            block_size: read_word(&header.data, 8),
                            block_hash: header.data[12..32].try_into()?,
                        },
                    },
                    _ => unreachable!(),
                };
                xex_optional_headers.push(XexOptionalHeader::BaseFileFormat {
                    format: BaseFileFormat { encrypted, compression },
                });
            }
            0x405 => {
                log::debug!("TODO: implement BaseReference")
            }
            0x5FF => {
                xex_optional_headers.push(XexOptionalHeader::DeltaPatchDescriptor {
                    descriptor: DeltaPatchDescriptor {
                        size_of_target_headers: read_word(&header.data, 44),
                        delta_headers_source_offset: read_word(&header.data, 48),
                        delta_headers_source_size: read_word(&header.data, 52),
                        delta_headers_target_offset: read_word(&header.data, 56),
                        delta_image_source_offset: read_word(&header.data, 60),
                        delta_image_source_size: read_word(&header.data, 64),
                        delta_image_target_offset: read_word(&header.data, 68),
                        delta_patch: DeltaPatch::parse(&header.data, 72),
                    },
                });
            }
            0x80FF => {
                log::debug!("TODO: implement BoundingPath")
            }
            0x8105 => {
                log::debug!("TODO: implement DeviceID")
            }
            0x10001 => {
                log::debug!("TODO: implement OriginalBaseAddress")
            }
            0x10100 => {
                xex_optional_headers
                    .push(XexOptionalHeader::EntryPoint { entry: read_word(&header.data, 0) });
            }
            0x10201 => {
                xex_optional_headers.push(XexOptionalHeader::ImageBaseAddress {
                    image_base: read_word(&header.data, 0),
                });
            }
            0x103FF => {
                let string_size = read_word(&header.data, 0);
                let lib_count = read_word(&header.data, 4);

                // populate the string table
                let mut string_table: Vec<String> = vec![];
                let mut pos: usize = 8;
                let mut cur_str = String::new();
                let cap: usize = (string_size + 8) as usize;
                while pos < cap {
                    if header.data[pos] != 0 {
                        cur_str += &(header.data[pos] as char).to_string();
                    } else {
                        // the values in between strings SHOULD be just zeros
                        // but some games have super small non-zero values (tomb raider legend)
                        while header.data[pos + 1] < 5 && pos < cap - 1 {
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
                    let name_idx = read_halfword(&header.data, pos) as usize;
                    let count = read_halfword(&header.data, pos + 2) as usize;
                    pos += 4;
                    let lib_name = &string_table[name_idx];
                    let mut records: Vec<u32> = vec![];
                    for i in 0..count {
                        records.push(read_word(&header.data, pos + (i * 4)));
                    }
                    pos += count * 4;
                    libraries.push(ImportLibrary {
                        name: lib_name.clone(),
                        records,
                        functions: Vec::new(),
                    });
                }
                xex_optional_headers.push(XexOptionalHeader::ImportLibraries { libraries });
            }
            0x18002 => {
                xex_optional_headers.push(XexOptionalHeader::ChecksumTimestamp {
                    timestamp: read_word(&header.data, 0),
                });
            }
            0x18102 => {
                log::debug!("TODO: implement EnabledForCallcap")
            }
            0x18200 => {
                log::debug!("TODO: implement EnabledForFastcap")
            }
            0x183FF => {
                // trim off the 0's
                let mut name = header.data.clone();
                if let Some(i) = name.iter().rposition(|&x| x != 0) {
                    let new_len = i + 1;
                    name.truncate(new_len);
                }
                xex_optional_headers
                    .push(XexOptionalHeader::OriginalPEName { name: String::from_utf8(name)? });
            }
            0x200FF => {
                let num_libs = header.data.len() / 16;
                let mut libraries: Vec<StaticLibrary> = vec![];
                for i in 0..num_libs {
                    let start = i * 16;
                    let mut name = header.data[start..start + 8].to_vec();
                    name.retain(|&x| x != 0);
                    libraries.push(StaticLibrary {
                        name: String::from_utf8(name)?,
                        major: read_halfword(&header.data, start + 8),
                        minor: read_halfword(&header.data, start + 10),
                        build: read_halfword(&header.data, start + 12),
                        qfe: header.data[start + 15],
                        approval_type: header.data[start + 14],
                    });
                }
                xex_optional_headers.push(XexOptionalHeader::StaticLibraries { libraries });
            }
            0x20104 => {
                log::debug!("TODO: implement TLSInfo")
            }
            0x20200 => {
                log::debug!("TODO: implement DefaultStackSize")
            }
            0x20301 => {
                log::debug!("TODO: implement DefaultFilesystemCacheSize")
            }
            0x20401 => {
                log::debug!("TODO: implement DefaultHeapSize")
            }
            0x28002 => {
                log::debug!("TODO: implement PageHeapSizeAndFlags")
            }
            0x30000 => {
                log::debug!("TODO: implement SystemFlags")
            }
            0x30100 => {
                log::debug!("TODO: implement Unknown30100")
            }
            0x40006 => {
                log::debug!("TODO: implement ExecutionID")
            }
            0x401FF => {
                log::debug!("TODO: implement ServiceIDList")
            }
            0x40201 => {
                log::debug!("TODO: implement TitleWorkspaceSize")
            }
            0x40310 => {
                log::debug!("TODO: implement GameRatings")
            }
            0x40404 => {
                log::debug!("TODO: implement LANKey")
            }
            0x405FF => {
                log::debug!("TODO: implement Xbox360Logo")
            }
            0x406FF => {
                log::debug!("TODO: implement MultidiscMediaIDs")
            }
            0x407FF => {
                log::debug!("TODO: implement AlternateTitleIDs")
            }
            0x40801 => {
                log::debug!("TODO: implement AdditionalTitleMemory")
            }
            0xE10402 => {
                log::debug!("TODO: implement ExportsByName")
            }
            _ => {
                log::warn!("Unhandled ID {:08X}!", header.id);
            }
        };
    }

    Ok(xex_optional_headers)
}
