use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fs::File,
    vec::Vec,
};

use anyhow::{ensure, Result};
use itertools::Itertools;
use pdb::{self, FallibleIterator};
use typed_path::Utf8NativePathBuf;

use crate::{
    analysis::cfa::SectionAddress,
    obj::{
        ObjDataKind, ObjSection, ObjSections, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags,
        ObjSymbolKind, ObjSymbolScope,
    },
};

/// This map is only used to give descriptive names to the SymbolKinds that
/// the pdb crate cannot parse; it doesn't need to be exhaustive.
fn sym_kind_name(kind: pdb::SymbolKind) -> &'static str {
    match kind {
        0x1012 => "S_FRAMEPROC",
        0x1136 => "S_SECTION",
        0x1137 => "S_COFFGROUP",
        _ => "Unknown",
    }
}

fn warn_unsupported_sym_kind(sym: &pdb::Symbol, set: &mut HashSet<pdb::SymbolKind>) {
    if set.insert(sym.raw_kind()) {
        log::warn!(
            "Unsupported symbol kind: {} (0x{:X})",
            sym_kind_name(sym.raw_kind()),
            sym.raw_kind()
        );
    }
}

/// Convert to jeff's SectionAddress type
fn to_section_addr(
    pdbmap: &pdb::AddressMap,
    pdb2dtk_section: &[u8; 32],
    pdb_offs: &pdb::PdbInternalSectionOffset,
) -> SectionAddress {
    let s_addr = pdb_offs.to_section_offset(pdbmap).unwrap_or_default();
    SectionAddress {
        address: s_addr.offset,
        section: pdb2dtk_section[s_addr.section as usize] as u32,
    }
}

fn to_virtual_address(
    pdbmap: &pdb::AddressMap,
    section_addrs: &ObjSections,
    pdb2dtk_section: &[u8; 32],
    pdb_offs: &pdb::PdbInternalSectionOffset,
) -> Result<u64> {
    let s_addr = to_section_addr(pdbmap, pdb2dtk_section, pdb_offs);
    let sect_base = section_addrs.get(s_addr.section).unwrap_or(&ObjSection::default()).address;
    Ok(s_addr.address as u64 + sect_base)
}

pub fn try_parse_pdb(
    path: &Utf8NativePathBuf,
    section_addrs: &ObjSections,
) -> Result<Vec<ObjSymbol>> {
    let mut dbfile = pdb::PDB::open(File::open(path)?)?;

    // setup configgery
    let mut pdb2dtk_section: [u8; 32] =
        std::array::from_fn::<u8, 32, _>(|x: usize| -> u8 { x as u8 });

    // build PDB -> DTK section lookup table
    ensure!(section_addrs.len() <= 32, "Oh god, why does your XEX have more than 32 sections?");
    {
        let dtk_iter = section_addrs.iter();
        let sec_headers = dbfile.sections()?.unwrap();
        let mut embsec_counter = 0;
        let pdb_hdr_names: Vec<String> = sec_headers
            .iter()
            .map(|hdr| {
                let s_name: String = if hdr.name() == ".embsec_" {
                    embsec_counter += 1;
                    format!(".embsec{}", embsec_counter - 1).to_string()
                } else {
                    hdr.name().to_string()
                };
                s_name
            })
            .collect();

        for dtk_section in dtk_iter {
            pdb_hdr_names.iter().enumerate().for_each(|x| {
                if *x.1 == dtk_section.1.name {
                    pdb2dtk_section[x.0 + 1] = dtk_section.0 as u8;
                    log::debug!(
                        "Remapping PDB section {} (no. {}) to DTK section {} (no. {})",
                        x.1,
                        x.0 + 1,
                        dtk_section.1.name,
                        dtk_section.0
                    );
                }
            });
        }
    }

    let pdbmap = dbfile.address_map()?;
    let mut unsupported_sym_kinds = HashSet::new();
    let mut syms: BTreeMap<SectionAddress, ObjSymbol> = BTreeMap::new();

    let dbi = dbfile.debug_information()?;
    let global_symtable = dbfile.global_symbols()?;
    let mut all_syms: Vec<pdb::Symbol> = vec![];

    // Collect Global and Module symbol streams into one combined iterator
    let mut global_syms = global_symtable.iter();
    while let Some(sym) = global_syms.next()? {
        all_syms.push(sym);
    }

    let mut modules = dbi.modules()?;
    let mut module_infos = vec![];
    while let Some(module) = modules.next()? {
        if let Some(info) = dbfile.module_info(&module)? {
            module_infos.push(info);
        }
    }
    for info in &module_infos {
        let mut module_syms = info.symbols()?;
        while let Some(sym) = module_syms.next()? {
            all_syms.push(sym);
        }
    }

    let all_syms_iter = all_syms.into_iter();
    let mut ldata_dupes: HashMap<String, u32> = HashMap::new();
    for symbol in all_syms_iter {
        match symbol.parse() {
            Ok(pdb::SymbolData::Public(data)) => {
                let symaddr = to_section_addr(&pdbmap, &pdb2dtk_section, &data.offset);
                let obj_sym = syms.entry(symaddr).or_default();

                // We get almost everything we need to know about a symbol
                // from its S_PUB32 record. However, we must revisit this
                // entry when parsing its corresponding PROC or DATA record
                // to compute its size
                // TODO: handle code/data merging properly, instead of
                // overwriting the name

                // TODO: Not all S_PUB32 records represent functions or objects;
                // Some may just be labels, which can be skipped
                obj_sym.name = data.name.to_string().into();
                obj_sym.address =
                    to_virtual_address(&pdbmap, section_addrs, &pdb2dtk_section, &data.offset)?;
                obj_sym.section = Some(symaddr.section);
                obj_sym.flags = ObjSymbolFlagSet(ObjSymbolFlags::Global.into());
                obj_sym.kind =
                    if data.function { ObjSymbolKind::Function } else { ObjSymbolKind::Object };
                obj_sym.data_kind = ObjDataKind::Unknown;
            }
            Ok(pdb::SymbolData::Data(data)) => {
                let symaddr = to_section_addr(&pdbmap, &pdb2dtk_section, &data.offset);
                let obj_sym = syms.entry(symaddr).or_default();

                // This is an S_GDATA32 or S_LDATA32 record
                if data.global {
                    obj_sym.flags.set_scope(ObjSymbolScope::Global);
                } else {
                    obj_sym.flags.set_scope(ObjSymbolScope::Local);
                    obj_sym.kind = ObjSymbolKind::Object;
                    let name = data.name.to_string().clone();
                    let c =
                        *ldata_dupes.entry(name.to_string()).and_modify(|c| *c += 1).or_insert(1);
                    let name: String = if c > 1 {
                        format!("static_dup_{}_{}", c - 1, name)
                    } else {
                        data.name.to_string().into()
                    };
                    obj_sym.name = name;
                    obj_sym.address =
                        to_virtual_address(&pdbmap, section_addrs, &pdb2dtk_section, &data.offset)?;
                    obj_sym.section = Some(symaddr.section);
                }
                // TODO: We can also deduce the size by using the type
                // field to index into the TPI.
                // Build a TypeFinder, then use it to compute object sizes
                // while iterating through the data symbols.
                // See https://docs.rs/pdb/latest/pdb/struct.ItemInformation.html
            }
            Ok(pdb::SymbolData::ThreadStorage(data)) => {
                let symaddr = to_section_addr(&pdbmap, &pdb2dtk_section, &data.offset);
                let obj_sym = syms.entry(symaddr).or_default();

                // This is an S_GTHREAD32 or S_LTHREAD32 record
                if data.global {
                    obj_sym.flags.set_scope(ObjSymbolScope::Global);
                } else {
                    obj_sym.flags.set_scope(ObjSymbolScope::Local);
                    obj_sym.kind = ObjSymbolKind::Object;
                    obj_sym.name = data.name.to_string().into();
                    obj_sym.address =
                        to_virtual_address(&pdbmap, section_addrs, &pdb2dtk_section, &data.offset)?;
                    obj_sym.section = Some(symaddr.section);
                }

                // TODO: Above note for DATA records also applies here
            }
            Ok(pdb::SymbolData::Procedure(data)) => {
                let symaddr = to_section_addr(&pdbmap, &pdb2dtk_section, &data.offset);
                let obj_sym = syms.entry(symaddr).or_default();

                // This is an S_GPROC32 or S_LPROC32 record
                obj_sym.size = data.len as u64;
                obj_sym.size_known = true;
                obj_sym.align = Some(4);
                if data.global {
                    obj_sym.flags.set_scope(ObjSymbolScope::Global);
                } else {
                    obj_sym.flags.set_scope(ObjSymbolScope::Local);
                    obj_sym.kind = ObjSymbolKind::Function;
                    obj_sym.name = data.name.to_string().into();
                    obj_sym.address =
                        to_virtual_address(&pdbmap, section_addrs, &pdb2dtk_section, &data.offset)?;
                    obj_sym.section = Some(symaddr.section);
                }
            }
            Ok(pdb::SymbolData::Thunk(data)) => {
                let symaddr = to_section_addr(&pdbmap, &pdb2dtk_section, &data.offset);
                let obj_sym = syms.entry(symaddr).or_default();

                // This is an S_THUNK32 record
                obj_sym.size = data.len as u64;
                obj_sym.size_known = true;
                obj_sym.align = Some(4);
            }
            // TODO: S_SECTION and S_COFFGROUP records are also useful,
            // but pdb 0.8.0 apparently can't parse them
            Ok(_) => {}
            Err(pdb::Error::UnimplementedSymbolKind(_)) => {
                warn_unsupported_sym_kind(&symbol, &mut unsupported_sym_kinds);
            }
            Err(parse_error) => {
                return Err(parse_error.into());
            }
        }
    }

    let mut addr_vec = syms.into_values().collect_vec();

    // weed out xidata and _RtlCheckStack symbols (jeff finds them later)
    let xidata_symbols: Vec<ObjSymbol> = addr_vec
        .iter()
        .filter_map(|x| {
            if x.name == "_RtlCheckStack12"
                || x.name == "_RtlCheckStack"
                || x.name.contains("__imp_")
            {
                Some(x.clone())
            } else {
                None
            }
        })
        .collect_vec();
    let vec_it = xidata_symbols.iter().rev();
    for sym in vec_it {
        if let Some(idx) = addr_vec.iter().enumerate().find_map(|x| {
            if x.1.name.contains(sym.name.as_str()) {
                Some(x.0)
            } else {
                None
            }
        }) {
            log::debug!("Dropping idx {}", idx);
            addr_vec.remove(idx);
        };
    }

    Ok(addr_vec)
}
