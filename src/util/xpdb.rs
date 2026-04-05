use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fs::File,
    vec::Vec,
};

use anyhow::{ensure, Result};
use itertools::Itertools;
use pdb2::{self, FallibleIterator};
use typed_path::Utf8NativePathBuf;

use crate::{
    analysis::cfa::SectionAddress,
    obj::{
        ObjDataKind, ObjSection, ObjSections, ObjSplit, ObjSplits, ObjSymbol, ObjSymbolFlagSet,
        ObjSymbolFlags, ObjSymbolKind, ObjSymbolScope,
    },
};

/// This map is only used to give descriptive names to the SymbolKinds that
/// the pdb crate cannot parse; it doesn't need to be exhaustive.
fn sym_kind_name(kind: pdb2::SymbolKind) -> &'static str {
    match kind {
        0x1012 => "S_FRAMEPROC",
        0x1136 => "S_SECTION",
        0x1137 => "S_COFFGROUP",
        _ => "Unknown",
    }
}

fn warn_unsupported_sym_kind(sym: &pdb2::Symbol, set: &mut HashSet<pdb2::SymbolKind>) {
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
    pdbmap: &pdb2::AddressMap,
    pdb_offs: &pdb2::PdbInternalSectionOffset,
) -> SectionAddress {
    let s_addr = pdb_offs.to_section_offset(pdbmap).unwrap_or_default();
    SectionAddress {
        address: s_addr.offset,
        // jeff sections are 0-indexed
        section: s_addr.section as u32 - 1,
    }
}

fn section_addr_to_virtual_addr(section_addrs: &ObjSections, s_addr: &SectionAddress) -> u64 {
    let sect_base = section_addrs.get(s_addr.section).unwrap_or(&ObjSection::default()).address;
    s_addr.address as u64 + sect_base
}

fn to_virtual_address(
    pdbmap: &pdb2::AddressMap,
    section_addrs: &ObjSections,
    pdb_offs: &pdb2::PdbInternalSectionOffset,
) -> u64 {
    section_addr_to_virtual_addr(section_addrs, &to_section_addr(pdbmap, pdb_offs))
}

#[derive(Debug, PartialEq, PartialOrd, Eq, Ord)]
struct CoffGroup {
    /// Starting address of the group
    pub address: u64,
    /// jeff section number
    pub section: u32,
    /// Group size in bytes
    pub size: u32,
    /// Full COFF group name
    pub name: String,
}

/// Extract translation units, splits, and symbols from a PDB
pub fn try_parse_pdb(
    path: &Utf8NativePathBuf,
    section_addrs: &ObjSections,
) -> Result<(Vec<String>, Vec<ObjSplits>, Vec<ObjSymbol>)> {
    let mut dbfile = pdb2::PDB::open(File::open(path)?)?;

    // Ensure pdb sections match the exe sections and that all the names match
    {
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
        ensure!(
            pdb_hdr_names.len() == section_addrs.len() as usize,
            "PDB has {} sections, EXE has {}",
            pdb_hdr_names.len(),
            section_addrs.len()
        );
        for i in 0..pdb_hdr_names.len() {
            ensure!(
                pdb_hdr_names[i] == section_addrs[i as u32].name,
                "PDB section '{}' does not match EXE section '{}'",
                pdb_hdr_names[i],
                section_addrs[i as u32].name
            );
        }
    }

    let pdbmap = dbfile.address_map()?;
    let mut unsupported_sym_kinds = HashSet::new();
    let mut syms: BTreeMap<SectionAddress, ObjSymbol> = BTreeMap::new();

    let dbi = dbfile.debug_information()?;

    // Parse symbols
    let global_symtable = dbfile.global_symbols()?;
    let mut all_syms: Vec<pdb2::Symbol> = vec![];

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
    let mut groups: Vec<CoffGroup> = vec![];
    let mut ldata_dupes: HashMap<String, u32> = HashMap::new();
    for symbol in all_syms_iter {
        match symbol.parse() {
            Ok(pdb2::SymbolData::Public(data)) => {
                if data.offset.section == 0 {
                    continue;
                }
                let symaddr = to_section_addr(&pdbmap, &data.offset);
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
                obj_sym.address = to_virtual_address(&pdbmap, section_addrs, &data.offset);
                obj_sym.section = Some(symaddr.section);
                obj_sym.flags = ObjSymbolFlagSet(ObjSymbolFlags::Global.into());
                obj_sym.kind =
                    if data.function { ObjSymbolKind::Function } else { ObjSymbolKind::Object };
                obj_sym.data_kind = ObjDataKind::Unknown;
            }
            Ok(pdb2::SymbolData::Data(data)) => {
                if data.offset.section == 0 {
                    continue;
                }
                let symaddr = to_section_addr(&pdbmap, &data.offset);
                let obj_sym = syms.entry(symaddr).or_default();

                // This is an S_GDATA32 or S_LDATA32 record
                if data.global {
                    obj_sym.flags.set_scope(ObjSymbolScope::Global);
                } else {
                    obj_sym.flags.set_scope(ObjSymbolScope::Local);
                    obj_sym.kind = ObjSymbolKind::Object;
                    // TODO: Now that we extract object files and splits, we can
                    // update this renaming so it is only done for repeat
                    // names of symbols in the same file
                    let name = data.name.to_string().clone();
                    let c =
                        *ldata_dupes.entry(name.to_string()).and_modify(|c| *c += 1).or_insert(1);
                    let name: String = if c > 1 {
                        format!("static_dup_{}_{}", c - 1, name)
                    } else {
                        data.name.to_string().into()
                    };
                    obj_sym.name = name;
                    obj_sym.address = to_virtual_address(&pdbmap, section_addrs, &data.offset);
                    obj_sym.section = Some(symaddr.section);
                }
                // TODO: We can also deduce the size by using the type
                // field to index into the TPI.
                // Build a TypeFinder, then use it to compute object sizes
                // while iterating through the data symbols.
                // See https://docs.rs/pdb2/latest/pdb2/struct.ItemInformation.html
            }
            Ok(pdb2::SymbolData::ThreadStorage(data)) => {
                if data.offset.section == 0 {
                    continue;
                }
                let symaddr = to_section_addr(&pdbmap, &data.offset);
                let obj_sym = syms.entry(symaddr).or_default();

                // This is an S_GTHREAD32 or S_LTHREAD32 record
                if data.global {
                    obj_sym.flags.set_scope(ObjSymbolScope::Global);
                } else {
                    obj_sym.flags.set_scope(ObjSymbolScope::Local);
                    obj_sym.kind = ObjSymbolKind::Object;
                    obj_sym.name = data.name.to_string().into();
                    obj_sym.address = to_virtual_address(&pdbmap, section_addrs, &data.offset);
                    obj_sym.section = Some(symaddr.section);
                }

                // TODO: Above note for DATA records also applies here
            }
            Ok(pdb2::SymbolData::Procedure(data)) => {
                if data.offset.section == 0 {
                    continue;
                }
                let symaddr = to_section_addr(&pdbmap, &data.offset);
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
                    obj_sym.address = to_virtual_address(&pdbmap, section_addrs, &data.offset);
                    obj_sym.section = Some(symaddr.section);
                }
            }
            Ok(pdb2::SymbolData::Thunk(data)) => {
                if data.offset.section == 0 {
                    continue;
                }
                let symaddr = to_section_addr(&pdbmap, &data.offset);
                let obj_sym = syms.entry(symaddr).or_default();

                // This is an S_THUNK32 record
                obj_sym.size = data.len as u64;
                obj_sym.size_known = true;
                obj_sym.align = Some(4);
            }
            Ok(pdb2::SymbolData::CoffGroup(data)) => groups.push(CoffGroup {
                address: to_virtual_address(&pdbmap, section_addrs, &data.offset),
                size: data.cb,
                name: data.name.to_string().into(),
                section: to_section_addr(&pdbmap, &data.offset).section,
            }),
            Ok(pdb2::SymbolData::Section(_data)) => {
                // TODO: We already have most section info from the EXE, but
                // S_SECTION records contain the unabbreviated section names,
                // which serve as an alternative solution for .embsec_ issues
            }
            Ok(_) => {}
            Err(pdb2::Error::UnimplementedSymbolKind(_)) => {
                warn_unsupported_sym_kind(&symbol, &mut unsupported_sym_kinds);
            }
            Err(parse_error) => {
                return Err(parse_error.into());
            }
        }
    }

    // Sort by address and append a sentinel
    groups.sort();
    groups.push(CoffGroup {
        address: groups[groups.len() - 1].address + groups[groups.len() - 1].size as u64,
        size: 0,
        name: "END".to_string(),
        section: u32::MAX,
    });
    log::debug!("COFF Sections");
    for sec in section_addrs.iter() {
        log::debug!("#{}: name = {}, addr = 0x{:X}", sec.0, sec.1.name, sec.1.address);
    }
    log::debug!("COFF Groups:");
    for grp in groups.iter() {
        log::debug!(
            "address: 0x{:X}, section: {}, size: 0x{:X}, name: {}",
            grp.address,
            grp.section,
            grp.size,
            grp.name
        );
    }

    // Begin parsing splits
    let mut splits_by_section: Vec<ObjSplits> = vec![];
    splits_by_section.resize_with(section_addrs.len() as usize, Default::default);

    let num_modules = dbi.modules()?.count().unwrap_or(0) as i32;

    let mut module_names: Vec<String> = vec![];
    for i in 0..num_modules {
        module_names.push(format!("module_{}.cpp", i));
    }

    // curr_grp will increase monotonically, since contributions are sorted
    let mut curr_grp = -1;
    let mut curr_mod = -1;
    let mut curr_split: &mut ObjSplit = &mut Default::default();

    let mut contribs = dbi.section_contributions()?;
    while let Some(contrib) = contribs.next()? {
        // TODO: Extract file names from the Sources substream to replace the
        // auto-generated names. Take only the base name, fix the extension,
        // and disambiguate identical names with a prefix
        let s_addr = to_section_addr(&pdbmap, &contrib.offset);
        let sec_idx = s_addr.section as usize;
        let start = section_addr_to_virtual_addr(section_addrs, &s_addr);
        let end = start + contrib.size as u64;
        let mod_idx = contrib.module as i32;

        let is_new_grp = start >= groups[(curr_grp + 1) as usize].address;
        let is_new_mod = mod_idx != curr_mod;
        if is_new_grp {
            // Skip empty groups
            loop {
                curr_grp += 1;
                if start < groups[(curr_grp + 1) as usize].address {
                    break;
                }
            }
        }

        if is_new_grp || is_new_mod {
            curr_mod = mod_idx;

            let mod_name = &module_names[mod_idx as usize];
            let rename = if groups[curr_grp as usize].name == section_addrs[sec_idx as u32].name {
                None
            } else {
                Some(groups[curr_grp as usize].name.clone())
            };

            // Get a mutable reference to the ObjSplit we just pushed, so
            // subsequent contributions to it can update its size
            curr_split = splits_by_section[sec_idx].push(start as u32, ObjSplit {
                unit: mod_name.clone(),
                end: end as u32,
                align: None,
                autogenerated: false,
                common: false,
                skip: false,
                rename: rename.clone(),
            });
        }
        // FIXME: This currently requires detect_objects=false to work.
        // Deducing exact object sizes from the PDB should fix this
        curr_split.end = end as u32;
    }

    for (i, splits) in splits_by_section.iter().enumerate() {
        log::debug!("Splits for section {}:", i);
        for split in splits.iter() {
            log::debug!(
                "From {}: 0x{:X} - 0x{:X}, rename {:?}",
                split.1.unit,
                split.0,
                split.1.end,
                split.1.rename
            );
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

    Ok((module_names, splits_by_section, addr_vec))
}
