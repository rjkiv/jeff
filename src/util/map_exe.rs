#![allow(dead_code)]
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fs::read_to_string,
    ops::Bound::{Excluded, Unbounded},
};

use anyhow::{Result, bail};
use typed_path::Utf8NativePathBuf;

use crate::{
    analysis::cfa::SectionAddress,
    obj::{
        ObjInfo, ObjSectionKind, ObjSplit, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags,
        ObjSymbolKind, ObjUnit,
    },
};
// SymbolRef: the symbol name, and the obj it came from

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExeSectionType {
    Code,
    Data,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExeSectionInfo {
    pub name: String,
    pub index: u32,
    pub offset: u32, // the section's offset within the index
    pub size: u32,
    pub section_type: ExeSectionType,
}

#[derive(Clone)]
pub struct ExeSymbolEntry {
    pub addr: u32,
    pub symbol: String,
    // what section is this symbol part of?
    pub section: SectionIdx,
    // what unit does this symbol belong to?
    pub unit: UnitIdx,
    pub is_function: bool,
    pub is_weak: bool, // denoted by the "i" in the symbol flags
    pub is_static: bool,
}

pub struct ExeObjUnit {
    pub name: String,
    // any other crap to add in the future goes in here
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct UnitIdx(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct SymbolIdx(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct SectionIdx(pub usize);

pub struct ExeMapInfo {
    pub preferred_load_addr: u32,
    // the different sections of the map
    pub sections: Vec<ExeSectionInfo>,
    // lookup for a section's name and its index into our sections Vec
    pub section_indices: HashMap<String, SectionIdx>,
    // units/obj names we find
    pub units: Vec<ExeObjUnit>,
    // lookup for a unit's name and its index into our units Vec
    pub unit_indices: HashMap<String, UnitIdx>,

    // pub unit_entries: MultiMap<String, SymbolRef>,
    // pub entry_references: MultiMap<SymbolRef, SymbolRef>,
    // pub entry_referenced_from: MultiMap<SymbolRef, SymbolRef>,
    // pub unit_references: MultiMap<SymbolRef, String>,
    // pub section_units: HashMap<String, Vec<(u32, String)>>,

    // a big vec of ALL the symbols we've found in the map
    pub symbols: Vec<ExeSymbolEntry>,
    // the symbols for a unit, indexed by section
    pub unit_symbols: BTreeMap<UnitIdx, BTreeMap<SectionIdx, Vec<SymbolIdx>>>,
    // the symbols for a section, indexed by their address in the exe
    // value is a Vec because of the potential of code merging
    pub section_symbols: BTreeMap<SectionIdx, BTreeMap<u32, Vec<SymbolIdx>>>,
}

impl Default for ExeMapInfo {
    fn default() -> Self {
        Self::new()
    }
}

impl ExeMapInfo {
    pub fn new() -> Self {
        ExeMapInfo {
            preferred_load_addr: 0,
            sections: Vec::new(),
            section_symbols: BTreeMap::new(),
            section_indices: HashMap::new(),
            symbols: Vec::new(),
            unit_indices: HashMap::new(),
            unit_symbols: BTreeMap::new(),
            units: Vec::new(),
        }
    }

    fn set_preferred_load_addr(&mut self, entry_point: u32) {
        self.preferred_load_addr = entry_point;
    }

    fn add_section(&mut self, section_parts: Vec<&str>) -> Result<()> {
        // section_parts: [0]: idx:offset, [1]: {size}H, [2]: name, [3]: type (we can ignore this)
        let name = String::from(section_parts[2]);
        let (index, offset) = {
            let idx_and_offset = section_parts[0].split(":").collect::<Vec<&str>>();
            (
                u32::from_str_radix(idx_and_offset[0], 16)?,
                u32::from_str_radix(idx_and_offset[1], 16)?,
            )
        };
        let size = {
            let size_str = section_parts[1].split("H").collect::<Vec<&str>>();
            u32::from_str_radix(size_str[0], 16)?
        };
        let section_index = SectionIdx(self.sections.len());
        self.section_indices.insert(name.clone(), section_index);
        self.section_symbols.insert(section_index, BTreeMap::new());
        self.sections.push(ExeSectionInfo {
            name,
            index,
            offset,
            size,
            section_type: match section_parts[3] {
                "CODE" => ExeSectionType::Code,
                "DATA" => ExeSectionType::Data,
                _ => unreachable!(),
            },
        });
        Ok(())
    }

    fn get_section_idx(&self, idx: u32, offset: u32) -> Result<SectionIdx> {
        for (sec_idx, sec) in self.sections.iter().enumerate() {
            if sec.index == idx && (offset >= sec.offset && offset < (sec.offset + sec.size))
                || (offset >= sec.offset && sec.size == 0 && sec.name == ".xedata")
            {
                return Ok(SectionIdx(sec_idx));
            }
        }
        bail!("index {}:{:#X} not found", idx, offset);
    }

    fn add_symbol(&mut self, symbol_parts: Vec<&str>, is_static: bool) -> Result<()> {
        let sym_name = String::from(symbol_parts[1]);
        // purposefully not adding unwind and catch names from the map into our obj
        // this is because in microsoft's never-ending brilliance,
        // two unwinds can have the same number, which will cause duplicate symbol entry conflicts,
        // and i don't want to deal with that
        if sym_name.starts_with("__unwind$") || sym_name.starts_with("__catch$") {
            return Ok(());
        }
        if sym_name.starts_with("__savegprlr_") || sym_name.starts_with("__restgprlr_") {
            return Ok(());
        }
        if sym_name.starts_with("__savefpr_") || sym_name.starts_with("__restfpr_") {
            return Ok(());
        }
        if sym_name.starts_with("__savevmx_") || sym_name.starts_with("__restvmx_") {
            return Ok(());
        }

        let sym_addr = u32::from_str_radix(symbol_parts[2], 16)?;
        let sym_section = {
            let idx_and_offset = symbol_parts[0].split(":").collect::<Vec<&str>>();
            let sec_idx = u32::from_str_radix(idx_and_offset[0], 16)?;
            let sec_offset = u32::from_str_radix(idx_and_offset[1], 16)?;
            self.get_section_idx(sec_idx, sec_offset)?
        };
        let flags_slice = &symbol_parts[3..symbol_parts.len() - 1];
        let unit = String::from(*symbol_parts.last().unwrap());
        let unit_idx = match self.unit_indices.get(&unit) {
            Some(idx) => *idx,
            None => {
                let unit_idx = UnitIdx(self.units.len());
                self.unit_indices.insert(unit.clone(), unit_idx);
                self.unit_symbols.insert(unit_idx, BTreeMap::new());
                self.units.push(ExeObjUnit { name: unit.clone() });
                unit_idx
            }
        };

        let symbol_idx = SymbolIdx(self.symbols.len());
        self.symbols.push(ExeSymbolEntry {
            addr: sym_addr,
            symbol: sym_name.clone(),
            section: sym_section,
            unit: unit_idx,
            is_function: flags_slice.contains(&"f"),
            is_weak: flags_slice.contains(&"i"),
            is_static,
        });
        // add this symbol idx to our unit_symbols
        self.unit_symbols
            .get_mut(&unit_idx)
            .expect("Unit should've been initialized at this point!")
            .entry(sym_section)
            .or_default()
            .push(symbol_idx);
        // add this symbol idx to our section symbols
        self.section_symbols
            .get_mut(&sym_section)
            .expect("Section should've been initialized at this point!")
            .entry(sym_addr)
            .or_default()
            .push(symbol_idx);
        Ok(())
    }

    fn debug_print(&self) {
        for (unit_idx, symbols_for_unit) in &self.unit_symbols {
            log::debug!("Symbols at unit {}", self.units[unit_idx.0].name);
            for (sec_idx, symbol_idxs) in symbols_for_unit {
                let mut msg = format!(
                    "\t{} ({:04}): ",
                    self.sections[sec_idx.0].name,
                    symbol_idxs.len()
                );
                for sym_idx in symbol_idxs {
                    let sym = &self.symbols[sym_idx.0];
                    msg += &*format!("{:08X}:{} ", sym.addr, sym.symbol.clone()).to_string();
                }
                log::debug!("{}", msg);
            }
        }
    }

    fn resolve_imps(&mut self) -> Result<()> {
        for symbols_by_address in self.section_symbols.values_mut() {
            for symbols in symbols_by_address.values_mut() {
                // if we've got a merged addr that contains an __imp, keep the __imp, dump everything else
                if symbols.len() > 1
                    && symbols
                        .iter()
                        .any(|s| self.symbols[s.0].symbol.starts_with("__imp_"))
                {
                    // println!("Merged imp at {:08X}!", addr);
                    symbols.retain(|s| self.symbols[s.0].symbol.starts_with("__imp_"));
                }
            }
        }
        Ok(())
    }
}

pub const PREFERRED_LOAD_ADDR_STR: &str = " Preferred load address is ";
pub const SECTION_STR: &str = " Start         Length     Name                   Class";
pub const ADDR_STR: &str =
    "  Address         Publics by Value              Rva+Base       Lib:Object";
pub const STATIC_SYM_STR: &str = " Static symbols";

pub enum ExeMapState {
    None,
    ReadingSections,
    ReadingSymbols,
    ReadingStaticSymbols,
}

pub fn apply_map_file_exe(path: &Utf8NativePathBuf, obj: &mut ObjInfo) -> Result<()> {
    let map_info = process_map_exe(path)?;
    apply_map_exe(map_info, obj)
}

pub fn is_reg_intrinsic(name: &str) -> bool {
    (name.contains("__save") || name.contains("__rest"))
        && (name.contains("gpr") || name.contains("fpr") || name.contains("vmx"))
}

pub fn apply_map_exe(result: ExeMapInfo, obj: &mut ObjInfo) -> Result<()> {
    // apply map symbols to ObjInfo
    // the good news: by this point, exception info and RTTI have been parsed/detected, and their symbols marked
    // so we can look for those and account for them when deducing .rdata sizes
    for symbols_by_address in result.section_symbols.values() {
        for (addr, symbols) in symbols_by_address {
            // we want to skip imps and save/restore reg intrinsics, since we'll find those ourselves later
            if symbols
                .iter()
                .any(|sym_idx| result.symbols[sym_idx.0].symbol.starts_with("__imp"))
            {
                continue;
            }
            // else, add to our ObjInfo
            let sym = {
                let mut sym = result.symbols[symbols[0].0].clone();
                if symbols.len() > 1 {
                    sym.symbol = format!("merged_{:08X}", sym.addr);
                }
                sym
            };
            match obj.sections.at_address(sym.addr) {
                Ok((sec_idx, sec)) => {
                    // if func came from pdata, DO NOT override the size
                    let the_sec_addr = SectionAddress::new(sec_idx, sym.addr);
                    let sym_to_add: ObjSymbol =
                        if let Some(info) = obj.pdata_funcs.get(&the_sec_addr) {
                            ObjSymbol {
                                name: sym.symbol,
                                address: sym.addr,
                                section: Some(sec_idx),
                                size: info.full_size,
                                size_known: true,
                                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                                kind: if sec.kind == ObjSectionKind::Code && sym.is_function {
                                    ObjSymbolKind::Function
                                } else {
                                    ObjSymbolKind::Object
                                },
                                ..Default::default()
                            }
                        } else if sym.symbol.starts_with("??_7") {
                            // if this sym is for a vftable...
                            let mut size_to_use: Option<u32> = None;
                            // if there's a "next addr" from this one in our map, AND we have a marked symbol at this address from our RTTI parsing
                            if let (Some((next_addr, _)), Some((_, obj_sym))) = (
                                symbols_by_address.range((Excluded(addr), Unbounded)).next(),
                                obj.symbols.at_section_address(sec_idx, sym.addr).next(),
                            ) {
                                // if we have, we need to get its size, and compare it against the deduced size from map
                                assert!(
                                    obj_sym.name.starts_with("??_7")
                                        || obj_sym.name.starts_with("VFTABLE_for_")
                                );
                                assert!(obj_sym.size_known);
                                // if deduced size from map < recorded size from symbol, overwrite it
                                let deduced_size_from_map = next_addr - sym.addr;
                                if deduced_size_from_map < obj_sym.size {
                                    log::debug!(
                                        "{:08X}: deduced size {:08X} < parsed size {:08X}!",
                                        sym.addr,
                                        deduced_size_from_map,
                                        obj_sym.size
                                    );
                                    size_to_use = Some(deduced_size_from_map);
                                }
                            }
                            ObjSymbol {
                                name: sym.symbol,
                                address: sym.addr,
                                section: Some(sec_idx),
                                size: size_to_use.unwrap_or(0),
                                size_known: size_to_use.is_some(),
                                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                                kind: ObjSymbolKind::Object, // vftables are not functions
                                ..Default::default()
                            }
                        } else if let Some(float_str) = sym.symbol.strip_prefix("__real@") {
                            // if this is a floating point value...
                            assert!(float_str.len() == 8 || float_str.len() == 16);
                            let size = float_str.len() as u32 / 2;
                            ObjSymbol {
                                name: sym.symbol,
                                address: sym.addr,
                                section: Some(sec_idx),
                                size,
                                size_known: true,
                                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                                kind: ObjSymbolKind::Object, // floats are not functions
                                ..Default::default()
                            }
                        } else if let Some(vmx_str) = sym.symbol.strip_prefix("__vmx@") {
                            // if this is a vmx value...
                            assert_eq!(vmx_str.len(), 32);
                            ObjSymbol {
                                name: sym.symbol,
                                address: sym.addr,
                                section: Some(sec_idx),
                                size: 16,
                                size_known: true,
                                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                                kind: ObjSymbolKind::Object, // vmx consts are not functions
                                ..Default::default()
                            }
                            // TODO: also mark down strings, as we can infer length from their symbols
                        } else {
                            ObjSymbol {
                                name: sym.symbol,
                                address: sym.addr,
                                section: Some(sec_idx),
                                // shoutout to MSVC maps for not providing sizes
                                size_known: false,
                                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                                kind: if sec.kind == ObjSectionKind::Code && sym.is_function {
                                    ObjSymbolKind::Function
                                } else {
                                    ObjSymbolKind::Object
                                },
                                ..Default::default()
                            }
                        };
                    obj.add_symbol(sym_to_add, true)?;
                }
                // if we couldn't find the section (like maybe it was stripped), just continue on
                Err(_) => continue,
            };
        }
    }

    fn fix_split_name(orig_name: String) -> String {
        let ret = orig_name.replace(":", "/");
        if orig_name.contains(".obj") {
            ret.replace(".obj", ".cpp")
        }
        // probably an import library
        else {
            // xapilib:xam.xex@21256.0+1861.0, for example
            let parts: Vec<&str> = ret.split(".").collect();
            String::from(parts[0]) + ".cpp"
        }
    }

    // BTreeMap outer u32 key = the SectionIndex for the ObjInfo
    // BTreeMap nested u32 key = the start addr of the split
    // BTreeMap nested value = the split
    // so, for each SectionIndex in the ObjInfo, here's a collection of start addresses for splits, and their corresponding split infos
    let mut deduced_obj_splits: BTreeMap<u32, BTreeMap<u32, ObjSplit>> = BTreeMap::new();
    let mut deduced_obj_units: HashSet<String> = HashSet::new();

    // identify split bounds and apply them to ObjInfo
    for (unit_idx, symbols_by_section) in &result.unit_symbols {
        let unit_name = &result.units[unit_idx.0].name;
        // log::debug!("Symbols at unit {}", unit_name);
        for (sec_idx, symbol_idxs) in symbols_by_section {
            let section_name = &result.sections[sec_idx.0].name;
            let mut addrs_for_this_section: BTreeSet<u32> = BTreeSet::new();
            let mut merged_addrs: BTreeSet<u32> = BTreeSet::new();
            let section_symbols = &result.section_symbols[sec_idx];
            for sym_idx in symbol_idxs {
                let sym = &result.symbols[sym_idx.0];
                let sym_addr = sym.addr;
                if section_symbols[&sym_addr].len() == 1 {
                    addrs_for_this_section.insert(sym_addr);
                } else {
                    merged_addrs.insert(sym_addr);
                }
            }
            for addr in merged_addrs {
                // log::debug!("\tMerged addr: {:08X}", addr);
                let prev_key = section_symbols
                    .range((Unbounded, Excluded(addr)))
                    .next_back();
                let next_key = section_symbols.range((Excluded(addr), Unbounded)).next();
                match (prev_key, next_key) {
                    // there's an adjacent address both in front of and behind this addr
                    (Some((prev_addr, prev_syms)), Some((next_addr, next_syms))) => {
                        // check the prev addr
                        // log::debug!("\tFor merged addr {:08X}, investigate prev addr {:08X} and next addr {:08X}", addr, prev_addr, next_addr);

                        // if the next addr has 1 entry
                        // and it's NOT our unit - stop, this isn't it
                        // and it IS our unit, qualifies, add it

                        // if either the prev or next addr is in our deduced addr bounds, add this one in
                        if addrs_for_this_section.contains(prev_addr)
                            || addrs_for_this_section.contains(next_addr)
                        {
                            addrs_for_this_section.insert(addr);
                        }
                        // if the prev addr over has one entry
                        else if prev_syms.len() == 1 {
                            // ...and it's at this unit, we can assume this is part of our TU, so add it
                            if result.symbols[prev_syms[0].0].unit == *unit_idx {
                                addrs_for_this_section.insert(addr);
                            } else {
                                // it's NOT our unit, this can't be part of our bounds
                                // log::debug!("\t\tDid NOT add");
                            }
                        }
                        // if the next addr over has one entry
                        else if next_syms.len() == 1 {
                            // ...and it's at this unit, we can assume this is part of our TU, so add it
                            if result.symbols[next_syms[0].0].unit == *unit_idx {
                                addrs_for_this_section.insert(addr);
                            } else {
                                // it's NOT our unit, this can't be part of our bounds
                                // log::debug!("\t\tDid NOT add");
                            }
                        } else {
                            // not sure what to do now, let's just not add it
                            // log::debug!("\t{:08X} needs further investigation! Did NOT add", addr);
                        }
                    }
                    // there's a previous address, but not a next one - this is the last one
                    (Some((prev_addr, prev_syms)), None) => {
                        // if the prev addr over has one entry, and it's at this unit, we can assume this is part of our TU, so add it
                        // alternatively, if the prev addr is already in our deduced addr bounds, we can assume this is part of our TU
                        if (prev_syms.len() == 1
                            && result.symbols[prev_syms[0].0].unit == *unit_idx)
                            || addrs_for_this_section.contains(prev_addr)
                        {
                            addrs_for_this_section.insert(addr);
                        } else {
                            // we can't reliably resolve this, just don't add it to our addr bounds then
                            // log::debug!("Couldn't resolve TU for addr {:08X}", addr);
                        }
                    }
                    // there's a next address, but not a previous one - this is the first one
                    (None, Some((next_addr, next_syms))) => {
                        // if the next addr over has one entry, and it's at this unit, we can assume this is part of our TU, so add it
                        // alternatively, if the next addr is already in our deduced addr bounds, we can assume this is part of our TU
                        if (next_syms.len() == 1
                            && result.symbols[next_syms[0].0].unit == *unit_idx)
                            || addrs_for_this_section.contains(next_addr)
                        {
                            addrs_for_this_section.insert(addr);
                        } else {
                            // we can't reliably resolve this, just don't add it to our addr bounds then
                            // log::debug!("Couldn't resolve TU for addr {:08X}", addr);
                        }
                    }
                    // this is the only addr in the section - i have no clue how this would even be possible
                    (None, None) => {
                        // log::debug!("Couldn't resolve TU for addr {:08X}", addr);
                    }
                };
            }
            // by this point, addrs_for_this_section should be our splits, we just need to deduce the size of the last addr

            // get a Vec of each contiguous address set
            // get the split end for each Vec - those are your splits
            let contiguous_bounds: Vec<(u32, u32)> = {
                let mut bounds: Vec<(u32, u32)> = vec![];
                let mut start: Option<u32> = None;
                let mut itr = addrs_for_this_section.iter().peekable();

                while let Some(addr) = itr.next() {
                    if start.is_none() {
                        start = Some(*addr);
                    }
                    match itr.peek() {
                        Some(next_addr_in_section) => {
                            // check if next addr is contiguous
                            let next_key =
                                section_symbols.range((Excluded(addr), Unbounded)).next();
                            match next_key {
                                Some((next_addr_from_sec_syms, _)) => {
                                    if *next_addr_in_section != next_addr_from_sec_syms {
                                        // not contiguous, mark the bounds and continue
                                        bounds.push((start.unwrap(), *addr));
                                        start = None;
                                    }
                                }
                                None => {
                                    unreachable!("this can't be the last addr in our section");
                                }
                            }
                        }
                        None => {
                            // addr is the last addr here
                            bounds.push((start.unwrap(), *addr));
                        }
                    };
                }
                bounds
            };

            if !contiguous_bounds.is_empty() {
                for (first, last) in &contiguous_bounds {
                    let split_end = {
                        let (sec_for_last_addr, _section) = obj.sections.at_address(*last)?;
                        let (_, sym_at_addr) = obj
                            .symbols
                            .at_section_address(sec_for_last_addr, *last)
                            .next()
                            .unwrap_or_else(|| {
                                panic!("No symbol at {}:{:08X}", sec_for_last_addr, last)
                            });

                        // if there's a known size for the last addr in our deduced bounds, this split ends at this sym's end
                        if sym_at_addr.size_known {
                            // we need to 4 byte align Type Descriptor ends
                            if sym_at_addr.name.starts_with("??_R0") {
                                last + sym_at_addr.size.next_multiple_of(4)
                            } else {
                                last + sym_at_addr.size
                            }
                        }
                        // else, deduce the end from our map
                        else {
                            match section_symbols.range((Excluded(last), Unbounded)).next() {
                                // there's a next addr over, its start is our split end
                                Some((next_addr, _)) => *next_addr,
                                // no next addr over, so the end of the map section is our split end
                                None => {
                                    // need the section size from the map, not from objinfo
                                    let sec = &result.sections[sec_idx.0];
                                    let obj_section =
                                        obj.sections.get(sec.index - 1).expect("where section");
                                    obj_section.address + sec.offset + sec.size
                                }
                            }
                        }
                    };
                    // let split_end = split_end.next_multiple_of(4);
                    // log::debug!(
                    //     "\t{}: Deduced bounds: {:08X} - {:08X}",
                    //     section_name,
                    //     first,
                    //     split_end
                    // );
                    let sec = &result.sections[sec_idx.0];
                    let target_sec_name = obj
                        .sections
                        .get(sec.index - 1)
                        .expect("where section")
                        .name
                        .clone();
                    let tu_name = fix_split_name(unit_name.clone());
                    deduced_obj_splits.entry(sec.index - 1).or_default().insert(
                        *first,
                        ObjSplit {
                            unit: tu_name.clone(),
                            end: split_end,
                            align: None,
                            common: false,
                            autogenerated: false,
                            skip: false,
                            rename: if *section_name != target_sec_name {
                                Some(section_name.clone())
                            } else {
                                None
                            },
                        },
                    );
                    deduced_obj_units.insert(tu_name.clone());
                }
            } else {
                // log::debug!("\t{}: No deducable bounds!", section_name);
                log::warn!(
                    "{}: Could not deduce bounds for section {}!",
                    unit_name,
                    section_name
                );
            }
        }
    }

    // sanity check/fix splits
    // TODO: also ensure splits don't end within symbols
    for splits_for_section in deduced_obj_splits.values_mut() {
        let mut keys_to_replace: Vec<(u32, u32)> = vec![];
        let mut itr = splits_for_section.iter().peekable();
        while let (Some((cur_split_start, cur_split)), Some((next_split_start, next_split))) =
            (itr.next(), itr.peek())
        {
            if cur_split.end > **next_split_start {
                log::warn!(
                    "Splits at {:08X}-{:08X} and {:08X}-{:08X} overlap!",
                    cur_split_start,
                    cur_split.end,
                    next_split_start,
                    next_split.end
                );
                keys_to_replace.push((**next_split_start, cur_split.end));
                // log::debug!(
                //     "Intending to replace {:08X} with {:08X}",
                //     next_split_start,
                //     cur_split.end
                // );
            }
        }
        for (old_key, new_key) in &keys_to_replace {
            let val = splits_for_section.remove(old_key).unwrap();
            splits_for_section.insert(*new_key, val);
            log::debug!(
                "\tReplaced split start {:08X} with {:08X}",
                old_key,
                new_key
            );
        }
    }

    for (objinfo_sec_idx, splits_for_section) in &deduced_obj_splits {
        let section = obj
            .sections
            .get_mut(*objinfo_sec_idx)
            .expect("where section");
        let section_name = section.name.clone();
        for (split_start_addr, split) in splits_for_section {
            let subsection_name = match &split.rename {
                Some(name) => name,
                None => &section_name,
            };
            log::debug!(
                "{} ({}): {:08X}-{:08X} (for {})",
                section_name,
                subsection_name,
                split_start_addr,
                split.end,
                split.unit.clone()
            );
            section.splits.push(*split_start_addr, split.clone());
        }
    }
    for unit in deduced_obj_units {
        obj.link_order.push(ObjUnit {
            name: unit,
            autogenerated: false,
            order: None,
        });
    }
    Ok(())
}

pub fn process_map_exe(map_path: &Utf8NativePathBuf) -> Result<ExeMapInfo> {
    println!("map: {}", map_path);

    let mut state = ExeMapState::None;
    let mut exe_map_info = ExeMapInfo::new();
    let mut must_read_syms = true;

    for line in read_to_string(map_path)?.lines() {
        if line.contains(PREFERRED_LOAD_ADDR_STR) {
            let entry_str = line.split(PREFERRED_LOAD_ADDR_STR).collect::<Vec<&str>>();
            assert_eq!(entry_str.len(), 2);
            exe_map_info.set_preferred_load_addr(u32::from_str_radix(entry_str[1], 16)?);
        } else if line == SECTION_STR {
            state = ExeMapState::ReadingSections;
            continue;
        } else if line == ADDR_STR {
            state = ExeMapState::ReadingSymbols;
            continue;
        } else if line == STATIC_SYM_STR {
            state = ExeMapState::ReadingStaticSymbols;
            must_read_syms = true;
            continue;
        }

        match state {
            ExeMapState::None => continue,
            ExeMapState::ReadingSections => {
                if line.is_empty() {
                    state = ExeMapState::None;
                } else {
                    let sec_parts = line.split_whitespace().collect::<Vec<&str>>();
                    assert_eq!(sec_parts.len(), 4);
                    exe_map_info.add_section(sec_parts)?;
                }
            }
            ExeMapState::ReadingSymbols => {
                if line.is_empty() {
                    if must_read_syms {
                        must_read_syms = false;
                        continue;
                    } else {
                        state = ExeMapState::None;
                        continue;
                    }
                }
                let symbol_parts = line.split_whitespace().collect::<Vec<&str>>();
                if symbol_parts[0].starts_with("0000:") {
                    continue;
                }
                exe_map_info.add_symbol(symbol_parts, false)?;
            }
            ExeMapState::ReadingStaticSymbols => {
                if line.is_empty() {
                    if must_read_syms {
                        must_read_syms = false;
                        continue;
                    } else {
                        state = ExeMapState::None;
                        continue;
                    }
                }
                let symbol_parts = line.split_whitespace().collect::<Vec<&str>>();
                exe_map_info.add_symbol(symbol_parts, true)?;
            }
        }
    }
    // exe_map_info.debug_print();
    exe_map_info.resolve_imps()?;
    Ok(exe_map_info)
}
