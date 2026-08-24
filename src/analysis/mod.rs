use std::{collections::BTreeSet, num::NonZeroU32};

use anyhow::{Context, Result, bail, ensure};
use powerpc::{Extensions, Ins};

use crate::{
    analysis::{cfa::SectionAddress, vm::JumpTableType},
    array_ref,
    obj::{ObjInfo, ObjRelocKind, ObjSection, ObjSectionKind, ObjSymbolKind},
};

pub mod cfa;
pub mod executor;
pub mod libcmt;
pub mod objects;
pub mod pass;
pub mod rtti;
pub mod seh;
pub mod slices;
pub mod tracker;
pub mod vm;

pub fn disassemble(section: &ObjSection, address: u32) -> Option<Ins> {
    read_u32(section, address).map(|v| Ins::new(v, Extensions::xenon()))
}

pub fn read_u32(section: &ObjSection, address: u32) -> Option<u32> {
    let offset = (address - section.address) as usize;
    if section.data.len() < offset + 4 {
        return None;
    }
    Some(u32::from_be_bytes(*array_ref!(section.data, offset, 4)))
}

fn read_relocation_address(
    obj: &ObjInfo,
    section: &ObjSection,
    address: u32,
    reloc_kind: Option<ObjRelocKind>,
) -> Result<Option<RelocationTarget>> {
    let Some(reloc) = section.relocations.at(address) else {
        return Ok(None);
    };
    if let Some(reloc_kind) = reloc_kind {
        ensure!(reloc.kind == reloc_kind);
    }
    let symbol = &obj.symbols[reloc.target_symbol];
    let Some(section_index) = symbol.section else {
        return Ok(Some(RelocationTarget::External));
    };
    Ok(Some(RelocationTarget::Address(SectionAddress {
        section: section_index,
        address: (symbol.address as i64 + reloc.addend) as u32,
    })))
}

fn is_valid_jump_table_addr(
    obj: &ObjInfo,
    addr: SectionAddress,
    jump_table_type: JumpTableType,
) -> bool {
    match jump_table_type {
        JumpTableType::Absolute => {
            let kind = obj.sections[addr.section].kind;
            kind == ObjSectionKind::Code && kind != ObjSectionKind::Bss
        }
        _ => !matches!(
            obj.sections[addr.section].kind,
            ObjSectionKind::Code | ObjSectionKind::Bss
        ),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelocationTarget {
    Address(SectionAddress),
    External,
}

#[inline(never)]
pub fn relocation_target_for(
    obj: &ObjInfo,
    addr: SectionAddress,
    reloc_kind: Option<ObjRelocKind>,
) -> Result<Option<RelocationTarget>> {
    let section = &obj.sections[addr.section];
    read_relocation_address(obj, section, addr.address, reloc_kind)
}

fn get_jump_table_entries_impl(
    obj: &ObjInfo,
    addr: SectionAddress, // the address the jump table is at
    jump_table_type: JumpTableType,
    size: Option<NonZeroU32>,
    from: SectionAddress, // the address of the bctr that uses the jump table
    function_start: SectionAddress,
    function_end: Option<SectionAddress>,
) -> Result<(Vec<SectionAddress>, u32)> {
    let section = &obj.sections[addr.section];
    match jump_table_type {
        JumpTableType::Absolute => {
            // the start of the jump table should be IMMEDIATELY after the bctr
            assert_eq!(
                from + 4,
                addr,
                "Absolute jump table did not start immediately after the bctr at {}!",
                from
            );
            let mut entries: Vec<SectionAddress> = Vec::new();
            let mut min_entry_addr: Option<u32> = None;
            let mut data = section.data_range(addr.address, section.address + section.size)?;
            let mut cur_addr = addr;
            loop {
                let entry_addr = u32::from_be_bytes(*array_ref!(data, 0, 4));
                // if function end is some:
                // entry_addr must be within known function bounds
                // else (function end is none):
                // entry_addr must be >= the function's start,
                // AND we must also not have hit the earliest address in our parsed entries so far
                if match function_end {
                    Some(function_end) => {
                        entry_addr >= function_start.address && entry_addr < function_end.address
                    }
                    None => {
                        entry_addr >= function_start.address
                            && min_entry_addr.is_none_or(|a| cur_addr.address < a)
                    }
                } {
                    let (section_index, _) =
                        obj.sections.at_address(entry_addr).with_context(|| {
                            format!(
                                "Invalid jump table entry {entry_addr:#010X} at {cur_addr:#010X}"
                            )
                        })?;
                    entries.push(SectionAddress::new(section_index, entry_addr));
                    min_entry_addr = Some(min_entry_addr.unwrap_or(entry_addr).min(entry_addr));
                } else {
                    break;
                }
                data = &data[4..];
                cur_addr += 4;
            }
            let size = cur_addr.address - addr.address;
            log::debug!(
                "Inferred absolute jump table @ {:#010X} with entry count {} (from {:#010X})",
                addr,
                size / 4,
                from
            );
            Ok((entries, size))
        }
        JumpTableType::RelativeBytes { target, multiplier } => {
            // Check for an existing symbol with a known size, and use that if available.
            // Allows overriding jump table size analysis.
            let known_size = obj
                .symbols
                .kind_at_section_address(addr.section, addr.address, ObjSymbolKind::Object)
                .ok()
                .flatten()
                .and_then(|(_, s)| {
                    if s.size_known {
                        NonZeroU32::new(s.size)
                    } else {
                        None
                    }
                });
            if let Some(size) = known_size.or(size).map(|n| n.get()) {
                log::trace!(
                    "Located jump table @ {:#010X} with entry count {} (from {:#010X})",
                    addr,
                    size,
                    from
                );
                let mut entries = Vec::with_capacity(size as usize);
                let mut data = section.data_range(addr.address, addr.address + size)?;
                let mut cur_addr = addr;
                loop {
                    if data.is_empty() {
                        break;
                    }
                    if let Some(target) =
                        relocation_target_for(obj, cur_addr, Some(ObjRelocKind::Absolute))?
                    {
                        match target {
                            RelocationTarget::Address(addr) => entries.push(addr),
                            RelocationTarget::External => {
                                bail!(
                                    "Jump table entry at {:#010X} points to external symbol",
                                    cur_addr
                                )
                            }
                        }
                    } else {
                        assert!(
                            target.is_some(),
                            "We need a target address to apply offsets to!"
                        );
                        let target = match target.unwrap() {
                            RelocationTarget::Address(addr) => addr,
                            _ => {
                                panic!("We need a target address to apply offsets to!")
                            }
                        };
                        let entry_addr = target.address
                            + (u8::from_be_bytes(*array_ref!(data, 0, 1)) as usize * multiplier)
                                as u32;
                        if entry_addr > 0 {
                            let (section_index, _) =
                                obj.sections.at_address(entry_addr).with_context(|| {
                                    format!(
                                        "Invalid jump table entry {entry_addr:#010X} at {cur_addr:#010X}"
                                    )
                                })?;
                            entries.push(SectionAddress::new(section_index, entry_addr));
                        }
                    }
                    data = &data[1..];
                    cur_addr += 4;
                }
                Ok((entries, size))
            } else {
                // TODO: this is a hack courtesy of jeff 0.1.0
                // Although the jump table code is a lot more robust, there are still cases where we don't definitively know the jump table size.
                // When this happens, just set the jump table size to 0 and move on.
                // While this does mean you miss out on CFA from the potential addresses in the jump table,
                // the size will ultimately sort itself out when rebuilding relocs.
                let entries: Vec<SectionAddress> = Vec::new();
                log::debug!(
                    "Guessed jump table @ {:#010X} with entry count {} (from {:#010X})",
                    addr,
                    0,
                    from
                );
                Ok((entries, 0))
            }
            // target = the first addr immediately after the bctr
            // multiplier = how much to multiply each entry in the jump table by
        }
        JumpTableType::RelativeShorts {
            target,
            multiplier: _,
        } => {
            // Check for an existing symbol with a known size, and use that if available.
            // Allows overriding jump table size analysis.
            let known_size = obj
                .symbols
                .kind_at_section_address(addr.section, addr.address, ObjSymbolKind::Object)
                .ok()
                .flatten()
                .and_then(|(_, s)| {
                    if s.size_known {
                        NonZeroU32::new(s.size)
                    } else {
                        None
                    }
                });
            if let Some(size) = known_size.or(size).map(|n| n.get()) {
                log::trace!(
                    "Located jump table @ {:#010X} with entry count {} (from {:#010X})",
                    addr,
                    size / 2,
                    from
                );
                let mut entries = Vec::with_capacity(size as usize / 2);
                let mut data = section.data_range(addr.address, addr.address + size)?;
                let mut cur_addr = addr;
                loop {
                    if data.is_empty() {
                        break;
                    }
                    if let Some(target) =
                        relocation_target_for(obj, cur_addr, Some(ObjRelocKind::Absolute))?
                    {
                        match target {
                            RelocationTarget::Address(addr) => entries.push(addr),
                            RelocationTarget::External => {
                                bail!(
                                    "Jump table entry at {:#010X} points to external symbol",
                                    cur_addr
                                )
                            }
                        }
                    } else {
                        assert!(
                            target.is_some(),
                            "We need a target address to apply offsets to!"
                        );
                        let target = match target.unwrap() {
                            RelocationTarget::Address(addr) => addr,
                            _ => {
                                panic!("We need a target address to apply offsets to!")
                            }
                        };
                        let entry_addr =
                            target.address + u16::from_be_bytes(*array_ref!(data, 0, 2)) as u32;
                        if entry_addr > 0 {
                            let (section_index, _) =
                                obj.sections.at_address(entry_addr).with_context(|| {
                                    format!(
                                        "Invalid jump table entry {entry_addr:#010X} at {cur_addr:#010X}"
                                    )
                                })?;
                            entries.push(SectionAddress::new(section_index, entry_addr));
                        }
                    }
                    data = &data[2..];
                    cur_addr += 4;
                }
                Ok((entries, size))
            } else {
                // TODO: this is a hack courtesy of jeff 0.1.0
                // Although the jump table code is a lot more robust, there are still cases where we don't definitively know the jump table size.
                // When this happens, just set the jump table size to 0 and move on.
                // While this does mean you miss out on CFA from the potential addresses in the jump table,
                // the size will ultimately sort itself out when rebuilding relocs.
                let entries: Vec<SectionAddress> = Vec::new();
                log::debug!(
                    "Guessed jump table @ {:#010X} with entry count {} (from {:#010X})",
                    addr,
                    0,
                    from
                );
                Ok((entries, 0))
            }
        }
    }
}

// Returns a Vec of every found jump table entry and its size, instead of unique entries like previous iterations.
// This is because for absolute jump tables, we need to add Absolute relocs for each entry.
// If you just need the unique entries, call BTreeSet::from_iter.
pub fn get_jump_table_entries(
    obj: &ObjInfo,
    addr: SectionAddress, // the address the jump table is at
    jump_table_type: JumpTableType,
    size: Option<NonZeroU32>,
    from: SectionAddress, // the address of the bctr that uses the jump table
    function_start: SectionAddress,
    function_end: Option<SectionAddress>,
) -> Result<(Vec<SectionAddress>, u32)> {
    if !is_valid_jump_table_addr(obj, addr, jump_table_type) {
        return Ok((Vec::new(), 0));
    }
    get_jump_table_entries_impl(
        obj,
        addr,
        jump_table_type,
        size,
        from,
        function_start,
        function_end,
    )
    .with_context(|| format!("While fetching jump table entries starting at {addr:#010X}"))
}

pub fn uniq_jump_table_entries(
    obj: &ObjInfo,
    addr: SectionAddress, // the address the jump table is at
    jump_table_type: JumpTableType,
    size: Option<NonZeroU32>,
    from: SectionAddress, // the address of the bctr that uses the jump table
    function_start: SectionAddress,
    function_end: Option<SectionAddress>,
) -> Result<(BTreeSet<SectionAddress>, u32)> {
    if !is_valid_jump_table_addr(obj, addr, jump_table_type) {
        return Ok((BTreeSet::new(), 0));
    }
    let (entries, size) = get_jump_table_entries_impl(
        obj,
        addr,
        jump_table_type,
        size,
        from,
        function_start,
        function_end,
    )
    .with_context(|| format!("While fetching jump table entries starting at {addr:#010X}"))?;
    Ok((BTreeSet::from_iter(entries.iter().cloned()), size))
}

pub fn skip_alignment(
    section: &ObjSection,
    mut addr: SectionAddress,
    end: SectionAddress,
) -> Option<SectionAddress> {
    let mut data = match section.data_range(addr.address, end.address) {
        Ok(data) => data,
        Err(_) => return None,
    };
    loop {
        if data.is_empty() {
            break None;
        }
        if data[0..4] == [0u8; 4] {
            addr += 4;
            data = &data[4..];
        } else {
            break Some(addr);
        }
    }
}
