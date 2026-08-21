use std::{
    cmp::min,
    collections::BTreeMap,
    fmt::{Debug, Display, Formatter, UpperHex},
    ops::{Add, AddAssign, BitAnd, Sub},
};

use anyhow::{Context, Result, bail, ensure};
use itertools::Itertools;

use crate::{
    analysis::{
        skip_alignment,
        slices::{FunctionSlices, TailCallResult},
    },
    obj::{
        ObjInfo, ObjSectionKind, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind,
        SectionIndex,
    },
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SectionAddress {
    pub section: SectionIndex,
    pub address: u32,
}

impl Debug for SectionAddress {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{:#X}", self.section as isize, self.address)
    }
}

impl Display for SectionAddress {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{:#X}", self.section as isize, self.address)
    }
}

impl SectionAddress {
    pub fn new(section: SectionIndex, address: u32) -> Self { Self { section, address } }

    pub fn offset(self, offset: i32) -> Self {
        Self { section: self.section, address: self.address.wrapping_add_signed(offset) }
    }

    pub fn align_up(self, align: u32) -> Self {
        Self { section: self.section, address: (self.address + align - 1) & !(align - 1) }
    }

    pub fn align_down(self, align: u32) -> Self {
        Self { section: self.section, address: self.address & !(align - 1) }
    }

    pub fn is_aligned(self, align: u32) -> bool { self.address & (align - 1) == 0 }

    pub fn wrapping_add(self, rhs: u32) -> Self {
        Self { section: self.section, address: self.address.wrapping_add(rhs) }
    }
}

impl Add<u32> for SectionAddress {
    type Output = Self;

    fn add(self, rhs: u32) -> Self::Output {
        Self { section: self.section, address: self.address + rhs }
    }
}

impl Sub<u32> for SectionAddress {
    type Output = Self;

    fn sub(self, rhs: u32) -> Self::Output {
        Self { section: self.section, address: self.address - rhs }
    }
}

impl AddAssign<u32> for SectionAddress {
    fn add_assign(&mut self, rhs: u32) { self.address += rhs; }
}

impl UpperHex for SectionAddress {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{:#010X}", self.section as isize, self.address)
    }
}

impl BitAnd<u32> for SectionAddress {
    type Output = u32;

    fn bitand(self, rhs: u32) -> Self::Output { self.address & rhs }
}

#[derive(Default, Debug, Clone)]
pub struct FunctionInfo {
    pub analyzed: bool,
    pub end: Option<SectionAddress>,
    pub slices: Option<FunctionSlices>,
}

impl FunctionInfo {
    pub fn is_analyzed(&self) -> bool { self.analyzed }

    pub fn is_function(&self) -> bool {
        self.analyzed && self.end.is_some() && self.slices.is_some()
    }

    pub fn is_non_function(&self) -> bool {
        self.analyzed && self.end.is_none() && self.slices.is_none()
    }

    pub fn is_unfinalized(&self) -> bool {
        self.analyzed && self.end.is_none() && self.slices.is_some()
    }
}

#[derive(Debug, Default)]
pub struct AnalyzerState {
    pub functions: BTreeMap<SectionAddress, FunctionInfo>,
    pub jump_tables: BTreeMap<SectionAddress, u32>,
    pub known_symbols: BTreeMap<SectionAddress, Vec<ObjSymbol>>,
    pub known_sections: BTreeMap<SectionIndex, String>,
}

impl AnalyzerState {
    pub fn apply(&self, obj: &mut ObjInfo) -> Result<()> {
        for (&section_index, section_name) in &self.known_sections {
            obj.sections[section_index].rename(section_name.clone())?;
        }
        for (&start, FunctionInfo { end, .. }) in self.functions.iter() {
            let Some(end) = end else { continue };
            let section = &obj.sections[start.section];
            ensure!(
                section.contains_range(start.address..end.address),
                "Function {:#010X}..{:#010X} out of bounds of section {} {:#010X}..{:#010X}",
                start.address,
                end,
                section.name,
                section.address,
                section.address + section.size
            );
            let func_name = format!("fn_{:08X}", start.address);
            let sym_idx = obj.add_symbol(
                ObjSymbol {
                    name: func_name,
                    address: start.address,
                    section: Some(start.section),
                    size: end.address - start.address,
                    size_known: true,
                    kind: ObjSymbolKind::Function,
                    ..Default::default()
                },
                false,
            )?;
            let sym_addr = {
                let sym = &obj.symbols[sym_idx];
                SectionAddress::new(sym.section.unwrap(), sym.address as u32)
            };
            // obj.symbols[sym_idx].name gives the actual name of the function at start.address
            // use it to replace the names of symbols of corresponding __ehfuncinfo, except_data, __scopetable, etc
            // if this func has a C++ exception, add/replace ehfuncinfo symbols
            if let Some(info) = &obj.pdata_funcs.get(&sym_addr)
                && let Some(cxx_eh_func_info) = &info.exception_info
            {
                obj.symbols.add(
                    ObjSymbol {
                        name: format!("__ehfuncinfo${}", obj.symbols[sym_idx].name),
                        address: cxx_eh_func_info.addr.address,
                        section: Some(cxx_eh_func_info.addr.section),
                        // if this exception record has any try/catches, there's no extra 0 at the end
                        size: if cxx_eh_func_info.num_tries > 0 { 0x24 } else { 0x28 },
                        size_known: true,
                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                        kind: ObjSymbolKind::Object,
                        ..Default::default()
                    },
                    false,
                )?;
                if let Some((unwind_addr, num_unwinds)) = cxx_eh_func_info.unwind_map {
                    obj.symbols.add(
                        ObjSymbol {
                            name: format!("__unwindtable${}", obj.symbols[sym_idx].name),
                            address: unwind_addr.address,
                            section: Some(unwind_addr.section),
                            size: num_unwinds * 8,
                            size_known: true,
                            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                            kind: ObjSymbolKind::Object,
                            ..Default::default()
                        },
                        false,
                    )?;
                }
                if let Some(try_map_addr) = cxx_eh_func_info.try_map_addr {
                    obj.symbols.add(
                        ObjSymbol {
                            name: format!("__tryblocktable${}", obj.symbols[sym_idx].name),
                            address: try_map_addr.address,
                            section: Some(try_map_addr.section),
                            size: cxx_eh_func_info.num_tries * 0x14,
                            size_known: true,
                            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                            kind: ObjSymbolKind::Object,
                            ..Default::default()
                        },
                        false,
                    )?;
                }
                if let Some((addr, num_entries)) = cxx_eh_func_info.ip_to_state_map {
                    obj.symbols.add(
                        ObjSymbol {
                            name: format!("__iptostatemap${}", obj.symbols[sym_idx].name),
                            address: addr.address,
                            section: Some(addr.section),
                            size: num_entries * 8,
                            size_known: true,
                            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                            kind: ObjSymbolKind::Object,
                            ..Default::default()
                        },
                        false,
                    )?;
                }
            }
        }
        let mut iter = self.jump_tables.iter().peekable();
        while let Some((&addr, &(mut size))) = iter.next() {
            // Truncate overlapping jump tables
            if let Some(&(&next_addr, _)) = iter.peek()
                && next_addr.section == addr.section
            {
                size = min(size, next_addr.address - addr.address);
            }
            let section = &obj.sections[addr.section];
            ensure!(
                section.contains_range(addr.address..addr.address + size),
                "Jump table {:#010X}..{:#010X} out of bounds of section {} {:#010X}..{:#010X}",
                addr.address,
                addr.address + size,
                section.name,
                section.address,
                section.address + section.size
            );
            // because MSVC likes to stick absolute jump tables in the middle of functions,
            // and if we label those it'll cause conflicts with the function boundaries itself
            if section.kind != ObjSectionKind::Code {
                obj.add_symbol(
                    ObjSymbol {
                        name: format!("jumptable_{:08X}", addr.address),
                        address: addr.address,
                        section: Some(addr.section),
                        size,
                        size_known: true,
                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Local.into()),
                        kind: ObjSymbolKind::Object,
                        ..Default::default()
                    },
                    false,
                )?;
            }
        }
        for (&_addr, symbols) in &self.known_symbols {
            for symbol in symbols {
                // Remove overlapping symbols
                if symbol.size > 0 {
                    let end = symbol.address + symbol.size;
                    let overlapping = obj
                        .symbols
                        .for_section_range(symbol.section.unwrap(), symbol.address + 1..end)
                        .filter(|(_, s)| s.kind == symbol.kind)
                        .map(|(a, _)| a)
                        .collect_vec();
                    for index in overlapping {
                        let existing = &obj.symbols[index];
                        let symbol = ObjSymbol {
                            name: format!("__DELETED_{}", existing.name),
                            kind: ObjSymbolKind::Unknown,
                            size: 0,
                            flags: ObjSymbolFlagSet(
                                ObjSymbolFlags::RelocationIgnore
                                    | ObjSymbolFlags::NoWrite
                                    | ObjSymbolFlags::NoExport
                                    | ObjSymbolFlags::Stripped,
                            ),
                            ..existing.clone()
                        };
                        obj.symbols.replace(index, symbol)?;
                    }
                }
                obj.add_symbol(symbol.clone(), true)?;
            }
        }
        Ok(())
    }

    pub fn detect_functions(&mut self, obj: &ObjInfo) -> Result<()> {
        // Apply known functions from pdata/import data
        for (&addr, &size) in &obj.known_functions {
            self.functions.insert(addr, FunctionInfo {
                analyzed: false,
                end: size.map(|size| addr + size),
                slices: None,
            });
        }

        // Apply known functions from symbols
        for (_, symbol) in obj.symbols.by_kind(ObjSymbolKind::Function) {
            let Some(section_index) = symbol.section else { continue };
            let addr_ref = SectionAddress::new(section_index, symbol.address);
            self.functions.insert(addr_ref, FunctionInfo {
                analyzed: false,
                end: if symbol.size_known { Some(addr_ref + symbol.size) } else { None },
                slices: None,
            });
        }

        // Also check the beginning of every code section
        for (section_index, section) in obj.sections.by_kind(ObjSectionKind::Code) {
            let this_sec_start = SectionAddress::new(section_index, section.address);
            if !obj.exception_data_infos.contains(&this_sec_start) {
                self.functions.entry(this_sec_start).or_default();
            }
        }

        // Process known functions first
        for addr in self.functions.keys().cloned().collect_vec() {
            self.process_function_at(obj, addr)?;
            // originally, I placed some assertions here to verify CFA reached the expected end
            // what I failed to consider is that functions may need multiple passes to reach that end.
            // so, some functions that had possible tail calls were ending CFA early on their first run, causing these to falsely fail.
        }

        // the rest...
        println!("Known functions complete.");

        if let Some(entry) = obj.entry {
            // Locate entry function bounds
            let (section_index, _) = obj
                .sections
                .at_address(entry)
                .context(format!("Entry point {entry:#010X} outside of any section"))?;
            self.process_function_at(obj, SectionAddress::new(section_index, entry))?;
        }
        // Locate bounds for referenced functions until none are left
        self.process_functions(obj)?;
        // Final pass(es)
        println!("Running final passes...\n");
        while self.finalize_functions(obj, true)? {
            self.process_functions(obj)?;
        }
        if self.functions.iter().any(|(_, i)| i.is_unfinalized()) {
            log::error!("Failed to finalize functions:");
            for (addr, info) in self.functions.iter().filter(|(_, i)| i.is_unfinalized()) {
                log::error!(
                    "  {:#010X}: blocks [{:?}]",
                    addr,
                    info.slices.as_ref().unwrap().possible_blocks.keys()
                );
            }
            bail!("Failed to finalize functions");
        }
        Ok(())
    }

    fn finalize_functions(&mut self, obj: &ObjInfo, finalize: bool) -> Result<bool> {
        let mut finalized_any = false;
        let unfinalized = self
            .functions
            .iter()
            .filter_map(|(&addr, info)| {
                if info.is_unfinalized() { info.slices.clone().map(|s| (addr, s)) } else { None }
            })
            .collect_vec();
        for (addr, mut slices) in unfinalized {
            // log::info!("Trying to finalize {:#010X}", addr);
            let Some(function_start) = slices.start() else {
                bail!("Function slice without start @ {:#010X}", addr);
            };
            let function_end = slices.end();
            let mut current = SectionAddress::new(addr.section, 0);
            while let Some((&block, vm)) = slices.possible_blocks.range(current..).next() {
                current = block + 4;
                let vm = vm.clone();
                match slices.check_tail_call(
                    obj,
                    block,
                    function_start,
                    function_end,
                    &self.functions,
                    Some(vm.clone()),
                ) {
                    TailCallResult::Not => {
                        log::trace!("Finalized block @ {:#010X}", block);
                        slices.possible_blocks.remove(&block);
                        slices.analyze(
                            obj,
                            block,
                            function_start,
                            function_end,
                            &self.functions,
                            Some(vm),
                        )?;
                        // Start at the beginning of the function again
                        current = SectionAddress::new(addr.section, 0);
                    }
                    TailCallResult::Is => {
                        log::trace!("Finalized tail call @ {:#010X}", block);
                        slices.possible_blocks.remove(&block);
                        slices.function_references.insert(block);
                        // Start at the beginning of the function again
                        current = SectionAddress::new(addr.section, 0);
                    }
                    TailCallResult::Possible => {
                        if finalize {
                            log::trace!(
                                "Still couldn't determine {:#010X}, assuming non-tail-call",
                                block
                            );
                            slices.possible_blocks.remove(&block);
                            slices.analyze(
                                obj,
                                block,
                                function_start,
                                function_end,
                                &self.functions,
                                Some(vm),
                            )?;
                        }
                    }
                    TailCallResult::Error(e) => return Err(e),
                }
            }
            if slices.can_finalize() {
                log::trace!("Finalizing {:#010X}", addr);
                slices.finalize(obj, &self.functions)?;
                for address in slices.function_references.iter().cloned() {
                    // Only create functions for code sections
                    // Some games use branches to data sections to prevent dead stripping (Mario Party)
                    if matches!(obj.sections.get(address.section), Some(section) if section.kind == ObjSectionKind::Code)
                    {
                        self.functions.entry(address).or_default();
                    }
                }
                self.jump_tables.append(&mut slices.jump_table_references.clone());
                for label in slices.special_jump_table_labels.iter() {
                    self.known_symbols.entry(*label).or_default().push(ObjSymbol {
                        name: format!("$LN{:X}", label.address),
                        address: label.address,
                        section: Some(label.section),
                        size_known: true,
                        flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                        ..Default::default()
                    })
                }
                let end = slices.end();
                let info = self.functions.get_mut(&addr).unwrap();
                info.analyzed = true;
                info.end = end;
                info.slices = Some(slices.clone());
                finalized_any = true;
            }
        }
        Ok(finalized_any)
    }

    fn first_unbounded_function(&self) -> Option<SectionAddress> {
        self.functions.iter().find(|(_, info)| !info.is_analyzed()).map(|(&addr, _)| addr)
    }

    fn process_functions(&mut self, obj: &ObjInfo) -> Result<()> {
        loop {
            match self.first_unbounded_function() {
                Some(addr) => {
                    log::trace!("Processing {:#010X}", addr);
                    self.process_function_at(obj, addr)?;
                }
                None => {
                    if !self.finalize_functions(obj, false)? && !self.detect_new_functions(obj)? {
                        break;
                    }
                }
            }
        }
        Ok(())
    }

    pub fn process_function_at(&mut self, obj: &ObjInfo, addr: SectionAddress) -> Result<bool> {
        Ok(if let Some(mut slices) = self.process_function(obj, addr)? {
            for address in slices.function_references.iter().cloned() {
                // Only create functions for code sections
                // Some games use branches to data sections to prevent dead stripping (Mario Party)
                if matches!(obj.sections.get(address.section), Some(section) if section.kind == ObjSectionKind::Code)
                {
                    self.functions.entry(address).or_default();
                }
            }
            self.jump_tables.append(&mut slices.jump_table_references.clone());
            for label in slices.special_jump_table_labels.iter() {
                self.known_symbols.entry(*label).or_default().push(ObjSymbol {
                    name: format!("$LN{:X}", label.address),
                    address: label.address,
                    section: Some(label.section),
                    flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                    ..Default::default()
                })
            }
            for label in slices.special_catch_labels.iter() {
                self.known_symbols.entry(*label).or_default().push(ObjSymbol {
                    name: format!("$LN{:X}", label.address),
                    address: label.address,
                    section: Some(label.section),
                    flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                    ..Default::default()
                })
            }
            if slices.can_finalize() {
                slices.finalize(obj, &self.functions)?;
                let info = self.functions.entry(addr).or_default();
                info.analyzed = true;
                info.end = slices.end();
                info.slices = Some(slices);
            } else {
                let info = self.functions.entry(addr).or_default();
                info.analyzed = true;
                info.end = None;
                info.slices = Some(slices);
            }
            true
        } else {
            log::info!("Not a function @ {:#010X}", addr);
            let info = self.functions.entry(addr).or_default();
            info.analyzed = true;
            info.end = None;
            false
        })
    }

    fn process_function(
        &mut self,
        obj: &ObjInfo,
        start: SectionAddress,
    ) -> Result<Option<FunctionSlices>> {
        let mut slices = FunctionSlices::default();
        let function_end = self.functions.get(&start).and_then(|info| info.end);

        // if there are exception structures coming after the main function, analyze those first
        if let Some(info) = obj.pdata_funcs.get(&start) {
            for (handler_start, handler_size) in &info.handlers {
                // FIXME: C funcs with excepts currently have a broken bl reloc
                if !slices.analyze(
                    obj,
                    *handler_start,
                    start,
                    Some(*handler_start + *handler_size),
                    &self.functions,
                    None,
                )? {
                    return Ok(None);
                }
            }
        }
        // finally, analyze the main function
        if !slices.analyze(obj, start, start, function_end, &self.functions, None)? {
            return Ok(None);
        }

        Ok(Some(slices))
    }

    fn detect_new_functions(&mut self, obj: &ObjInfo) -> Result<bool> {
        let mut new_functions = vec![];
        let mut truncations: Vec<(SectionAddress, SectionAddress)> = vec![];
        // 1. the start of the C func; 2. the false "func" to remove from self.functions; 3. the known end of the C func
        // false "funcs" come from funcs with C exception handlers, because microsoft likes to bl to them rather than b
        let mut c_exception_truncations: Vec<(SectionAddress, SectionAddress, SectionAddress)> =
            vec![];
        for (section_index, section) in obj.sections.by_kind(ObjSectionKind::Code) {
            if section.name == ".xidata" {
                continue;
            } // because we already did our xidata processing at this point
            let section_start = SectionAddress::new(section_index, section.address);
            let section_end = section_start + section.size;
            let mut iter = self.functions.range(section_start..section_end).peekable();
            loop {
                match (iter.next(), iter.peek()) {
                    (Some((&first, first_info)), Some(&(&second, second_info))) => {
                        let Some(first_end) = first_info.end else { continue };
                        if first_end > second {
                            // if first is a C func with excepts, and the second is not
                            if let Some(first_info) = obj.pdata_funcs.get(&first)
                                && !obj.pdata_funcs.contains_key(&second)
                            {
                                let max_except_end = first + first_info.full_size;
                                // if second is within the bounds of first (a C func with exception handling) and max_except_end (the known max end of said C func),
                                // delete it, and set first's end to max end
                                if first <= second && second < max_except_end {
                                    assert_eq!(
                                        first_end, max_except_end,
                                        "Expected end {:?}, calculated end {:?}",
                                        max_except_end, first
                                    );
                                    c_exception_truncations.push((first, second, max_except_end));
                                    continue;
                                }
                            }
                            log::warn!(
                                "Overlapping functions {}-{} -> {}, truncating end of {}",
                                first,
                                first_end,
                                second,
                                first
                            );
                            truncations.push((first, second));
                            continue;
                        }
                        let addr = match skip_alignment(section, first_end, second) {
                            Some(addr) => addr,
                            None => continue,
                        };
                        if second > addr {
                            // don't try to add a function where there's an exception symbol
                            if obj.exception_data_infos.contains(&addr) {
                                continue;
                            }
                            log::trace!(
                                "Trying function @ {:#010X} (from {:#010X}-{:#010X} <-> {:#010X}-{:#010X?})",
                                addr,
                                first.address,
                                first_end,
                                second.address,
                                second_info.end,
                            );
                            new_functions.push(addr);
                        }
                    }
                    (Some((last, last_info)), None) => {
                        let Some(last_end) = last_info.end else { continue };
                        if last_end < section_end {
                            let addr = match skip_alignment(section, last_end, section_end) {
                                Some(addr) => addr,
                                None => continue,
                            };
                            if addr < section_end {
                                log::trace!(
                                    "Trying function @ {:#010X} (from {:#010X}-{:#010X} <-> {:#010X})",
                                    addr,
                                    last.address,
                                    last_end,
                                    section_end,
                                );
                                new_functions.push(addr);
                            }
                        }
                    }
                    _ => break,
                }
            }
        }
        // TODO: looking at .objs in objdiff, the SectionAddress corresponding with fake_func has a b to 0
        // Need an actual C with exceptions source-compiled .obj to use as a ground truth/reference
        for (c_func, fake_func, c_func_len) in c_exception_truncations {
            self.functions.remove(&fake_func);
            if let Some(c_func) = self.functions.get_mut(&c_func) {
                c_func.end = Some(c_func_len);
            }
        }

        let found_new = !new_functions.is_empty() || !truncations.is_empty();
        for (fn_addr, new_end) in truncations {
            if let Some(info) = self.functions.get_mut(&fn_addr) {
                info.end = Some(new_end);
            }
        }
        for addr in new_functions {
            let opt = self.functions.insert(addr, FunctionInfo::default());
            ensure!(opt.is_none(), "Attempted to detect duplicate function @ {:#010X}", addr);
        }
        Ok(found_new)
    }
}

#[cfg(test)]
#[path = "cfa_tests.rs"]
mod cfa_tests;
