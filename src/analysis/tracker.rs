use std::{
    collections::{BTreeMap, BTreeSet},
    mem::take,
};

use anyhow::{Result, bail};
use powerpc::Opcode;
use tracing::{debug_span, info_span};
use tracing_attributes::instrument;

use crate::{
    analysis::{
        RelocationTarget,
        cfa::SectionAddress,
        executor::{ExecCbData, ExecCbResult, Executor},
        get_jump_table_entries, read_u32, relocation_target_for,
        vm::{BranchTarget, GprValue, StepResult, VM},
    },
    obj::{
        ObjDataKind, ObjInfo, ObjKind, ObjReloc, ObjRelocKind, ObjSection, ObjSectionKind,
        ObjSymbol, ObjSymbolKind, SectionIndex,
    },
};

#[derive(Debug, Copy, Clone)]
pub enum Relocation {
    Ha(RelocationTarget),
    Hi(RelocationTarget),
    Lo(RelocationTarget),
    Sda21(RelocationTarget),
    Rel14(RelocationTarget),
    Rel24(RelocationTarget),
    Absolute(RelocationTarget),
}

impl Relocation {
    fn kind_and_address(&self) -> Option<(ObjRelocKind, SectionAddress)> {
        let (reloc_kind, target) = match self {
            Relocation::Ha(v) => (ObjRelocKind::PpcAddr16Ha, v),
            Relocation::Hi(v) => (ObjRelocKind::PpcAddr16Hi, v),
            Relocation::Lo(v) => (ObjRelocKind::PpcAddr16Lo, v),
            Relocation::Sda21(v) => (ObjRelocKind::PpcEmbSda21, v),
            Relocation::Rel14(v) => (ObjRelocKind::PpcRel14, v),
            Relocation::Rel24(v) => (ObjRelocKind::PpcRel24, v),
            Relocation::Absolute(v) => (ObjRelocKind::Absolute, v),
        };
        match *target {
            RelocationTarget::Address(address) => Some((reloc_kind, address)),
            RelocationTarget::External => None,
        }
    }
}

#[derive(Debug)]
pub enum DataKind {
    Unknown = -1,
    Word,
    Half,
    Byte,
    Float,
    Double,
    // String,
    // String16,
}

pub struct Tracker {
    processed_functions: BTreeSet<SectionAddress>,
    pub relocations: BTreeMap<SectionAddress, Relocation>,
    data_types: BTreeMap<SectionAddress, DataKind>,
    pub known_relocations: BTreeSet<SectionAddress>,
}

impl Tracker {
    pub fn new(_obj: &ObjInfo) -> Tracker {
        Self {
            processed_functions: Default::default(),
            relocations: Default::default(),
            data_types: Default::default(),
            known_relocations: Default::default(),
        }
    }

    #[instrument(name = "tracker", skip(self, obj))]
    pub fn process(&mut self, obj: &ObjInfo) -> Result<()> {
        self.process_code(obj)?;
        if obj.kind == ObjKind::Executable {
            for (section_index, section) in obj.sections.iter().filter(|(_, s)| {
                matches!(s.kind, ObjSectionKind::Data | ObjSectionKind::ReadOnlyData)
            }) {
                log::debug!(
                    "Processing section {}, address {:#X}",
                    section_index,
                    section.address
                );
                self.process_data(obj, section_index, section)?;
            }
        }
        self.reject_invalid_relocations(obj)?;
        Ok(())
    }

    /// Remove data relocations that point to an unaligned address if the aligned address has a
    /// relocation. A relocation will never point to the middle of an address.
    fn reject_invalid_relocations(&mut self, obj: &ObjInfo) -> Result<()> {
        let mut to_reject = vec![];
        for (&address, reloc) in &self.relocations {
            let section = &obj.sections[address.section];
            if !matches!(
                section.kind,
                ObjSectionKind::Data | ObjSectionKind::ReadOnlyData
            ) {
                continue;
            }
            let Some((_, target)) = reloc.kind_and_address() else {
                continue;
            };
            if !target.is_aligned(4) && self.relocations.contains_key(&target.align_down(4)) {
                log::debug!("Rejecting invalid relocation @ {} -> {}", address, target);
                to_reject.push(address);
            }
        }
        for address in to_reject {
            self.relocations.remove(&address);
        }
        Ok(())
    }

    fn process_code(&mut self, obj: &ObjInfo) -> Result<()> {
        // add exception infos
        for info in &obj.exception_data_infos {
            let handler = read_u32(&obj.sections[info.section], info.address).unwrap();
            if let Some(handler_addr) = self.is_valid_address(obj, *info, handler) {
                self.relocations.insert(
                    *info,
                    Relocation::Absolute(RelocationTarget::Address(handler_addr)),
                );
            } else {
                panic!("Invalid exception data at {:08X}!", info);
            }

            // read u32 at info + 4, should be an absolute reloc to exception record
            let record = read_u32(&obj.sections[info.section], info.address + 4).unwrap();
            if record != 0 {
                if let Some(record_addr) = self.is_valid_address(obj, *info + 4, record) {
                    self.relocations.insert(
                        *info + 4,
                        Relocation::Absolute(RelocationTarget::Address(record_addr)),
                    );
                } else {
                    panic!("Invalid exception data at {:08X}!", info);
                }
            }
        }
        if let Some(entry) = obj.entry {
            let (section_index, _) = obj.sections.at_address(entry)?;
            let entry_addr = SectionAddress::new(section_index, entry);
            self.process_function_by_address(obj, entry_addr)?;
        }
        for (section_index, _) in obj.sections.by_kind(ObjSectionKind::Code) {
            for (_, symbol) in obj
                .symbols
                .for_section(section_index)
                .filter(|(_, symbol)| {
                    symbol.kind == ObjSymbolKind::Function
                        && symbol.size_known
                        && !symbol.name.contains("__imp")
                })
            {
                let addr = SectionAddress::new(section_index, symbol.address);
                if !self.processed_functions.insert(addr) {
                    continue;
                }
                self.process_function(obj, symbol)?;
            }
        }
        Ok(())
    }

    fn process_function_by_address(&mut self, obj: &ObjInfo, addr: SectionAddress) -> Result<()> {
        if self.processed_functions.contains(&addr) {
            return Ok(());
        }
        self.processed_functions.insert(addr);
        if let Some((_, symbol)) = obj
            .symbols
            .at_section_address(addr.section, addr.address)
            .find(|(_, symbol)| symbol.kind == ObjSymbolKind::Function && symbol.size_known)
        {
            self.process_function(obj, symbol)?;
        } else {
            log::warn!("Failed to locate function symbol @ {:#010X}", addr);
        }
        Ok(())
    }

    #[inline]
    fn gpr_address(
        &self,
        obj: &ObjInfo,
        ins_addr: SectionAddress,
        value: &GprValue,
    ) -> Option<RelocationTarget> {
        match *value {
            GprValue::Constant(value) => self
                .is_valid_address(obj, ins_addr, value as u32)
                .map(RelocationTarget::Address),
            GprValue::Address(address) => Some(address),
            _ => None,
        }
    }

    fn instruction_callback(
        &mut self,
        data: ExecCbData,
        obj: &ObjInfo,
        function_start: SectionAddress,
        function_end: SectionAddress,
        possible_missed_branches: &mut BTreeMap<SectionAddress, Box<VM>>,
    ) -> Result<ExecCbResult<()>> {
        let ExecCbData {
            executor,
            vm,
            result,
            ins_addr,
            section: _,
            ins,
            block_start: _,
        } = data;
        // Using > instead of >= to treat a branch to the beginning of the function as a tail call
        let is_function_addr = |addr: SectionAddress| addr > function_start && addr < function_end;
        let _span = debug_span!("ins", addr = %ins_addr, op = ?ins.op).entered();

        match result {
            StepResult::Continue => {
                match ins.op {
                    // addi rD, rA, SIMM
                    Opcode::Addi | Opcode::Addic | Opcode::Addic_ => {
                        // let source = ins.field_ra() as usize;
                        let target = ins.field_rd() as usize;
                        if let Some(value) = self.gpr_address(obj, ins_addr, &vm.gpr[target].value)
                            && let (Some(hi_addr), Some(lo_addr)) =
                                (vm.gpr[target].hi_addr, vm.gpr[target].lo_addr)
                        {
                            let hi_reloc = self.relocations.get(&hi_addr).cloned();
                            if hi_reloc.is_none() {
                                debug_assert_ne!(
                                    value,
                                    RelocationTarget::Address(SectionAddress::new(
                                        SectionIndex::MAX,
                                        0
                                    ))
                                );
                                self.relocations.insert(hi_addr, Relocation::Ha(value));
                            }
                            let lo_reloc = self.relocations.get(&lo_addr).cloned();
                            if lo_reloc.is_none() {
                                self.relocations.insert(lo_addr, Relocation::Lo(value));
                            }
                        }
                    }
                    // ori rA, rS, UIMM
                    Opcode::Ori => {
                        let target = ins.field_ra() as usize;
                        if let Some(value) = self.gpr_address(obj, ins_addr, &vm.gpr[target].value)
                            && let (Some(hi_addr), Some(lo_addr)) =
                                (vm.gpr[target].hi_addr, vm.gpr[target].lo_addr)
                        {
                            let hi_reloc = self.relocations.get(&hi_addr).cloned();
                            if hi_reloc.is_none() {
                                self.relocations.insert(hi_addr, Relocation::Ha(value));
                            }
                            let lo_reloc = self.relocations.get(&lo_addr).cloned();
                            if lo_reloc.is_none() {
                                self.relocations.insert(lo_addr, Relocation::Lo(value));
                            }
                        }
                    }
                    _ => {}
                }
                Ok(ExecCbResult::Continue)
            }
            StepResult::LoadStore {
                address,
                source,
                source_reg: _,
            } => {
                if !obj.blocked_relocation_sources.contains(ins_addr) {
                    match (source.hi_addr, source.lo_addr) {
                        (Some(hi_addr), None) => {
                            let hi_reloc = self.relocations.get(&hi_addr).cloned();
                            if hi_reloc.is_none() {
                                debug_assert_ne!(
                                    address,
                                    RelocationTarget::Address(SectionAddress::new(
                                        SectionIndex::MAX,
                                        0
                                    ))
                                );
                                self.relocations.insert(hi_addr, Relocation::Ha(address));
                            }
                            if hi_reloc.is_none()
                                || matches!(hi_reloc, Some(Relocation::Ha(v)) if v == address)
                            {
                                self.relocations.insert(ins_addr, Relocation::Lo(address));
                            }
                        }
                        (Some(hi_addr), Some(lo_addr)) => {
                            let hi_reloc = self.relocations.get(&hi_addr).cloned();
                            if hi_reloc.is_none() {
                                debug_assert_ne!(
                                    address,
                                    RelocationTarget::Address(SectionAddress::new(
                                        SectionIndex::MAX,
                                        0
                                    ))
                                );
                                self.relocations.insert(hi_addr, Relocation::Ha(address));
                            }
                            let lo_reloc = self.relocations.get(&lo_addr).cloned();
                            if lo_reloc.is_none() {
                                self.relocations.insert(lo_addr, Relocation::Lo(address));
                            }
                        }
                        _ => {}
                    }

                    if let RelocationTarget::Address(address) = address {
                        self.data_types.insert(address, data_kind_from_op(ins.op));
                    }
                }
                Ok(ExecCbResult::Continue)
            }
            StepResult::Illegal => {
                log::debug!(
                    "Illegal instruction hit @ {:#010X} (function {:#010X}-{:#010X})",
                    ins_addr,
                    function_start,
                    function_end
                );
                Ok(ExecCbResult::Continue)
            }
            StepResult::Jump(target) => match target {
                BranchTarget::Return => Ok(ExecCbResult::EndBlock),
                BranchTarget::Unknown
                | BranchTarget::JumpTable {
                    jump_table_address: RelocationTarget::External,
                    ..
                } => {
                    let next_addr = ins_addr + 4;
                    if next_addr < function_end {
                        possible_missed_branches.insert(ins_addr + 4, vm.clone_all());
                    }
                    Ok(ExecCbResult::EndBlock)
                }
                BranchTarget::Address(addr) => {
                    let next_addr = ins_addr + 4;
                    if next_addr < function_end {
                        possible_missed_branches.insert(ins_addr + 4, vm.clone_all());
                    }
                    if let RelocationTarget::Address(addr) = addr
                        && is_function_addr(addr)
                    {
                        return Ok(ExecCbResult::Jump(addr));
                    }
                    if ins.is_direct_branch() {
                        self.relocations.insert(ins_addr, Relocation::Rel24(addr));
                    }
                    Ok(ExecCbResult::EndBlock)
                }
                BranchTarget::JumpTable {
                    jump_table_type: jt,
                    jump_table_address: RelocationTarget::Address(address),
                    size,
                } => {
                    let (entries, _) = get_jump_table_entries(
                        obj,
                        address,
                        jt,
                        size,
                        ins_addr,
                        function_start,
                        Some(function_end),
                    )?;
                    // TODO: if this is an absolute jump table, add relocs for each entry
                    for target in BTreeSet::from_iter(entries) {
                        if is_function_addr(target) {
                            executor.push(target, vm.clone_all(), true);
                        }
                    }
                    Ok(ExecCbResult::EndBlock)
                }
            },
            StepResult::Branch(branches) => {
                for branch in branches {
                    match branch.target {
                        BranchTarget::Unknown
                        | BranchTarget::Return
                        | BranchTarget::JumpTable {
                            jump_table_address: RelocationTarget::External,
                            ..
                        } => {}
                        BranchTarget::Address(target) => {
                            let (addr, is_fn_addr) = if let RelocationTarget::Address(addr) = target
                            {
                                (addr, is_function_addr(addr))
                            } else {
                                (SectionAddress::new(SectionIndex::MAX, 0), false)
                            };
                            if branch.link || !is_fn_addr {
                                self.relocations.insert(
                                    ins_addr,
                                    match ins.op {
                                        Opcode::B => Relocation::Rel24(target),
                                        Opcode::Bc => Relocation::Rel14(target),
                                        _ => continue,
                                    },
                                );
                            } else if is_fn_addr {
                                executor.push(addr, branch.vm, true);
                            }
                        }
                        BranchTarget::JumpTable {
                            jump_table_type: jt,
                            jump_table_address: RelocationTarget::Address(address),
                            size,
                        } => {
                            let (entries, _) = get_jump_table_entries(
                                obj,
                                address,
                                jt,
                                size,
                                ins_addr,
                                function_start,
                                Some(function_end),
                            )?;
                            for target in BTreeSet::from_iter(entries) {
                                if is_function_addr(target) {
                                    executor.push(target, branch.vm.clone_all(), true);
                                }
                            }
                        }
                    }
                }
                Ok(ExecCbResult::EndBlock)
            }
        }
    }

    pub fn process_function(&mut self, obj: &ObjInfo, symbol: &ObjSymbol) -> Result<()> {
        let Some(section_index) = symbol.section else {
            bail!("Function '{}' missing section", symbol.name)
        };
        let function_start = SectionAddress::new(section_index, symbol.address);
        let function_end = function_start + symbol.size;
        let _span =
            info_span!("fn", name = %symbol.name, start = %function_start, end = %function_end)
                .entered();

        // The compiler can sometimes create impossible-to-reach branches,
        // but we still want to track them.
        let mut possible_missed_branches = BTreeMap::new();

        if let Some(info) = &obj.pdata_funcs.get(&function_start) {
            for handler in info.handlers.keys() {
                possible_missed_branches.insert(*handler, VM::new());
            }
        }

        let mut executor = Executor::new(obj);
        executor.push(function_start, VM::new(), false);
        loop {
            executor.run(obj, |data| -> Result<ExecCbResult<()>> {
                self.instruction_callback(
                    data,
                    obj,
                    function_start,
                    function_end,
                    &mut possible_missed_branches,
                )
            })?;

            if possible_missed_branches.is_empty() {
                break;
            }
            let mut added = false;
            for (addr, vm) in take(&mut possible_missed_branches) {
                let section = &obj.sections[addr.section];
                if !executor.visited(section.address, addr) {
                    executor.push(addr, vm, true);
                    added = true;
                }
            }
            if !added {
                break;
            }
        }
        Ok(())
    }

    fn process_data(
        &mut self,
        obj: &ObjInfo,
        section_index: SectionIndex,
        section: &ObjSection,
    ) -> Result<()> {
        let mut addr = SectionAddress::new(section_index, section.address);
        for chunk in section.data.as_chunks::<4>().0 {
            let value = u32::from_be_bytes(chunk[0..4].try_into()?);
            if let Some(value) = self.is_valid_address(obj, addr, value) {
                self.relocations
                    .insert(addr, Relocation::Absolute(RelocationTarget::Address(value)));
            }
            addr += 4;
        }
        Ok(())
    }

    fn is_valid_address(
        &self,
        obj: &ObjInfo,
        from: SectionAddress,
        addr: u32,
    ) -> Option<SectionAddress> {
        // Check for an existing relocation
        if cfg!(debug_assertions) {
            let relocation_target = relocation_target_for(obj, from, None).ok().flatten();
            if !matches!(relocation_target, None | Some(RelocationTarget::External)) {
                // VM should have already handled this
                panic!("Relocation already exists for {addr:#010X} (from {from:#010X})");
            }
        }
        // Remainder of this function is for executable objects only
        if obj.kind == ObjKind::Relocatable {
            return None;
        }
        // Check blocked relocation sources
        if obj.blocked_relocation_sources.contains(from) {
            return None;
        }
        // Find the section containing the address
        if let Ok((section_index, section)) = obj.sections.at_address(addr) {
            // References to code sections will never be unaligned
            if section.kind == ObjSectionKind::Code && addr & 3 != 0 {
                return None;
            }
            let section_address = SectionAddress::new(section_index, addr);
            // Check blocked relocation targets
            if obj.blocked_relocation_targets.contains(section_address) {
                return None;
            }
            // It's valid
            Some(section_address)
        } else {
            // Check known relocations (function signature matching)
            if self.known_relocations.contains(&from) {
                return Some(SectionAddress::new(SectionIndex::MAX, addr));
            }
            // Not valid
            None
        }
    }

    #[instrument(name = "apply", skip(self, obj))]
    pub fn apply(&self, obj: &mut ObjInfo, replace: bool) -> Result<()> {
        for (&addr, reloc) in &self.relocations {
            let Some((reloc_kind, target)) = reloc.kind_and_address() else {
                // Skip external relocations, they already exist
                continue;
            };
            if obj.blocked_relocation_sources.contains(addr)
                || obj.blocked_relocation_targets.contains(target)
            {
                // Skip blocked relocations
                continue;
            }
            if obj.sections[target.section].name == ".pdata" {
                // Skip .pdata
                continue;
            }
            if obj.kind == ObjKind::Relocatable {
                // Sanity check: relocatable objects already have relocations,
                // did our analyzer find one that isn't real?
                let section = &obj.sections[addr.section];
                if section.relocations.at(addr.address).is_none()
                    // We _do_ want to rebuild missing R_PPC_REL24 relocations
                    && !matches!(reloc_kind, ObjRelocKind::PpcRel24)
                {
                    log::warn!(
                        "Found invalid relocation {} {:?} (target {}) in relocatable object",
                        addr,
                        reloc,
                        target
                    );
                }
            }
            let (data_kind, inferred_alignment) = self
                .data_types
                .get(&target)
                .map(|dt| match dt {
                    DataKind::Unknown => (ObjDataKind::Unknown, None),
                    DataKind::Word => (ObjDataKind::Byte4, None),
                    DataKind::Half => (ObjDataKind::Byte2, None),
                    DataKind::Byte => (ObjDataKind::Byte, None),
                    DataKind::Float => (ObjDataKind::Float, Some(4)),
                    DataKind::Double => (ObjDataKind::Double, Some(8)),
                })
                .unwrap_or_default();
            let (target_symbol, addend) = if let Some((symbol_idx, symbol)) =
                obj.symbols.for_relocation(target, reloc_kind)?
            {
                let symbol_address = symbol.address;
                if symbol_address == target.address
                    && ((data_kind != ObjDataKind::Unknown
                        && symbol.data_kind == ObjDataKind::Unknown)
                        || (symbol.align.is_none() && inferred_alignment.is_some()))
                {
                    let mut new_symbol = symbol.clone();
                    if symbol.data_kind == ObjDataKind::Unknown {
                        new_symbol.data_kind = data_kind;
                    }
                    if symbol.align.is_none()
                        && let Some(inferred_alignment) = inferred_alignment
                        && symbol_address % inferred_alignment == 0
                    {
                        new_symbol.align = Some(inferred_alignment);
                    }
                    obj.symbols.replace(symbol_idx, new_symbol)?;
                }
                (symbol_idx, target.address as i64 - symbol_address as i64)
            } else {
                let symbol_idx = obj.symbols.add_direct(ObjSymbol {
                    name: format!("lbl_{:08X}", target.address),
                    address: target.address,
                    section: Some(target.section),
                    data_kind,
                    ..Default::default()
                })?;
                (symbol_idx, 0)
            };
            let reloc = ObjReloc {
                kind: reloc_kind,
                target_symbol,
                addend,
                module: None,
            };
            let section = &mut obj.sections[addr.section];
            if replace {
                section.relocations.replace(addr.address, reloc);
            } else if let Err(e) = section.relocations.insert(addr.address, reloc.clone()) {
                let reloc_symbol = &obj.symbols[target_symbol];
                if reloc_symbol.name != "_unresolved" {
                    let iter_symbol = &obj.symbols[e.value.target_symbol];
                    if iter_symbol.address as i64 + e.value.addend
                        != reloc_symbol.address as i64 + addend
                    {
                        bail!(
                            "Conflicting relocations (target {:#010X}): {:#010X?} ({} {:#X}) != {:#010X?} ({} {:#X})",
                            target,
                            e.value,
                            iter_symbol.name,
                            iter_symbol.address as i64 + e.value.addend,
                            reloc,
                            reloc_symbol.name,
                            reloc_symbol.address as i64 + addend,
                        );
                    }
                }
            }
        }
        Ok(())
    }
}

fn data_kind_from_op(op: Opcode) -> DataKind {
    match op {
        Opcode::Lbz => DataKind::Byte,
        Opcode::Lbzu => DataKind::Byte,
        Opcode::Lbzux => DataKind::Byte,
        Opcode::Lbzx => DataKind::Byte,
        Opcode::Lfd => DataKind::Double,
        Opcode::Lfdu => DataKind::Double,
        Opcode::Lfdux => DataKind::Double,
        Opcode::Lfdx => DataKind::Double,
        Opcode::Lfs => DataKind::Float,
        Opcode::Lfsu => DataKind::Float,
        Opcode::Lfsux => DataKind::Float,
        Opcode::Lfsx => DataKind::Float,
        Opcode::Lha => DataKind::Half,
        Opcode::Lhau => DataKind::Half,
        Opcode::Lhaux => DataKind::Half,
        Opcode::Lhax => DataKind::Half,
        Opcode::Lhbrx => DataKind::Half,
        Opcode::Lhz => DataKind::Half,
        Opcode::Lhzu => DataKind::Half,
        Opcode::Lhzux => DataKind::Half,
        Opcode::Lhzx => DataKind::Half,
        Opcode::Lwz => DataKind::Word,
        Opcode::Lwzu => DataKind::Word,
        Opcode::Lwzux => DataKind::Word,
        Opcode::Lwzx => DataKind::Word,
        Opcode::Stb => DataKind::Byte,
        Opcode::Stbu => DataKind::Byte,
        Opcode::Stbux => DataKind::Byte,
        Opcode::Stbx => DataKind::Byte,
        Opcode::Stfd => DataKind::Double,
        Opcode::Stfdu => DataKind::Double,
        Opcode::Stfdux => DataKind::Double,
        Opcode::Stfdx => DataKind::Double,
        Opcode::Stfiwx => DataKind::Float,
        Opcode::Stfs => DataKind::Float,
        Opcode::Stfsu => DataKind::Float,
        Opcode::Stfsux => DataKind::Float,
        Opcode::Stfsx => DataKind::Float,
        Opcode::Sth => DataKind::Half,
        Opcode::Sthbrx => DataKind::Half,
        Opcode::Sthu => DataKind::Half,
        Opcode::Sthux => DataKind::Half,
        Opcode::Sthx => DataKind::Half,
        Opcode::Stw => DataKind::Word,
        Opcode::Stwbrx => DataKind::Word,
        Opcode::Stwcx_ => DataKind::Word,
        Opcode::Stwu => DataKind::Word,
        Opcode::Stwux => DataKind::Word,
        Opcode::Stwx => DataKind::Word,
        _ => DataKind::Unknown,
    }
}
