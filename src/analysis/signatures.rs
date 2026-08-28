use crate::{
    analysis::RelocationTarget,
    analysis::cfa::SectionAddress,
    analysis::tracker::{Relocation, Tracker},
    obj::{ObjInfo, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind, SymbolIndex},
    util::signatures::{FunctionSignature, OutReference, SignatureCandidate},
};
use anyhow::{Result, ensure};
use base64::{Engine, engine::general_purpose::STANDARD};
use std::collections::BTreeSet;

// fn apply_signature_for_symbol(obj: &mut ObjInfo, name: &str, sig_str: &str) -> Result<()> {
//     Ok(())
// }

fn add_symbol_from_reference(
    obj: &mut ObjInfo,
    addr: &SectionAddress,
    reference: &OutReference,
) -> Result<SymbolIndex> {
    // deduce a symbol size from our known_functions (or pdata for C++)
    let symbol_size = {
        let mut size = reference.size;
        if size == 0
            && let Some(info) = obj.pdata_funcs.get(addr)
        {
            size = info.full_size;
        }
        size
    };
    log::debug!(
        "Adding inferred symbol {} at {:08X}{}",
        reference.name,
        addr,
        if symbol_size != 0 {
            format!(" of size 0x{:X}", symbol_size)
        } else {
            String::from("")
        },
    );
    obj.add_symbol(
        ObjSymbol {
            name: reference.name.clone(),
            address: addr.address,
            section: Some(addr.section),
            size: symbol_size,
            size_known: symbol_size != 0,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            kind: reference.kind,
            ..Default::default()
        },
        false,
    )
}

fn check_signature(bytes: &[u8], sig: &SignatureCandidate) -> Result<bool> {
    let signature = STANDARD.decode(&sig.signature)?;
    let funcs_size = signature.len() / 2;
    if bytes.len() < funcs_size {
        return Ok(false);
    }

    let mut i = 0;
    for chunk in signature.as_chunks::<8>().0 {
        let ins = u32::from_be_bytes(chunk[0..4].try_into()?);
        let pat = u32::from_be_bytes(chunk[4..8].try_into()?);
        let actual_ins = u32::from_be_bytes(bytes[i..i + 4].try_into()?);
        if actual_ins & pat != ins {
            // log::debug!("Mismatch: {:08X} & {:08X} != {:08X}!", actual_ins, pat, ins);
            return Ok(false);
        }
        i += 4;
    }
    Ok(true)
}

// add_to_obj - covers labels and references
// returns a set of the SymbolIndexes that were applied/added as a result of this signature
fn add_to_obj(
    obj: &mut ObjInfo,
    sym_idx: SymbolIndex,
    sig: &FunctionSignature,
) -> Result<BTreeSet<SymbolIndex>> {
    let mut applied_symbols: BTreeSet<SymbolIndex> = BTreeSet::new();
    let symbol_addr = {
        let sym = &obj.symbols[sym_idx];
        SectionAddress::new(sym.section.unwrap(), sym.address)
    };
    applied_symbols.insert(sym_idx);
    // add any additional labels
    for label in sig.labels.iter() {
        let this_sym_addr = symbol_addr + label.offset;
        log::debug!(
            "Adding additional symbol {} at {:08X}",
            label.name,
            this_sym_addr
        );
        applied_symbols.insert(obj.add_symbol(
            ObjSymbol {
                name: label.name.clone(),
                address: this_sym_addr.address,
                section: Some(this_sym_addr.section),
                size: label.size.unwrap_or(0),
                size_known: label.size.is_some(),
                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                kind: match label.size {
                    Some(_) => ObjSymbolKind::Function,
                    None => ObjSymbolKind::Unknown,
                },
                ..Default::default()
            },
            false,
        )?);
    }
    // add any sleds
    for sled in sig.sleds.iter() {
        let start_addr = symbol_addr + sled.offset;
        for i in sled.start..sled.end {
            let addr = start_addr + (i - sled.start) * sled.step;
            log::debug!(
                "\tAdding additional symbol {}{} at {:08X}",
                sled.name_start,
                i,
                addr
            );
            applied_symbols.insert(obj.add_symbol(
                ObjSymbol {
                    name: format!("{}{}", sled.name_start, i),
                    address: addr.address,
                    section: Some(addr.section),
                    flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                    ..Default::default()
                },
                false,
            )?);
        }
    }
    // then add any references
    let mut tracker = Tracker::new(obj);
    tracker.process_function(obj, &obj.symbols[sym_idx])?;
    let discovered_refs = {
        let mut refs = vec![];
        for reloc in tracker.relocations.values() {
            match reloc {
                Relocation::Rel24(RelocationTarget::Address(a)) => {
                    refs.push(*a);
                }
                Relocation::Lo(RelocationTarget::Address(a)) => {
                    refs.push(*a);
                }
                _ => {}
            }
        }
        refs
    };
    let signature_refs = {
        let mut sig_refs = sig.references.clone();
        if sig_refs.len() != discovered_refs.len() {
            sig_refs.retain(|x| !x.optional);
        }
        sig_refs
    };
    // if we don't have a matching OutReference count by this point, this can't be our func
    ensure!(
        discovered_refs.len() == signature_refs.len(),
        "Mismatch in reference count for function {}! (expected {}, got {})",
        sig.name,
        signature_refs.len(),
        discovered_refs.len()
    );
    for i in 0..discovered_refs.len() {
        if !signature_refs[i].skip {
            applied_symbols.insert(add_symbol_from_reference(
                obj,
                &discovered_refs[i],
                &signature_refs[i],
            )?);
        }
    }
    Ok(applied_symbols)
}

// returns a set of the SymbolIndexes that were applied/added as a result of this signature
// this way, when deducing splits, you can lookup symbols from this set instead of the entire obj
pub fn apply_signature(obj: &mut ObjInfo, sig_str: &str) -> Result<BTreeSet<SymbolIndex>> {
    let mut applied_symbols: BTreeSet<SymbolIndex> = BTreeSet::new();
    let sigs: Vec<FunctionSignature> = serde_yaml::from_str(sig_str)?;
    for sig in sigs.iter() {
        log::debug!("Signature name: {}", sig.name);

        // if there's a symbol associated with this func
        if let Some((func_sym_idx, func_sym)) = obj.symbols.by_name(&sig.name)? {
            // the symbol HAS to have an address
            let sec_addr = SectionAddress::new(func_sym.section.unwrap(), func_sym.address);
            log::debug!(
                "Existing symbol for {} found at {:08X}!",
                sig.name,
                sec_addr
            );
            ensure!(
                func_sym.size_known,
                "Func at {:08X} has no known size!",
                sec_addr
            );
            // then call add_to_obj
            applied_symbols.extend(add_to_obj(obj, func_sym_idx, sig)?);
        } else {
            // if we have a size but no concrete address, we'll have to filter pdata to find possible candidates for this function
            // at this point, we'll need a signature from the yml - we have to rely on our possible signatures
            for sig_candidate in sig.possible_signatures.iter() {
                if let Some(num_handlers_in_pdata) = sig.num_handlers {
                    let mut found = false;
                    // pre-compute the desired section index
                    let (sec_idx, sec) = obj
                        .sections
                        .by_name(&sig.section)?
                        .expect("Couldn't find section!");
                    // filter pdata for acceptable potential candidates for this func
                    for (addr, _) in
                    // In order to be a potential candidates for this function signature...
                        obj.pdata_funcs.iter().filter(|(addr, info)| {
                            // -there can't be a symbol at the associated SectionAddress
                            obj.symbols.at_section_address(addr.section, addr.address).next().is_none() &&
                                // -the section has to match
                                addr.section == sec_idx &&
                                // -the number of expected exception handlers has to match
                                info.handlers.len() == num_handlers_in_pdata as usize
                                // -the full size of the function has to match
                                && info.full_size == sig_candidate.size
                                // -if we don't have any handlers, then the main size == full size == the signature's listed size
                                && if num_handlers_in_pdata == 0 { info.main_size == info.full_size } else { true }
                        }) {
                        if check_signature(sec.data_range(addr.address, 0)?, sig_candidate)? {
                            log::debug!("Found func {} at {:08X}, size 0x{:X}", sig.name, addr, sig_candidate.size);
                            found = true;
                            // add the main symbol here
                            let sym_idx = obj.add_symbol(ObjSymbol {
                                name: sig.name.clone(),
                                address: addr.address,
                                section: Some(addr.section),
                                size: sig_candidate.size,
                                size_known: true,
                                flags: ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
                                kind: ObjSymbolKind::Function,
                                ..Default::default()
                            }, false)?;

                            // add any additional functions/labels, and any references
                            applied_symbols.extend(add_to_obj(obj, sym_idx, sig)?);
                            break;
                        }
                    }
                    // if we haven't found it by this point, and required is true, fail
                    if !found && sig.required {
                        panic!("Couldn't find required func {}!", sig.name);
                    }
                } else {
                    // brute force memmem find
                    log::debug!("need to brute force memmem find to identify {}!", sig.name);
                }
            }
        }
    }
    Ok(applied_symbols)
}

// defer splitting, have our yml focus solely on function signatures
// we can deduce splits after signature processing is complete

// splits can be in a lazylock map or something

// parse from entrypoint first, and when that's done, then you can pick up any stragglers from LIBCMT or XAPILIB
pub fn apply_signatures(obj: &mut ObjInfo) -> Result<()> {
    apply_signature(
        obj,
        include_str!("../../assets/signatures/reg_intrinsics.yml"),
    )?;
    if obj.entry.is_some() {
        apply_signature(obj, include_str!("../../assets/signatures/entry.yml"))?;
    }
    Ok(())
}

// pub fn apply_signatures(obj: &mut ObjInfo) -> Result<()> {
//     if let Some(entry) = obj.entry.map(|n| n as u32) {
//         let (entry_section_index, entry_section) = obj.sections.at_address(entry)?;
//         if let Some(signature) = check_signatures_str(
//             entry_section,
//             entry,
//             include_str!("../../assets/signatures/__start.yml"),
//         )? {
//             apply_signature(obj, SectionAddress::new(entry_section_index, entry), &signature)?;
//         }
//     }
//
//     for &(name, sig_str) in SIGNATURES {
//         apply_signature_for_symbol(obj, name, sig_str)?
//     }
//
//     apply_init_user_signatures(obj)?;
//     apply_ctors_signatures(obj)?;
//     apply_dtors_signatures(obj)?;
//     Ok(())
// }
