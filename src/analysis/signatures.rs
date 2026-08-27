use crate::{
    analysis::RelocationTarget,
    analysis::cfa::SectionAddress,
    analysis::tracker::{Relocation, Tracker},
    obj::{ObjInfo, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags, SymbolIndex},
    util::signatures::{FunctionSignature, OutReference, SignatureCandidate},
};
use anyhow::{Result, ensure};
use base64::{Engine, engine::general_purpose::STANDARD};

// fn apply_signature_for_symbol(obj: &mut ObjInfo, name: &str, sig_str: &str) -> Result<()> {
//     Ok(())
// }

// you pass in a function's name and address, and this'll give you the relevant relocs for mapping/labeling
fn get_function_references(
    obj: &ObjInfo,
    name: &str,
    addr: &SectionAddress,
    size_override: Option<u32>,
) -> Result<Vec<SectionAddress>> {
    let mut tracker = Tracker::new(obj);
    // the symbol being passed into process_function only needs a name, address, section, and size
    let tracker_sym = ObjSymbol {
        name: String::from(name),
        address: addr.address,
        section: Some(addr.section),
        size: match size_override {
            Some(size) => size,
            None => match &obj.pdata_funcs.get(addr) {
                Some(info) => info.full_size,
                None => {
                    // check obj's symbols - we might've added this symbol in beforehand
                    // otherwise, we can't reliably deduce function end at this point - empty vecs returned
                    if let Some((_, sym)) = obj
                        .symbols
                        .at_section_address(addr.section, addr.address)
                        .next()
                    {
                        if sym.size_known {
                            sym.size
                        } else {
                            return Ok(vec![]);
                        }
                    } else {
                        return Ok(vec![]);
                    }
                }
            },
        },
        ..Default::default()
    };
    tracker.process_function(obj, &tracker_sym)?;
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
    Ok(refs)
}

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
    for chunk in signature.chunks_exact(8) {
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

pub fn apply_signature(obj: &mut ObjInfo, sig_str: &str) -> Result<()> {
    let sigs: Vec<FunctionSignature> = serde_yaml::from_str(sig_str)?;
    for sig in sigs.iter() {
        log::debug!("Signature name: {}", sig.name);

        // func_addr we have to have gotten from a symbol
        let func_sym = obj.symbols.by_name(&sig.name)?.map(|(_, sym)| sym);
        // if we have a concrete address, go straight to finding references
        if let Some(func_addr) = func_sym.map(|sym| sym.address) {
            let sec_addr = SectionAddress::new(obj.sections.at_address(func_addr)?.0, func_addr);
            log::debug!(
                "Existing symbol for {} found at {:08X}!",
                sig.name,
                sec_addr
            );
            // the code below this could be a callable function maybe
            let (discovered_refs, signature_refs) = {
                let refs = get_function_references(
                    obj,
                    &sig.name,
                    &sec_addr,
                    match func_sym {
                        Some(sym) => {
                            if sym.size_known {
                                Some(sym.size)
                            } else {
                                None
                            }
                        }
                        None => None,
                    },
                )?;
                let mut sig_refs = sig.references.clone();
                if sig_refs.len() != refs.len() {
                    sig_refs.retain(|x| !x.optional);
                }
                // if we don't have a matching OutReference count by this point, this can't be our func
                ensure!(
                    refs.len() == sig_refs.len(),
                    "Mismatch in reference count for function {}! (expected {}, got {})",
                    sig.name,
                    sig_refs.len(),
                    refs.len()
                );
                (refs, sig_refs)
            };
            for i in 0..discovered_refs.len() {
                if !signature_refs[i].skip {
                    add_symbol_from_reference(obj, &discovered_refs[i], &signature_refs[i])?;
                }
            }
        } else {
            // if we have a size but no concrete address, we'll have to filter pdata to find possible candidates for this function
            // at this point, we'll need a signature from the yml - we have to rely on our possible signatures
            for sig_candidate in sig.possible_signatures.iter() {
                log::debug!(
                    "Looking for func of size 0x{:X} with handler count {:?}",
                    sig_candidate.size,
                    sig.num_handlers
                );
                if let Some(num_handlers_in_pdata) = sig.num_handlers {
                    // pre-compute the desired section index
                    let (sec_idx, sec) = obj
                        .sections
                        .by_name(&*sig.section)?
                        .expect("Couldn't find section!");
                    // filter pdata for acceptable potential candidates for this func
                    for (addr, info) in
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
                        log::debug!("Candidate for {}: {:08X}", sig.name, addr);
                        if check_signature(sec.data_range(addr.address, 0)?, sig_candidate)? {
                            log::debug!("Found the func! It's at {:08X}", addr);
                            // add function and labels, and any references
                        }
                    }
                    // if we haven't found it by this point, and required is true, fail
                } else {
                    // brute force memmem find
                }
            }
        }
    }

    Ok(())
}

// defer splitting, have our yml focus solely on function signatures
// we can deduce splits after signature processing is complete

// splits can be in a lazylock map or something

// parse from entrypoint first, and when that's done, then you can pick up any stragglers from LIBCMT or XAPILIB
pub fn apply_signatures(obj: &mut ObjInfo) -> Result<()> {
    apply_signature(obj, include_str!("../../assets/signatures/crtgpr.yml"))?;
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
