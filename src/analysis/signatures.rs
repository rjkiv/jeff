use std::{collections::HashMap, sync::LazyLock};

use anyhow::{Ok, Result};
use base64::{engine::general_purpose::STANDARD, Engine};
use serde::{Deserialize, Serialize};

use crate::{
    analysis::{
        cfa::SectionAddress,
        tracker::{Relocation, Tracker},
        RelocationTarget,
    },
    obj::{
        ExceptionType::{Normal, C, CXX},
        ObjInfo, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind,
        ObjSymbolKind::Function,
        SymbolIndex,
    },
};

static SIGNATURES: LazyLock<HashMap<&str, &str>> = LazyLock::new(|| {
    let mut map = HashMap::new();
    map.insert("entry", include_str!("../../assets/signatures_x360/entry.yml"));
    map.insert("post-entry", include_str!("../../assets/signatures_x360/postentry.yml"));
    map.insert("_purecall", include_str!("../../assets/signatures_x360/_purecall.yml"));
    map.insert("_beginthreadex", include_str!("../../assets/signatures_x360/_beginthreadex.yml"));
    map.insert("atexit", include_str!("../../assets/signatures_x360/atexit.yml"));
    map.insert("post-atexit", include_str!("../../assets/signatures_x360/postatexit.yml"));
    map
});

#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
struct OutReference {
    pub name: String,
    #[serde(default)]
    pub kind: ObjSymbolKind,
    #[serde(default)]
    pub size: u32,
    // If this reference can show up on one xex but not on another, we'll mark it as optional
    #[serde(default)]
    pub optional: bool,
    // If this is a reg intrinsic, xex import, something we already know ahead of time,
    // skip labeling it
    #[serde(default)]
    pub skip: bool,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
struct FunctionSignature {
    pub name: String,
    #[serde(default)]
    pub pdata_type: u8,
    #[serde(default)]
    pub num_handlers: u8,
    // The expected size of this function.
    // If this function can't be reliably found in pdata, this HAS to be provided
    #[serde(default)]
    pub size: u32,
    // The expected signature of this function.
    // If this function can't be reliably found in pdata, this HAS to be provided
    #[serde(default)]
    pub signature: String,
    #[serde(default)]
    pub references: Vec<OutReference>,
}

// you pass in a function's name and address, and this'll give you the relevant relocs for mapping/labeling
fn get_function_references(
    obj: &ObjInfo,
    name: &str,
    addr: &SectionAddress,
) -> Result<Vec<SectionAddress>> {
    let mut tracker = Tracker::new(obj);
    // the symbol being passed into process_function only needs a name, address, section, and size
    // TODO: if a symbol for this func was already added to our ObjInfo, reuse its info so we don't have to recalculate things
    let tracker_sym = ObjSymbol {
        name: String::from(name),
        address: addr.address,
        section: Some(addr.section),
        size: match &obj.pdata_funcs.get(addr) {
            Some(Normal { end }) => end.address - addr.address,
            Some(C { handlers }) => {
                // the end of the main function body == the start of the first C handler
                let Some((k, _)) = handlers.first_key_value() else {
                    panic!("entry doesn't have C handlers?");
                };
                k.address - addr.address
            }
            Some(CXX { info }) => {
                let first_unwind = info.unwinds.iter().filter_map(|x| *x).min();
                let first_catch = info.catches.iter().filter_map(|x| *x).min();
                let main_body_ending = match (first_unwind, first_catch) {
                    (Some(unwind), Some(catch)) => unwind.min(catch),
                    (Some(unwind), None) => unwind,
                    (None, Some(catch)) => catch,
                    _ => return Ok(vec![]),
                };
                main_body_ending.address - addr.address
            }
            None => {
                // check obj's symbols - we might've added this symbol in beforehand
                // otherwise, we can't reliably deduce function end at this point - empty vecs returned
                if let Some((_, sym)) =
                    obj.symbols.at_section_address(addr.section, addr.address).next()
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
        if size == 0 {
            // Normal and C funcs should have a size value in known_functions
            if let Some(size_option) = obj.known_functions.get(addr) {
                if let Some(s) = size_option {
                    size = *s;
                }
                // we have to search for C++ info from pdata
                else if let Some(CXX { info }) = obj.pdata_funcs.get(addr) {
                    let first_unwind = info.unwinds.iter().filter_map(|x| *x).max();
                    let first_catch = info.catches.iter().filter_map(|x| *x).max();
                    // if there are catches and zero unwinds, we have a known ending
                    if let (None, Some(catch)) = (first_unwind, first_catch) {
                        size = obj.catches.get(&catch).unwrap().address - addr.address;
                    }
                }
            }
        }
        size
    };
    log::debug!(
        "Adding inferred symbol {} at {:08X}{}",
        reference.name,
        addr,
        if symbol_size != 0 { format!(" of size 0x{:X}", symbol_size) } else { String::from("") },
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

// returns true if everything was successfully applied
// false if any signature could not be applied
pub fn apply_signature(obj: &mut ObjInfo, name: &str) -> Result<bool> {
    let sigs: Vec<FunctionSignature> =
        serde_yaml::from_str(SIGNATURES.get(name).expect("Missing signature!"))?;

    // if this bool is true, then this yml is just multiple known versions of one func we're trying to match
    let matching_one_func = sigs.iter().all(|sig| sig.name == sigs[0].name);

    for sig in sigs {
        log::debug!("Signature name: {}", sig.name);
        let func_sym = obj.symbols.by_name(&sig.name)?;

        // either we know the size from a symbol, or it was given to us in our yml
        let size = match sig.size {
            0 => match func_sym {
                Some((_, sym)) => {
                    if sym.size_known {
                        Some(sym.size)
                    } else {
                        None
                    }
                }
                None => None,
            },
            _ => Some(sig.size),
        };
        // func_addr we have to have gotten from a symbol
        let func_addr = func_sym.map(|(_, sym)| sym.address);

        // if we have a concrete address, go straight to finding references
        if let Some(func_addr) = func_addr {
            let sec_addr = SectionAddress::new(obj.sections.at_address(func_addr)?.0, func_addr);
            // get_function_references will infer the size from pdata, doesn't matter if we know it or not
            // if it can't find a size, refs will be empty, nothing new will be marked
            let refs = get_function_references(obj, &sig.name, &sec_addr)?;
            let sig_refs = {
                let mut sig_refs = sig.references.clone();
                if sig_refs.len() != refs.len() {
                    sig_refs.retain(|x| !x.optional);
                }
                sig_refs
            };
            // if we don't have a matching OutReference count by this point, this ain't our func, skip
            if sig_refs.len() != refs.len() {
                return Ok(false);
            }
            for i in 0..refs.len() {
                if !sig_refs[i].skip {
                    add_symbol_from_reference(obj, &refs[i], &sig_refs[i])?;
                }
            }
        }
        // if we have a size but no concrete address, we'll have to filter pdata to find possible candidates for this function
        // at this point, we'll need a signature from the yml
        else if let Some(size) = size {
            // if this func is in pdata, get possible candidates and try to apply the signature to each of them
            // otherwise, we have to brute force it
            match sig.pdata_type {
                1 => {
                    let mut func_candidates = vec![];
                    // Normal
                    // get every pdata_func where the type is Normal, and end - start == size
                    for (addr, exception_type) in obj.pdata_funcs.iter() {
                        // there must also not be a known symbol associated with this address
                        if matches!(exception_type, Normal { end } if end.address - addr.address == size)
                            && obj
                                .symbols
                                .kind_at_section_address(addr.section, addr.address, Function)?
                                .is_none()
                        {
                            func_candidates.push(*addr);
                        }
                    }
                    // println!("Candidates found: {}", func_candidates.len());
                    for cand in func_candidates {
                        // TODO: accept multiple possible sizes/signatures for one function?
                        // thanks to reg intrinsics and XDK versions varying
                        if check_signature(obj, cand.address, &sig.signature)? {
                            log::debug!("Found function at {:08X}!", cand);
                            add_symbol_from_reference(obj, &cand, &OutReference {
                                name: sig.name.clone(),
                                kind: Function,
                                size,
                                optional: false,
                                skip: false,
                            })?;
                            // add function references from this func
                            let refs = get_function_references(obj, &sig.name, &cand)?;
                            let sig_refs = {
                                let mut sig_refs = sig.references.clone();
                                if sig_refs.len() != refs.len() {
                                    sig_refs.retain(|x| !x.optional);
                                }
                                sig_refs
                            };
                            // if we don't have a matching OutReference count by this point, this ain't our func, skip
                            if sig_refs.len() != refs.len() {
                                return Ok(false);
                            }
                            for i in 0..refs.len() {
                                if !sig_refs[i].skip {
                                    add_symbol_from_reference(obj, &refs[i], &sig_refs[i])?;
                                }
                            }

                            // if we're ultimately just trying to find one func, and we found it just now, get outta here, we've done what we need to
                            if matching_one_func {
                                return Ok(true);
                            }

                            break;
                        }
                    }
                }
                _ => {
                    todo!("Func only has a size {:X}, need to find address!", size);
                }
            }
        }
    }

    Ok(true)
}

// check_signature - this is where we actually compare the instruction bytes/pattern masks to make sure we've got the function locked down
fn check_signature(obj: &ObjInfo, addr: u32, sig: &String) -> Result<bool> {
    // get the data bytes starting at addr
    let section = obj.sections.at_address(addr)?.1;
    let bytes = section.data_range(addr, 0)?; // the data bytes
    let signature = STANDARD.decode(sig)?; // the signature
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

pub fn apply_signatures(obj: &mut ObjInfo) -> Result<()> {
    apply_signature(obj, "_purecall")?;
    // older xexes may not have this function actually
    apply_signature(obj, "_beginthreadex")?;

    if apply_signature(obj, "atexit")? {
        apply_signature(obj, "post-atexit")?;
        // atexit -> will lead to realloc -> malloc/free
    }

    // funcs to find:
    // calloc, _errno, strstr, strrchr, isalpha and all the other char checkers
    // _CxxThrowException
    // __security_init_cookie - will need to find this for yc bounds
    // _NLG_Notify/__NLG_Dispatch
    // _CallSettingFrame/__NLG_Return
    // strncmp, printf

    // if we have RTTI, these two *should* exist somewhere:
    // typeid - is a C except func with one exception
    // dynamic_cast - is a C except func with one exception
    // look for the strings "Bad dynamic_cast!" and "no RTTI data!"

    // XGetOverlappedResult - can't rely on signature, two versions, one with reg intrinsics and one without
    // CreateThread - can't rely on signature, two versions, one with reg intrinsics and one without
    // look at more XAPILIB funcs, LIBCMT funcs

    Ok(())
}
