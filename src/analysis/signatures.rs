use std::{collections::HashMap, sync::LazyLock};

use anyhow::{ensure, Ok, Result};
use base64::{engine::general_purpose::STANDARD, Engine};
use memchr::memmem;
use serde::{Deserialize, Serialize};

use crate::{
    analysis::{
        cfa::SectionAddress,
        read_u32,
        tracker::{Relocation, Tracker},
        RelocationTarget,
    },
    obj::{
        ExceptionType::{Normal, C, CXX},
        ObjInfo, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind,
        ObjSymbolKind::{Function, Object},
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

fn apply_entry(obj: &mut ObjInfo) -> Result<bool> {
    let Some(entry) = obj.entry else {
        return Ok(false);
    };
    let entry_yml = include_str!("../../assets/signatures_x360/entry.yml");
    let entry_sig = {
        let sigs: Vec<FunctionSignature> = serde_yaml::from_str(entry_yml)?;
        sigs[0].clone()
    };
    let entry_addr = SectionAddress::new(obj.sections.at_address(entry)?.0, entry);
    let refs = get_function_references(obj, "entry", &entry_addr)?;
    if entry_sig.references.len() != refs.len() || refs.len() != 18 {
        return Ok(false);
    }

    for i in 0..refs.len() {
        if !entry_sig.references[i].skip {
            add_symbol_from_reference(obj, &refs[i], &entry_sig.references[i])?;
        }
    }

    Ok(true)
}

// returns true if everything was successfully applied
// false if any signature could not be applied
fn apply_signature(obj: &mut ObjInfo, name: &str) -> Result<bool> {
    log::debug!("Name: {}", name);

    let sigs: Vec<FunctionSignature> =
        serde_yaml::from_str(SIGNATURES.get(name).expect("Missing signature!"))?;

    // if this bool is true, then this yml is just multiple known versions of one func we're trying to match
    let matching_one_func = sigs.iter().all(|sig| sig.name == sigs[0].name);

    for sig in sigs {
        let func_sym = obj.symbols.by_name(&*sig.name)?;

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
            let refs = get_function_references(obj, &*sig.name, &sec_addr)?;
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
                            let sig_name_str = String::from(sig.name);
                            add_symbol_from_reference(obj, &cand, &OutReference {
                                name: sig_name_str.clone(),
                                kind: Function,
                                size,
                                optional: false,
                                skip: false,
                            })?;
                            // add function references from this func
                            let refs = get_function_references(obj, &*sig_name_str, &cand)?;
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

fn process_crt(obj: &mut ObjInfo) -> Result<()> {
    let data_sec_idx = obj.sections.by_name(".data")?.expect("where data").0;

    // xri - runtime initializers?
    let (xri_start, xri_end) = {
        let (xria_sym_idx, xria_sym) =
            obj.symbols.by_name("__xri_a")?.expect("we should've found __xri_a at this point!");
        let xriz_sym =
            obj.symbols.by_name("__xri_z")?.expect("we should've found __xri_z at this point!").1;
        let xri_start = xria_sym.address;
        let xri_end = xriz_sym.address;
        let mut new_sym = xria_sym.clone();
        new_sym.size = xri_end - xri_start;
        new_sym.size_known = true;
        obj.symbols.replace(xria_sym_idx, new_sym)?;
        (xri_start, xri_end)
    };

    for addr in (xri_start..xri_end).step_by(4) {
        match addr - xri_start {
            0 => {
                // first entry of xri_a - must be 0
                ensure!(read_u32(&obj.sections[data_sec_idx], addr).unwrap() == 0, "bad __xri_a!");
            }
            4 => {
                // second entry of xri_a - must be __onexitinit
                let exitinit_addr = {
                    let addr = read_u32(&obj.sections[data_sec_idx], addr).unwrap();
                    SectionAddress::new(obj.sections.at_address(addr)?.0, addr)
                };
                add_symbol_from_reference(obj, &exitinit_addr, &OutReference {
                    name: String::from("__onexitinit"),
                    kind: Function,
                    size: 0,
                    optional: false,
                    skip: false,
                })?;
            }
            8 => {
                // third entry of xri_a - must be _ioinit
                let ioinit_addr = {
                    let addr = read_u32(&obj.sections[data_sec_idx], addr).unwrap();
                    SectionAddress::new(obj.sections.at_address(addr)?.0, addr)
                };
                add_symbol_from_reference(obj, &ioinit_addr, &OutReference {
                    name: String::from("_ioinit"),
                    kind: Function,
                    size: 0,
                    optional: false,
                    skip: false,
                })?;
                let pioinit_addr = SectionAddress::new(data_sec_idx, addr);
                add_symbol_from_reference(obj, &pioinit_addr, &OutReference {
                    name: String::from("__pioinit"),
                    kind: Object,
                    size: 4,
                    optional: false,
                    skip: false,
                })?;
            }
            _ => {
                // any further entries are unknown to us, except for the fact they're functions
                let func_addr = {
                    let addr = read_u32(&obj.sections[data_sec_idx], addr).unwrap();
                    SectionAddress::new(obj.sections.at_address(addr)?.0, addr)
                };
                obj.known_functions.entry(func_addr).or_default();
            }
        }
    }

    // xc - static constructors
    let (xc_start, xc_end) = {
        let (xca_sym_idx, xca_sym) =
            obj.symbols.by_name("__xc_a")?.expect("we should've found __xc_a at this point!");
        let xcz_sym =
            obj.symbols.by_name("__xc_z")?.expect("we should've found __xc_z at this point!").1;
        let xc_start = xca_sym.address;
        let xc_end = xcz_sym.address;
        let mut new_sym = xca_sym.clone();
        new_sym.size = xc_end - xc_start;
        new_sym.size_known = true;
        obj.symbols.replace(xca_sym_idx, new_sym)?;
        (xc_start, xc_end)
    };

    let mut num_sinits = 0;
    for addr in (xc_start..xc_end).step_by(4) {
        let sinit_addr = read_u32(&obj.sections[data_sec_idx], addr).unwrap();
        if sinit_addr != 0 {
            let sinit_sec_addr =
                SectionAddress::new(obj.sections.at_address(sinit_addr)?.0, sinit_addr);
            obj.known_functions.entry(sinit_sec_addr).or_default();
            num_sinits += 1;
        }
    }
    log::info!("Found {} known static initializer funcs!", num_sinits);

    let (xi_start, xi_end) = {
        let (xia_sym_idx, xia_sym) =
            obj.symbols.by_name("__xi_a")?.expect("we should've found __xi_a at this point!");
        let xiz_sym =
            obj.symbols.by_name("__xi_z")?.expect("we should've found __xi_z at this point!").1;
        let xi_start = xia_sym.address;
        let xi_end = xiz_sym.address;
        let mut new_sym = xia_sym.clone();
        new_sym.size = xi_end - xi_start;
        new_sym.size_known = true;
        obj.symbols.replace(xia_sym_idx, new_sym)?;
        (xi_start, xi_end)
    };

    // TODO adjust the logic of this loop to match xri, namely other funcs than __initstdio and __initmbctable
    for addr in (xi_start..xi_end).step_by(4) {
        let cur_addr = read_u32(&obj.sections[data_sec_idx], addr).unwrap();
        if cur_addr != 0 {
            let cur_sec_addr = SectionAddress::new(obj.sections.at_address(cur_addr)?.0, cur_addr);
            obj.known_functions.entry(cur_sec_addr).or_default();
        }
    }

    let (xp_start, xp_end) = {
        let (xpa_sym_idx, xpa_sym) =
            obj.symbols.by_name("__xp_a")?.expect("we should've found __xp_a at this point!");
        let xpz_sym =
            obj.symbols.by_name("__xp_z")?.expect("we should've found __xp_z at this point!").1;
        let xp_start = xpa_sym.address;
        let xp_end = xpz_sym.address;
        let mut new_sym = xpa_sym.clone();
        new_sym.size = xp_end - xp_start;
        new_sym.size_known = true;
        obj.symbols.replace(xpa_sym_idx, new_sym)?;
        (xp_start, xp_end)
    };
    for addr in (xp_start..xp_end).step_by(4) {
        let cur_addr = read_u32(&obj.sections[data_sec_idx], addr).unwrap();
        if cur_addr != 0 {
            let cur_sec_addr = SectionAddress::new(obj.sections.at_address(cur_addr)?.0, cur_addr);
            obj.known_functions.entry(cur_sec_addr).or_default();
        }
    }

    let (xt_start, xt_end) = {
        let (xta_sym_idx, xta_sym) =
            obj.symbols.by_name("__xt_a")?.expect("we should've found __xt_a at this point!");
        let xtz_sym =
            obj.symbols.by_name("__xt_z")?.expect("we should've found __xt_z at this point!").1;
        let xt_start = xta_sym.address;
        let xt_end = xtz_sym.address;
        let mut new_sym = xta_sym.clone();
        new_sym.size = xt_end - xt_start;
        new_sym.size_known = true;
        obj.symbols.replace(xta_sym_idx, new_sym)?;
        (xt_start, xt_end)
    };
    for addr in (xt_start..xt_end).step_by(4) {
        let cur_addr = read_u32(&obj.sections[data_sec_idx], addr).unwrap();
        if cur_addr != 0 {
            let cur_sec_addr = SectionAddress::new(obj.sections.at_address(cur_addr)?.0, cur_addr);
            obj.known_functions.entry(cur_sec_addr).or_default();
        }
    }

    Ok(())
}

pub fn apply_signatures(obj: &mut ObjInfo) -> Result<()> {
    if apply_entry(obj)? {
        log::debug!("Entry successfully parsed!");
        // then CRT objects using the funcs we found from the entry point
        if apply_signature(obj, "post-entry")? {
            log::debug!("Post-entry successfully parsed!");
            // after all that's been applied, peruse through the xa/z's
            process_crt(obj)?;
        }
    }

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
