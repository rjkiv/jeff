use crate::obj::ObjSymbolKind;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct SubSignature {
    // a snippet of exact bytes within this signature to help narrow down the field to search in
    pub exact_bytes: String,
    // the offset within the function where this snippet occurs
    pub offset: u32,
}

// the possible signature a function can have.
// we need this struct because signatures can vary in size across xexes (for example, some may save/rest regs, some may not)
#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct SignatureCandidate {
    // this signature's size
    pub size: u32,
    // this signature's byte pattern
    pub signature: String,
    #[serde(default)]
    // a subsignature of exact bytes to help narrow down the search for our main signature
    pub subsignature: Option<SubSignature>,
}

// the functions and labels to mark for this FunctionSignature.
#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct FunctionLabel {
    // the name of this function/label
    pub name: String,
    // the offset in the signature bytes to mark this function/label
    pub offset: u32,
    #[serde(default)]
    // if function, the function's size. if this is None, this is a label
    pub size: Option<u32>,
}

// Sleds of labels to add so you don't have to manually write them all out in FunctionLabels
#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct Sled {
    pub name_start: String,
    pub offset: u32,
    pub start: u32,
    pub end: u32,
    pub step: u32,
}

// A function or data reference that our FunctionSignature may call.
#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct OutReference {
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

fn default_section_name() -> String {
    ".text".to_string()
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct FunctionSignature {
    // the name of the function
    pub name: String,
    // the expected section this function would be in. Defaults to .text.
    // useful for .embsec, PSFD00, or other funny microsoft section names
    #[serde(default = "default_section_name")]
    pub section: String,
    #[serde(default)]
    // if this func is found in pdata, the number of exception handlers it has
    pub num_handlers: Option<u8>,
    #[serde(default)]
    // this func's possible signatures
    pub possible_signatures: Vec<SignatureCandidate>,
    #[serde(default)]
    // any additional functions/labels to add for this signature (useful for reg intrinsics, fpctrl, chkstk, etc)
    pub labels: Vec<FunctionLabel>,
    #[serde(default)]
    // label sleds to add (useful for reg intrinsics)
    pub sleds: Vec<Sled>,
    #[serde(default)]
    // the function calls and data references this signature has
    pub references: Vec<OutReference>,
    #[serde(default)]
    // if false, this is allowed to fail (like not all xexes would have memcmp for example)
    pub required: bool,
}
