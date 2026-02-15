use std::fs::File;

use anyhow::Result;
use serde::{de::Error, Deserialize, Deserializer};

use super::*;
use crate::{
    analysis::cfa::{AnalyzerState, FunctionInfo},
    obj::{ObjArchitecture, ObjInfo, ObjKind, ObjSection, ObjSectionKind},
};

fn bytestr_to_bytes<'de, D>(deserializer: D) -> Result<Vec<u8>, D::Error>
where D: Deserializer<'de> {
    let hex_str = String::deserialize(deserializer)?;

    if hex_str.len() % 2 != 0 {
        return Err(D::Error::custom("hex string must have even length"));
    }

    let bytes = (0..hex_str.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex_str[i..i + 2], 16))
        .collect::<Result<Vec<u8>, _>>()
        .map_err(D::Error::custom)?;

    Ok(bytes)
}

fn get_fn_start<'de, D>(deserializer: D) -> Result<u32, D::Error>
where D: Deserializer<'de> {
    let hex_str = String::deserialize(deserializer)?;
    if hex_str.len() != 8 {
        return Err(D::Error::custom(format!("expected 8 hex chars, got {}", hex_str.len())));
    }
    let start = u32::from_str_radix(&*hex_str, 16).map_err(D::Error::custom)?;
    Ok(start)
}

#[derive(Debug, Deserialize)]
struct TestConfig {
    test_id: u32,
    #[serde(deserialize_with = "get_fn_start")]
    function_start: u32,
    #[serde(deserialize_with = "bytestr_to_bytes")]
    function_bytes: Vec<u8>,
}

// helper func to create an ObjInfo
fn make_code_section(base_addr: u32, instructions: &[u8]) -> ObjSection {
    ObjSection {
        name: ".text".into(),
        kind: ObjSectionKind::Code,
        address: base_addr as u64,
        size: instructions.len() as u64,
        data: Vec::from(instructions),
        align: 0x10000,
        ..Default::default()
    }
}

// fn make_data_section

fn create_dummy_obj(section: ObjSection) -> ObjInfo {
    let mut sections: Vec<ObjSection> = vec![];
    sections.push(section);
    ObjInfo::new(ObjKind::Executable, ObjArchitecture::PowerPc, "test.exe".into(), vec![], sections)
}

// helper func to insert function asm into an ObjInfo. could put it in here directly, or read it from a .txt

// pub struct FunctionInfo {
//     pub analyzed: bool,
//     pub end: Option<SectionAddress>,
//     pub slices: Option<FunctionSlices>,
// }

#[test]
fn test_super_basic_cfa() -> Result<()> {
    let test_cfg: Vec<TestConfig> =
        serde_yaml::from_reader(File::open("assets/tests/cfa_tests.yml")?)?;
    let cur_test = &test_cfg[0];
    assert_eq!(cur_test.test_id, 0);
    let obj =
        create_dummy_obj(make_code_section(cur_test.function_start, &cur_test.function_bytes));
    let mut state = AnalyzerState::default();
    let start_addr = SectionAddress::new(0, cur_test.function_start);
    state.functions.insert(start_addr, FunctionInfo { analyzed: false, end: None, slices: None });
    // CFA completed with no errors
    let res = state.process_function_at(&obj, start_addr).unwrap_or_else(|e| panic!("{:?}", e));
    // we have one more function
    assert!(res);
    assert_eq!(state.functions.len(), 1);
    let func = state.functions.get(&start_addr);
    assert!(func.is_some());
    let func = func.unwrap();
    assert!(func.is_function());
    // does the detected function end match our expected end?
    assert_eq!(func.end, Some(start_addr + cur_test.function_bytes.len() as u32));
    // assert that we have slices
    assert!(func.slices.is_some());
    let slices = func.slices.as_ref().unwrap();
    // this func should only have 1 basic block
    assert_eq!(slices.blocks.len(), 1);
    Ok(())
}

// would prefer 2-3 test functions that cover each JumpTableType
// pub enum JumpTableType {
//     // the table came from an lwzx, contains absolute addresses
//     Absolute,
//     // the table came from an lbzx, contains relative byte offsets (no rlwinm before the bctr)
//     RelativeBytes(Option<RelocationTarget>),
//     // the table came from an lbzx, contains relative byte offsets that we must multiply by 4
//     RelativeBytesTimes4(Option<RelocationTarget>),
//     // the table came from an lhzx, contains relative short offsets (no rlwinm before the bctr)
//     RelativeShorts(Option<RelocationTarget>),
//     // the table came from an lhzx, contains relative short offsets that we must multiply by 2
//     RelativeShortsTimes2(Option<RelocationTarget>),
// }

#[test]
fn test_jump_table_absolute_1() -> Result<()> {
    let test_cfg: Vec<TestConfig> =
        serde_yaml::from_reader(File::open("assets/tests/cfa_tests.yml")?)?;
    let cur_test = &test_cfg[1];
    assert_eq!(cur_test.test_id, 1);
    let obj =
        create_dummy_obj(make_code_section(cur_test.function_start, &cur_test.function_bytes));
    let mut state = AnalyzerState::default();
    let start_addr = SectionAddress::new(0, cur_test.function_start);
    // CFA completed with no errors
    let res = state.process_function_at(&obj, start_addr).unwrap_or_else(|e| panic!("{:?}", e));
    // we have one more function
    assert!(res);
    assert_eq!(state.functions.len(), 1);
    let func = state.functions.get(&start_addr);
    assert!(func.is_some());
    let func = func.unwrap();
    assert!(func.is_function());
    // does the detected function end match our expected end?
    assert_eq!(func.end, Some(start_addr + cur_test.function_bytes.len() as u32));
    // for this func, we should have 1 jump table
    assert_eq!(state.jump_tables.is_empty(), false);
    assert_eq!(state.jump_tables.len(), 1);
    // and there should be 4 entries in it
    let jump_table_entry = state.jump_tables.get(&SectionAddress::new(0, 0x820869fc));
    assert!(jump_table_entry.is_some());
    assert_eq!(*jump_table_entry.unwrap(), 4);
    // we should also have a lotta basic blocks
    assert!(func.slices.is_some());
    let slices = func.slices.as_ref().unwrap();
    assert!(slices.blocks.len() > 5); // idk the exact number but i know it's more than 5
    Ok(())
}

#[test]
fn test_jump_table_absolute_2() -> Result<()> {
    let test_cfg: Vec<TestConfig> =
        serde_yaml::from_reader(File::open("assets/tests/cfa_tests.yml")?)?;
    let cur_test = &test_cfg[2];
    assert_eq!(cur_test.test_id, 2);
    let obj =
        create_dummy_obj(make_code_section(cur_test.function_start, &cur_test.function_bytes));
    let mut state = AnalyzerState::default();
    let start_addr = SectionAddress::new(0, cur_test.function_start);
    // CFA completed with no errors
    let res = state.process_function_at(&obj, start_addr).unwrap_or_else(|e| panic!("{:?}", e));
    // we have one more function
    assert!(res);
    assert_eq!(state.functions.len(), 1);
    let func = state.functions.get(&start_addr);
    assert!(func.is_some());
    let func = func.unwrap();
    assert!(func.is_function());
    // does the detected function end match our expected end?
    assert_eq!(func.end, Some(start_addr + cur_test.function_bytes.len() as u32));
    // for this func, we should have 1 jump table
    assert_eq!(state.jump_tables.is_empty(), false);
    assert_eq!(state.jump_tables.len(), 1);
    // and there should be 4 entries in it
    let jump_table_entry = state.jump_tables.get(&SectionAddress::new(0, 0x827f9434));
    assert!(jump_table_entry.is_some());
    assert_eq!(*jump_table_entry.unwrap(), 4);
    // we should also have a lotta basic blocks
    assert!(func.slices.is_some());
    let slices = func.slices.as_ref().unwrap();
    assert!(slices.blocks.len() > 5); // idk the exact number but i know it's more than 5
    Ok(())
}

// this one's also got VMX! for added fun
#[test]
fn test_jump_table_absolute_3() -> Result<()> {
    let test_cfg: Vec<TestConfig> =
        serde_yaml::from_reader(File::open("assets/tests/cfa_tests.yml")?)?;
    let cur_test = &test_cfg[3];
    assert_eq!(cur_test.test_id, 3);
    let obj =
        create_dummy_obj(make_code_section(cur_test.function_start, &cur_test.function_bytes));
    let mut state = AnalyzerState::default();
    let start_addr = SectionAddress::new(0, cur_test.function_start);
    // CFA completed with no errors
    let res = state.process_function_at(&obj, start_addr).unwrap_or_else(|e| panic!("{:?}", e));
    // we have one more function
    assert!(res);
    assert_eq!(state.functions.len(), 1);
    let func = state.functions.get(&start_addr);
    assert!(func.is_some());
    let func = func.unwrap();
    assert!(func.is_function());
    // does the detected function end match our expected end?
    assert_eq!(func.end, Some(start_addr + cur_test.function_bytes.len() as u32));
    // for this func, we should have 1 jump table
    assert_eq!(state.jump_tables.is_empty(), false);
    assert_eq!(state.jump_tables.len(), 1);
    // and there should be 4 entries in it
    let jump_table_entry = state.jump_tables.get(&SectionAddress::new(0, 0x82fbb464));
    assert!(jump_table_entry.is_some());
    assert_eq!(*jump_table_entry.unwrap(), 4);
    // we should also have a lotta basic blocks
    assert!(func.slices.is_some());
    let slices = func.slices.as_ref().unwrap();
    assert!(slices.blocks.len() > 5); // idk the exact number but i know it's more than 5
    Ok(())
}
