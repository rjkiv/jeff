use super::*;
use crate::{
    analysis::{cfa::AnalyzerState, slices::FunctionSlices},
    obj::{
        ObjArchitecture, ObjInfo, ObjKind, ObjSection, ObjSectionKind, ObjSymbol, ObjSymbolFlagSet,
        ObjSymbolKind, ObjSymbolKind::Section, ObjSymbolScope,
    },
};

// helper func to create an ObjInfo
fn make_code_section(base_addr: u32, instructions: &[u32]) -> ObjSection {
    let data: Vec<u8> = instructions.iter().flat_map(|w| w.to_be_bytes()).collect();
    ObjSection {
        name: ".text".into(),
        kind: ObjSectionKind::Code,
        address: base_addr as u64,
        size: data.len() as u64,
        data,
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
fn test_super_basic_cfa() {
    let section = make_code_section(0x82000000, &[
        0x38600000, // li r3, 0
        0x4e800020, // blr
    ]);
    let obj = create_dummy_obj(section);
    let mut state = AnalyzerState::default();
    let start_addr = SectionAddress::new(0, 0x82000000);
    let expected_end_addr = SectionAddress::new(0, 0x82000008);
    let res = state.process_function_at(&obj, start_addr);
    // CFA completed with no errors
    assert!(res.is_ok_and(|x| x == true));
    // we have one more function
    assert_eq!(state.functions.len(), 1);
    let func = state.functions.get(&start_addr);
    assert!(func.is_some());
    let func = func.unwrap();
    assert!(func.is_function());
    // does the detected function end match our expected end?
    assert_eq!(func.end, Some(expected_end_addr));
    // assert some slice stuff?
}
