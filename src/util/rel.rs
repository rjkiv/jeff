use crate::obj::ObjRelocKind;

/// REL relocation.
#[derive(Debug, Clone)]
pub struct RelReloc {
    /// Relocation kind.
    pub kind: ObjRelocKind,
    /// Source section index.
    pub section: u8,
    /// Source address.
    pub address: u32,
    /// Target module ID.
    pub module_id: u32,
    /// Target section index.
    pub target_section: u8,
    /// Target addend within section.
    /// If target module ID is 0 (DOL), this is an absolute address.
    pub addend: u32,

    // EXTRA for matching
    pub original_section: u8,
    pub original_target_section: u8,
}
