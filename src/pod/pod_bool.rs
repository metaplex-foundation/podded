use bytemuck::{Pod, Zeroable};

#[repr(C)]
#[derive(Copy, Clone, Default, Pod, Zeroable)]
pub struct PodBool(u8);

impl From<bool> for PodBool {
    fn from(b: bool) -> Self {
        Self(b.into())
    }
}

impl From<&bool> for PodBool {
    fn from(b: &bool) -> Self {
        Self((*b).into())
    }
}

impl From<&PodBool> for bool {
    fn from(b: &PodBool) -> Self {
        b.0 != 0
    }
}

impl From<PodBool> for bool {
    fn from(b: PodBool) -> Self {
        b.0 != 0
    }
}
