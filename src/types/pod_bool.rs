use bytemuck::{Pod, Zeroable};

/// A `PodBool` value representing a boolean `true`.
pub const POD_TRUE: PodBool = PodBool(1);

/// A `PodBool` value representing a boolean `false`.
pub const POD_FALSE: PodBool = PodBool(0);

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
