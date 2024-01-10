use bytemuck::{Pod, Zeroable};

/// Used for "pod-enabled" types that can have a `None` value.
pub trait Nullable: Pod {
    /// Indicates if the value is `Some`.
    fn is_some(&self) -> bool;

    /// Indicates if the value is `None`.
    fn is_none(&self) -> bool;
}

/// A "pod-enabled" type that can be used as an `Option<T>` without
/// requiring extra space to indicate if the value is `Some` or `None`.
///
/// This can be used when a specific value of `T` indicates that its
/// value is `None`.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct PodOption<T: Nullable>(T);

unsafe impl<T: Nullable> Pod for PodOption<T> {}

unsafe impl<T: Nullable> Zeroable for PodOption<T> {}

impl<T: Nullable> PodOption<T> {
    pub fn new(value: T) -> Self {
        Self(value)
    }

    pub fn value(&self) -> Option<&T> {
        if self.0.is_some() {
            Some(&self.0)
        } else {
            None
        }
    }

    pub fn value_mut(&mut self) -> Option<&mut T> {
        if self.0.is_some() {
            Some(&mut self.0)
        } else {
            None
        }
    }
}
