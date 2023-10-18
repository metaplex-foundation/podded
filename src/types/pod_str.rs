use bytemuck::{Pod, Zeroable};
use std::fmt::Display;
use std::ops::Deref;
use std::str;

use crate::ZeroCopy;

/// Struct representing a "pod-enabled" `str`.
#[repr(C)]
#[derive(Copy, Clone)]
pub struct PodStr<const MAX_SIZE: usize> {
    /// The bytes of the string.
    pub value: [u8; MAX_SIZE],
}

impl<const MAX_SIZE: usize> PodStr<MAX_SIZE> {
    pub fn copy_from_slice(&mut self, slice: &[u8]) {
        let length = std::cmp::min(slice.len(), MAX_SIZE);
        self.value[..length].clone_from_slice(&slice[..length]);
        self.value[length..].fill(0);
    }
}

unsafe impl<const MAX_SIZE: usize> Pod for PodStr<MAX_SIZE> {}

unsafe impl<const MAX_SIZE: usize> Zeroable for PodStr<MAX_SIZE> {}

impl<const MAX_SIZE: usize> Deref for PodStr<MAX_SIZE> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<const MAX_SIZE: usize> Display for PodStr<MAX_SIZE> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let end_index = self
            .value
            .iter()
            .position(|&x| x == b'\0')
            .unwrap_or(MAX_SIZE);
        // return a copy of the str without any padding bytes
        formatter.write_str(unsafe { str::from_utf8_unchecked(&self.value[..end_index]) })
    }
}

impl<const MAX_SIZE: usize> From<String> for PodStr<MAX_SIZE> {
    fn from(s: String) -> Self {
        let mut value = [0; MAX_SIZE];
        let length = std::cmp::min(s.len(), MAX_SIZE);
        value[..length].clone_from_slice(&s.as_bytes()[..length]);
        Self { value }
    }
}

impl<'a, const MAX_SIZE: usize> ZeroCopy<'a, PodStr<MAX_SIZE>> for PodStr<MAX_SIZE> {}
