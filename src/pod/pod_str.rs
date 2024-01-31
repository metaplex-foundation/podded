use bytemuck::{Pod, Zeroable};
use std::fmt::{Debug, Display};
use std::ops::Deref;
use std::str;

use crate::ZeroCopy;

/// Struct representing a "pod-enabled" `str`.
#[repr(C)]
#[derive(Copy, Clone, PartialEq)]
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

    /// Copy the content of a `&str` into the pod str.
    pub fn copy_from_str(&mut self, string: &str) {
        self.copy_from_slice(string.as_bytes())
    }
}

unsafe impl<const MAX_SIZE: usize> Pod for PodStr<MAX_SIZE> {}

unsafe impl<const MAX_SIZE: usize> Zeroable for PodStr<MAX_SIZE> {}

impl<const MAX_SIZE: usize> ZeroCopy<'_, PodStr<MAX_SIZE>> for PodStr<MAX_SIZE> {}

impl<const MAX_SIZE: usize> Default for PodStr<MAX_SIZE> {
    fn default() -> Self {
        Self {
            value: [0; MAX_SIZE],
        }
    }
}

impl<const MAX_SIZE: usize> Deref for PodStr<MAX_SIZE> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        let end_index = self
            .value
            .iter()
            .position(|&x| x == b'\0')
            .unwrap_or(MAX_SIZE);

        unsafe { str::from_utf8_unchecked(&self.value[..end_index]) }
    }
}

impl<const MAX_SIZE: usize> Display for PodStr<MAX_SIZE> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(self)
    }
}

impl<const MAX_SIZE: usize> Debug for PodStr<MAX_SIZE> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(self)
    }
}

impl<const MAX_SIZE: usize> From<&str> for PodStr<MAX_SIZE> {
    fn from(s: &str) -> Self {
        let mut value = [0; MAX_SIZE];
        let length = std::cmp::min(s.len(), MAX_SIZE);
        value[..length].clone_from_slice(&s.as_bytes()[..length]);
        Self { value }
    }
}

impl<const MAX_SIZE: usize> From<String> for PodStr<MAX_SIZE> {
    fn from(s: String) -> Self {
        s.as_str().into()
    }
}

impl<const MAX_SIZE: usize> PartialEq<str> for PodStr<MAX_SIZE> {
    fn eq(&self, other: &str) -> bool {
        self.deref() == other
    }
}

#[cfg(test)]
mod tests {
    use crate::pod::PodStr;

    #[test]
    fn test_from() {
        let str = PodStr::<10>::from("str");
        assert_eq!(&str, "str");
    }

    #[test]
    fn test_copy_from_slice() {
        let mut str = PodStr::<10>::from("empty");
        assert_eq!(&str, "empty");

        // Copy a slice that is equal to the max size.
        str.copy_from_str("emptyempty");
        assert_eq!(&str, "emptyempty");

        // Copy a slice that is smaller than the max size.
        str.copy_from_str("empty");
        assert_eq!(&str, "empty");

        // Copy a slice that is bigger than the max size.
        str.copy_from_str("emptyemptyempty");
        assert_eq!(&str, "emptyempty");
    }
}
