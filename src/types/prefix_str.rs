use std::ops::{Deref, DerefMut};
use std::str::{from_utf8_unchecked, from_utf8_unchecked_mut};

macro_rules! prefix_str {
    ( ($n:tt, $p:tt), $(($name:tt, $prefix:tt)),+ ) => {
        prefix_str!(($n, $p));
        prefix_str!($( ($name, $prefix) ),+);
    };
    ( ($name:tt, $prefix_type:tt) ) => {
        /// A "wrapped-pod" str with a prefix length.
        ///
        /// This is a wrapper around a byte slice that contains a length prefix, which
        /// enables having a str of variable size.
        pub struct $name<'a> {
            /// The bytes representing the str.
            value: &'a [u8],
        }

        impl<'a> $name<'a> {
            /// Loads from a byte slice.
            pub fn from_bytes(bytes: &'a [u8]) -> Self {
                let (length, value) = bytes.split_at(std::mem::size_of::<$prefix_type>());

                let length = bytemuck::from_bytes::<$prefix_type>(length);
                let value = bytemuck::cast_slice(&value[..*length as usize]);

                Self { value }
            }
        }
    };
}

macro_rules! prefix_str_mut {
    ( ($n:tt, $p:tt), $(($name:tt, $prefix:tt)),+ ) => {
        prefix_str_mut!(($n, $p));
        prefix_str_mut!($( ($name, $prefix) ),+);
    };
    ( ($name:tt, $prefix_type:tt) ) => {
        /// A mutable "wrapped-pod" str with a prefix length.
        ///
        /// This is a wrapper around a byte slice that contains a length prefix, which
        /// enables having a str of variable size.
        pub struct $name<'a> {
            /// The bytes representing the str.
            value: &'a mut [u8],
        }

        impl<'a> $name<'a> {
            /// Creates a new reference from a byte slice.
            ///
            /// The `data` is used a the storage for the type.
            pub fn new(data: &'a mut [u8]) -> Self {
                let type_length = std::mem::size_of::<$prefix_type>();
                let length = (data.len().saturating_sub(type_length) as $prefix_type).to_le_bytes();
                data[..type_length].copy_from_slice(&length);
                Self::from_bytes_mut(data)
            }

            /// Loads from a mutable byte slice.
            pub fn from_bytes_mut(bytes: &'a mut [u8]) -> Self {
                let (length, value) = bytes.split_at_mut(std::mem::size_of::<$prefix_type>());

                let length = bytemuck::from_bytes_mut::<$prefix_type>(length);
                let value = bytemuck::cast_slice_mut(&mut value[..*length as usize]);

                Self { value }
            }

            /// Copy the content of a slice into the prefixed str.
            pub fn copy_from_slice(&mut self, slice: &[u8]) {
                let length = std::cmp::min(self.value.len(), slice.len());
                self.value[..length].clone_from_slice(&slice[..length]);
                self.value[length..].fill(0);
            }

            /// Copy the content of a `&str` into the prefixed str.
            pub fn copy_from_str(&mut self, string: &str) {
                self.copy_from_slice(string.as_bytes())
            }
        }

        impl<'a> DerefMut for $name<'a> {
            #[inline]
            fn deref_mut(&mut self) -> &mut str {
                unsafe { from_utf8_unchecked_mut(self.value) }
            }
        }
    };
}

macro_rules! prefix_str_type {
    ( ($n:tt, $p:tt), $(($name:tt, $prefix:tt)),+ ) => {
        prefix_str_type!(($n, $p));
        prefix_str_type!($( ($name, $prefix) ),+);
    };
    ( ($name:tt, $prefix_type:tt) ) => {
        impl<'a> $name<'a> {
            /// Return the type as a `&str`.
            pub fn as_str(&self) -> &str {
                self
            }

            #[allow(clippy::len_without_is_empty)]
            /// Returns the size (in bytes) of the prefixed str.
            ///
            /// This is different than the `len` method of `str` because it includes the
            /// length of the prefix.
            pub fn size(&self) -> usize {
                std::mem::size_of::<$prefix_type>() + self.value.len()
            }
        }

        impl<'a> Deref for $name<'a> {
            type Target = str;

            #[inline]
            fn deref(&self) -> &str {
                unsafe { from_utf8_unchecked(self.value) }
            }
        }
    };
}

// "read-only" impl
prefix_str!((U8PrefixStr, u8), (U16PrefixStr, u16));
// "mutable" impl
prefix_str_mut!((U8PrefixStrMut, u8), (U16PrefixStrMut, u16));
// "shared" impl
prefix_str_type!(
    (U8PrefixStr, u8),
    (U8PrefixStrMut, u8),
    (U16PrefixStr, u16),
    (U16PrefixStrMut, u16)
);

#[cfg(test)]
mod tests {
    use crate::types::{U16PrefixStr, U16PrefixStrMut, U8PrefixStr, U8PrefixStrMut};

    #[test]
    fn test_new() {
        // u8
        let mut data = [0u8; 4];
        let mut prefix_str = U8PrefixStrMut::new(&mut data);
        prefix_str.copy_from_str("str");

        assert_eq!(prefix_str.as_str(), "str");
        assert_eq!(prefix_str.size(), data.len());

        // u16
        let mut data = [0u8; 5];
        let mut prefix_str = U16PrefixStrMut::new(&mut data);
        prefix_str.copy_from_str("str");

        assert_eq!(prefix_str.as_str(), "str");
        assert_eq!(prefix_str.size(), data.len());
    }

    #[test]
    fn test_new_with_shorter_str() {
        // u8
        let mut data = [0u8; 10];
        let mut prefix_str = U8PrefixStrMut::new(&mut data);
        prefix_str.copy_from_str("string");

        assert_eq!(prefix_str.as_str(), "string\0\0\0");

        // u16
        let mut data = [0u8; 11];
        let mut prefix_str = U16PrefixStrMut::new(&mut data);
        prefix_str.copy_from_str("string");

        assert_eq!(prefix_str.as_str(), "string\0\0\0");
    }

    #[test]
    fn test_new_with_larger_str() {
        // u8
        let mut data = [0u8; 4];
        let mut prefix_str = U8PrefixStrMut::new(&mut data);
        prefix_str.copy_from_str("string");

        assert_eq!(prefix_str.as_str(), "str");

        // u16
        let mut data = [0u8; 5];
        let mut prefix_str = U16PrefixStrMut::new(&mut data);
        prefix_str.copy_from_str("string");

        assert_eq!(prefix_str.as_str(), "str");
    }

    #[test]
    fn test_from_bytes() {
        // u8
        let mut data = [0u8; 4];
        data[0] = 3;
        data[1..].copy_from_slice("str".as_bytes());

        let prefix_str = U8PrefixStr::from_bytes(&data);
        assert_eq!(prefix_str.as_str(), "str");

        // u16
        let mut data = [0u8; 5];
        data[..2].copy_from_slice(&3u16.to_le_bytes());
        data[2..].copy_from_slice("str".as_bytes());

        let prefix_str = U16PrefixStr::from_bytes(&data);
        assert_eq!(prefix_str.as_str(), "str");
    }
}
