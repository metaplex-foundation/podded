use bytemuck::{Pod, Zeroable};
use std::fmt::{Debug, Display};

use crate::pod::Nullable;

pub trait IntegerSentinel: Pod + Default + PartialEq + Debug {
    const NONE_VALUE: Self;
}

macro_rules! impl_integer_sentinel {
    ($($t:ty => $sentinel:expr),*) => {
        $(
            impl IntegerSentinel for $t {
                const NONE_VALUE: Self = $sentinel;
            }
        )*
    };
}

impl_integer_sentinel! {
    u8 => u8::MAX,
    u16 => u16::MAX,
    u32 => u32::MAX,
    u64 => u64::MAX,
    u128 => u128::MAX,
    i8 => i8::MIN,
    i16 => i16::MIN,
    i32 => i32::MIN,
    i64 => i64::MIN,
    i128 => i128::MIN
}

#[repr(transparent)]
#[derive(Copy, Clone, Pod, Zeroable, PartialEq, Eq, Hash)]
pub struct OptionalInteger<T> {
    value: T,
}

impl<T: IntegerSentinel> Default for OptionalInteger<T> {
    fn default() -> Self {
        Self::none()
    }
}

impl<T: IntegerSentinel> OptionalInteger<T> {
    #[inline]
    pub fn new(value: Option<T>) -> Self {
        Self {
            value: value.unwrap_or(T::NONE_VALUE),
        }
    }

    #[inline]
    pub fn some(value: T) -> Self {
        assert_ne!(value, T::NONE_VALUE, "Cannot use sentinel value as Some");
        Self { value }
    }

    #[inline]
    pub fn none() -> Self {
        Self {
            value: T::NONE_VALUE,
        }
    }

    #[inline]
    pub fn value(&self) -> Option<T> {
        if self.value != T::NONE_VALUE {
            Some(self.value)
        } else {
            None
        }
    }

    #[inline]
    pub fn set(&mut self, value: Option<T>) {
        if let Some(v) = value {
            assert_ne!(v, T::NONE_VALUE, "Cannot use sentinel value as Some");
        }

        self.value = value.unwrap_or(T::NONE_VALUE);
    }

    #[inline]
    pub fn take(&mut self) -> Option<T> {
        let result = self.value();
        self.value = T::NONE_VALUE;
        result
    }
}

impl<T: IntegerSentinel> Nullable for OptionalInteger<T> {
    #[inline]
    fn is_some(&self) -> bool {
        self.value != T::NONE_VALUE
    }

    #[inline]
    fn is_none(&self) -> bool {
        self.value == T::NONE_VALUE
    }
}

impl<T: IntegerSentinel> From<Option<T>> for OptionalInteger<T> {
    fn from(value: Option<T>) -> Self {
        Self::new(value)
    }
}

impl<T: IntegerSentinel> From<OptionalInteger<T>> for Option<T> {
    fn from(opt: OptionalInteger<T>) -> Self {
        opt.value()
    }
}

impl<T: IntegerSentinel + Debug> Debug for OptionalInteger<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value() {
            Some(v) => write!(f, "Some({:?})", v),
            None => write!(f, "None"),
        }
    }
}

impl<T: IntegerSentinel + Display> Display for OptionalInteger<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value() {
            Some(v) => write!(f, "{}", v),
            None => write!(f, "None"),
        }
    }
}

pub type OptionalU8 = OptionalInteger<u8>;
pub type OptionalU16 = OptionalInteger<u16>;
pub type OptionalU32 = OptionalInteger<u32>;
pub type OptionalU64 = OptionalInteger<u64>;
pub type OptionalU128 = OptionalInteger<u128>;

pub type OptionalI8 = OptionalInteger<i8>;
pub type OptionalI16 = OptionalInteger<i16>;
pub type OptionalI32 = OptionalInteger<i32>;
pub type OptionalI64 = OptionalInteger<i64>;
pub type OptionalI128 = OptionalInteger<i128>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_optional_u8() {
        let none = OptionalU8::none();
        assert!(none.is_none());
        assert_eq!(none.value(), None);

        let some = OptionalU8::some(42);
        assert!(some.is_some());
        assert_eq!(some.value(), Some(42));

        let from_option = OptionalU8::from(Some(100));
        assert_eq!(from_option.value(), Some(100));

        let from_none = OptionalU8::from(None);
        assert_eq!(from_none.value(), None);
    }

    #[test]
    fn test_optional_i32() {
        let none = OptionalI32::none();
        assert!(none.is_none());
        assert_eq!(none.value(), None);

        let some = OptionalI32::some(-42);
        assert!(some.is_some());
        assert_eq!(some.value(), Some(-42));

        let positive = OptionalI32::some(100);
        assert_eq!(positive.value(), Some(100));
    }

    #[test]
    fn test_optional_u64() {
        let mut opt = OptionalU64::some(1000);
        assert_eq!(opt.value(), Some(1000));

        opt.set(Some(2000));
        assert_eq!(opt.value(), Some(2000));

        opt.set(None);
        assert_eq!(opt.value(), None);

        opt.set(Some(3000));
        let taken = opt.take();
        assert_eq!(taken, Some(3000));
        assert_eq!(opt.value(), None);
    }

    #[test]
    #[should_panic(expected = "Cannot use sentinel value as Some")]
    fn test_sentinel_value_panic_u8() {
        OptionalU8::some(u8::MAX);
    }

    #[test]
    #[should_panic(expected = "Cannot use sentinel value as Some")]
    fn test_sentinel_value_panic_i32() {
        OptionalI32::some(i32::MIN);
    }

    #[test]
    fn test_conversions() {
        let opt_u16 = OptionalU16::from(Some(1234u16));
        let value: Option<u16> = opt_u16.into();
        assert_eq!(value, Some(1234));

        let opt_none = OptionalU16::from(None);
        let none_value: Option<u16> = opt_none.into();
        assert_eq!(none_value, None);
    }

    #[test]
    fn test_debug_display() {
        let some = OptionalU32::some(42);
        assert_eq!(format!("{:?}", some), "Some(42)");
        assert_eq!(format!("{}", some), "42");

        let none = OptionalU32::none();
        assert_eq!(format!("{:?}", none), "None");
        assert_eq!(format!("{}", none), "None");
    }

    #[test]
    fn test_pod_properties() {
        use std::mem;

        assert_eq!(mem::size_of::<OptionalU8>(), mem::size_of::<u8>());
        assert_eq!(mem::size_of::<OptionalU16>(), mem::size_of::<u16>());
        assert_eq!(mem::size_of::<OptionalU32>(), mem::size_of::<u32>());
        assert_eq!(mem::size_of::<OptionalU64>(), mem::size_of::<u64>());
        assert_eq!(mem::size_of::<OptionalI8>(), mem::size_of::<i8>());
        assert_eq!(mem::size_of::<OptionalI16>(), mem::size_of::<i16>());
        assert_eq!(mem::size_of::<OptionalI32>(), mem::size_of::<i32>());
        assert_eq!(mem::size_of::<OptionalI64>(), mem::size_of::<i64>());
    }
}
