use bytemuck::Pod;

pub mod collections;
pub mod pod;
pub mod types;

/// Trait to represent types with zero-copy deserialization.
pub trait ZeroCopy<'a, T: Pod>
where
    Self: Pod,
{
    fn load(data: &'a [u8]) -> &'a Self {
        bytemuck::from_bytes(&data[..std::mem::size_of::<T>()])
    }

    fn load_mut(data: &'a mut [u8]) -> &'a mut Self {
        bytemuck::from_bytes_mut(&mut data[..std::mem::size_of::<T>()])
    }
}
