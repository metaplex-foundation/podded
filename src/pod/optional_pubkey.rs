use bytemuck::{Pod, Zeroable};
use solana_program::pubkey::Pubkey;

use crate::pod::Nullable;

#[repr(C)]
#[derive(Copy, Clone, Default, Pod, Zeroable, PartialEq, Eq, Hash, Debug)]
pub struct OptionalPubkey(pub Pubkey);

impl Nullable for OptionalPubkey {
    fn is_some(&self) -> bool {
        self.0 != Pubkey::default()
    }

    fn is_none(&self) -> bool {
        self.0 == Pubkey::default()
    }
}

impl OptionalPubkey {
    #[inline]
    pub fn new(value: Pubkey) -> Self {
        Self(value)
    }

    #[inline]
    pub fn value(&self) -> Option<&Pubkey> {
        if self.is_some() {
            Some(&self.0)
        } else {
            None
        }
    }

    #[inline]
    pub fn value_mut(&mut self) -> Option<&mut Pubkey> {
        if self.is_some() {
            Some(&mut self.0)
        } else {
            None
        }
    }
}
