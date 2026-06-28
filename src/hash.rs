// Copyright © 2023-2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

//! Implementations of [`Hash`].

use crate::CircularBuffer;
use crate::FixedCircularBuffer;
use core::hash::Hash;
use core::hash::Hasher;
use core::ops::Deref;

#[cfg(feature = "alloc")]
use crate::HeapCircularBuffer;

impl<T> Hash for CircularBuffer<T>
where
    T: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        // TODO: Use `Hasher::write_length_prefix()` once it's stabilized
        self.inner.size.hash(state);
        self.iter().for_each(|item| item.hash(state));
    }
}

impl<T, const N: usize> Hash for FixedCircularBuffer<T, N>
where
    T: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.deref().hash(state);
    }
}

#[cfg(feature = "alloc")]
impl<T> Hash for HeapCircularBuffer<T>
where
    T: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.deref().hash(state);
    }
}
