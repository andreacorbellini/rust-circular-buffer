// Copyright © 2023-2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

use crate::CircularBuffer;
use crate::FixedCircularBuffer;
use core::fmt;
use core::iter;
use core::ops::Deref;

#[cfg(feature = "alloc")]
use crate::HeapCircularBuffer;

#[derive(Default, Copy, Clone)]
struct Placeholder;

impl fmt::Debug for Placeholder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("_")
    }
}

impl<T> fmt::Debug for CircularBuffer<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut list = f.debug_list();
        list.entries(self);
        list.entries(iter::repeat_n(Placeholder, self.capacity() - self.len()));
        list.finish()
    }
}

impl<T, const N: usize> fmt::Debug for FixedCircularBuffer<T, N>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

#[cfg(feature = "alloc")]
impl<T> fmt::Debug for HeapCircularBuffer<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}
