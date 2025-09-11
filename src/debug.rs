// Copyright © 2023-2025 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

use crate::CircularBuffer;
use core::fmt;
use core::iter;

#[derive(Default, Copy, Clone)]
struct Placeholder;

impl fmt::Debug for Placeholder { 
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("_")
    }
}

impl<T, const N: usize> fmt::Debug for CircularBuffer<T, N>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut list = f.debug_list();
        list.entries(self);
        list.entries(iter::repeat(Placeholder).take(self.capacity() - self.len()));
        list.finish()
    }
}
