// Copyright © 2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

mod common;

use circular_buffer::FixedCircularBuffer;

#[must_use]
fn fixed_circular_buffer<T, const N: usize>() -> FixedCircularBuffer<T, N> {
    FixedCircularBuffer::<T, N>::new()
}

common::define_tests!(fixed_circular_buffer);
