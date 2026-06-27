// Copyright © 2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

mod common;

use circular_buffer::FixedCircularBuffer;

#[must_use]
fn fixed_circular_buffer<T, const N: usize>() -> FixedCircularBuffer<T, N> {
    FixedCircularBuffer::<T, N>::new()
}

#[must_use]
fn fixed_circular_buffer_from<T, const N: usize, I>(input: I) -> FixedCircularBuffer<T, N>
where
    FixedCircularBuffer<T, N>: From<I>,
{
    FixedCircularBuffer::<T, N>::from(input)
}

#[must_use]
fn fixed_circular_buffer_from_iter<T, const N: usize, I>(input: I) -> FixedCircularBuffer<T, N>
where
    I: IntoIterator<Item = T>,
{
    FixedCircularBuffer::<T, N>::from_iter(input)
}

common::define_tests!(
    fixed_circular_buffer,
    fixed_circular_buffer_from,
    fixed_circular_buffer_from_iter,
);
