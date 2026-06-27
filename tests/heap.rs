// Copyright © 2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

#![cfg(feature = "alloc")]

mod common;

use circular_buffer::HeapCircularBuffer;

#[must_use]
fn heap_circular_buffer<T, const N: usize>() -> HeapCircularBuffer<T> {
    HeapCircularBuffer::<T>::with_capacity(N)
}

common::define_tests!(heap_circular_buffer);
