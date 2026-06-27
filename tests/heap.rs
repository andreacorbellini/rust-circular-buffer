// Copyright © 2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

#![cfg(feature = "alloc")]

mod common;

use circular_buffer::HeapCircularBuffer;

#[must_use]
fn heap_circular_buffer<T, const N: usize>() -> HeapCircularBuffer<T> {
    HeapCircularBuffer::<T>::with_capacity(N)
}

#[must_use]
fn heap_circular_buffer_from<T, const N: usize, I>(input: I) -> HeapCircularBuffer<T>
where
    I: IntoIterator<Item = T>,
{
    let mut buf = heap_circular_buffer::<T, N>();
    buf.extend(input);
    buf
}

#[must_use]
fn heap_circular_buffer_from_iter<T, const N: usize, I>(input: I) -> HeapCircularBuffer<T>
where
    I: IntoIterator<Item = T>,
{
    let mut buf = heap_circular_buffer::<T, N>();
    buf.extend(input);
    buf
}

#[must_use]
#[allow(dead_code)]
fn heap_circular_buffer_boxed<T, const N: usize>() -> HeapCircularBuffer<T> {
    HeapCircularBuffer::<T>::with_capacity(N)
}

common::define_tests!(
    heap_circular_buffer,
    heap_circular_buffer_from,
    heap_circular_buffer_from_iter,
    heap_circular_buffer_boxed,
);
