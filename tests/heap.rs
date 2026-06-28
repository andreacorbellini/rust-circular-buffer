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

#[test]
fn with_capacity() {
    for n in 0..1000 {
        let buf = HeapCircularBuffer::<u32>::with_capacity(n);
        assert_eq!(buf.capacity(), n);
        assert_buf_eq!(buf, [] as [u32; 0]);
    }

    assert!(
        std::panic::catch_unwind(|| HeapCircularBuffer::<u32>::with_capacity(isize::MAX as usize))
            .is_err()
    );
    assert!(
        std::panic::catch_unwind(|| HeapCircularBuffer::<u32>::with_capacity(usize::MAX)).is_err()
    );
}

#[test]
fn with_capacity_zst() {
    for n in [0, 1000, 1_000_000, isize::MAX as usize, usize::MAX] {
        let buf = HeapCircularBuffer::<()>::with_capacity(n);
        assert_eq!(buf.capacity(), n);
        assert_buf_eq!(buf, [] as [(); 0]);
    }
}

#[test]
fn resize() {
    let mut buf = HeapCircularBuffer::<u32>::with_capacity(0);
    assert_buf_eq!(buf, [] as [u32; 0]);
    assert_eq!(buf.capacity(), 0);

    // Grow an empty buffer.
    buf.resize(4);

    assert_buf_eq!(buf, [] as [u32; 0]);
    assert_eq!(buf.capacity(), 4);
    assert!(is_contiguous(&buf));

    buf.extend([1, 2, 3, 4]);
    assert_buf_eq!(buf, [1, 2, 3, 4]);
    assert_eq!(buf.capacity(), 4);
    assert!(is_contiguous(&buf));

    // Grow a full, contiguous buffer.
    buf.resize(8);

    assert_buf_eq!(buf, [1, 2, 3, 4]);
    assert_eq!(buf.capacity(), 8);
    assert!(is_contiguous(&buf));

    buf.pop_front();
    buf.pop_front();
    assert_buf_eq!(buf, [3, 4]);
    assert_eq!(buf.capacity(), 8);
    assert!(is_contiguous(&buf));

    // Shrink a partial, contiguous buffer, with elements that are not at the start of the array.
    buf.resize(2);

    assert_buf_eq!(buf, [3, 4]);
    assert_eq!(buf.capacity(), 2);
    assert!(is_contiguous(&buf));

    buf.push_back(5);
    assert_buf_eq!(buf, [4, 5]);
    assert_eq!(buf.capacity(), 2);
    assert!(!is_contiguous(&buf));

    // Grow a full, non contiguous buffer.
    buf.resize(4);

    assert_buf_eq!(buf, [4, 5]);
    assert_eq!(buf.capacity(), 4);
    assert!(is_contiguous(&buf));

    buf.extend([6, 7, 8, 9]);
    buf.pop_front();
    assert_buf_eq!(buf, [7, 8, 9]);
    assert_eq!(buf.capacity(), 4);
    assert!(!is_contiguous(&buf));

    // Grow a partial, non contiguous buffer.
    buf.resize(8);

    assert_buf_eq!(buf, [7, 8, 9]);
    assert_eq!(buf.capacity(), 8);
    assert!(is_contiguous(&buf));
}

#[test]
fn resize_too_small_panics() {
    let capacity = 4;

    for n in 0..capacity {
        let mut buf = HeapCircularBuffer::<u32>::with_capacity(capacity);
        assert_eq!(buf.capacity(), capacity);
        buf.extend([1, 2, 3, 4]);

        assert!(std::panic::catch_unwind(move || buf.resize(n)).is_err());
    }
}

#[test]
fn resize_too_large_panics() {
    let mut buf = HeapCircularBuffer::<u32>::with_capacity(0);
    assert_eq!(buf.capacity(), 0);

    assert!(std::panic::catch_unwind(move || buf.resize(isize::MAX as usize)).is_err());
}

#[test]
fn resize_zst() {
    for n in [0, 1000, 1_000_000, isize::MAX as usize, usize::MAX] {
        let mut buf = HeapCircularBuffer::<()>::with_capacity(0);
        assert_eq!(buf.capacity(), 0);
        assert_buf_eq!(buf, [] as [(); 0]);

        buf.resize(n);
        assert_eq!(buf.capacity(), n);
        assert_buf_eq!(buf, [] as [(); 0]);
    }
}
