// Copyright © 2023-2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

#![allow(clippy::extra_unused_lifetimes)]

/// Tests to verify that certain types offered by the crate are [covariant].
///
/// [covariant]: https://doc.rust-lang.org/nomicon/subtyping.html
use circular_buffer::CircularBuffer;
use circular_buffer::Drain;
use circular_buffer::Iter;

/// Verify that `CircularBuffer<T, N>` is covariant over `T`
#[test]
fn circular_buffer<'a>() {
    let buf = CircularBuffer::<&'static str, 1>::new();
    let _: CircularBuffer<&'a str, 1> = buf;
}

/// Verify that `Iter<'_, T>` is covariant over `T`
#[test]
fn iter<'a>() {
    let buf = CircularBuffer::<&'static str, 1>::new();
    let iter: Iter<'_, &'static str> = buf.iter();
    let _: Iter<'_, &'a str> = iter;
}

// `IterMut<'a, T>` is invariant over `T` because it holds a mutable reference to the elements of
// the buffer.
//
// TODO Add a test to verify the invariance of `IterMut`
//
//#[test]
//fn iter_mut<'a>() {
//    let mut buf = CircularBuffer::<&'static str, 1>::new();
//    let iter: IterMut<'_, &'static str> = buf.iter_mut();
//    let _: IterMut<'_, &'a str> = iter;
//}

/// Verify that `Drain<'_, T>` is covariant over `T`
#[test]
fn drain<'a>() {
    let mut buf = CircularBuffer::<&'static str, 1>::new();
    let drain: Drain<'_, &'static str> = buf.drain(..);
    let _: Drain<'_, &'a str> = drain;
}
