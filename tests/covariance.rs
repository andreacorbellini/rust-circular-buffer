#![allow(clippy::extra_unused_lifetimes)]

/// Tests to verify that certain types offered by the crate are [covariant].
///
/// [covariant]: https://doc.rust-lang.org/nomicon/subtyping.html

use circular_buffer::CircularBuffer;
use circular_buffer::Iter;
use circular_buffer::Drain;
use circular_buffer::heap::{HeapCircularBuffer, HeapDrain};

/// Verify that `CircularBuffer<N, T>` is covariant over `T`
#[test]
fn circular_buffer<'a>() {
    let buf = CircularBuffer::<1, &'static str>::new();
    let _: CircularBuffer::<1, &'a str> = buf;
}

/// Verify that `HeapCircularBuffer<T>` is covariant over `T`
#[test]
fn heap_circular_buffer<'a>() {
    let buf = HeapCircularBuffer::<&'static str>::with_capacity(1);
    let _: HeapCircularBuffer::<&'a str> = buf;
}

/// Verify that `Iter<'_, T>` is covariant over `T`
#[test]
fn iter<'a>() {
    let buf = CircularBuffer::<1, &'static str>::new();
    let iter: Iter<'_, &'static str> = buf.iter();
    let _: Iter<'_, &'a str> = iter;
}

/// Verify that `Iter<'_, T>` is covariant over `T`
#[test]
fn heap_iter<'a>() {
    let buf = HeapCircularBuffer::<&'static str>::with_capacity(1);
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
//    let mut buf = CircularBuffer::<1, &'static str>::new();
//    let iter: IterMut<'_, &'static str> = buf.iter_mut();
//    let _: IterMut<'_, &'a str> = iter;
//}

/// Verify that `Drain<'_, N, T>` is covariant over `T`
#[test]
fn drain<'a>() {
    let mut buf = CircularBuffer::<1, &'static str>::new();
    let drain: Drain<'_, 1, &'static str> = buf.drain(..);
    let _: Drain<'_, 1, &'a str> = drain;
}

/// Verify that `Drain<'_, N, T>` is covariant over `T`
#[test]
fn heap_drain<'a>() {
    let mut buf = HeapCircularBuffer::<&'static str>::with_capacity(1);
    let drain: HeapDrain<'_, &'static str> = buf.drain(..);
    let _: HeapDrain<'_, &'a str> = drain;
}
