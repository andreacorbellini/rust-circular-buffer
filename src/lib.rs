// Copyright © 2023-2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

//! This crate implements a [circular buffer], also known as cyclic buffer, circular queue or ring.
//!
//! A **circular buffer** is a sequence of elements with a maximum capacity: elements can be added
//! to the buffer, and once the maximum capacity is reached, the elements at the start of the buffer
//! are discarded and overwritten.
//!
//! The main structs are [`CircularBuffer`], [`FixedCircularBuffer`], and [`HeapCircularBuffer`].
//! You can think of them as semantically equivalent to [`slice`], [`array`], and [`Vec`]
//! respectively:
//!
//! * A [`CircularBuffer`] provides a _reference_ to either a `FixedCircularBuffer` or a
//!   `HeapCircularBuffer`. It can be used to get/add/remove elements.
//! * A [`FixedCircularBuffer`] is an _owned_ fixed-capacity buffer that can live on the stack or
//!   can be constructed in `const` contexts.
//! * A [`HeapCircularBuffer`] is an _owned_ buffer that is heap-allocated and can its capacity can
//!   be adjusted at runtime.
//!
//! `CircularBuffer` and `FixedCircularBuffer` can be used in a [`no_std` environment].
//! `HeapCircularBuffer` requires either the [`std` library] or the [`alloc` crate].
//!
//! # Examples
//!
//! ```
//! use circular_buffer::FixedCircularBuffer;
//!
//! // Initialize a new, empty circular buffer with a capacity of 5 elements
//! let mut buf = FixedCircularBuffer::<u32, 5>::new();
//!
//! // Add a few elements
//! buf.push_back(1);
//! buf.push_back(2);
//! buf.push_back(3);
//! assert_eq!(buf, [1, 2, 3]);
//!
//! // Add more elements to fill the buffer capacity completely
//! buf.push_back(4);
//! buf.push_back(5);
//! assert_eq!(buf, [1, 2, 3, 4, 5]);
//!
//! // Adding more elements than the buffer can contain causes the front elements to be
//! // automatically dropped
//! buf.push_back(6);
//! assert_eq!(buf, [2, 3, 4, 5, 6]); // `1` got dropped to make room for `6`
//! ```
//!
//! # Interface
//!
//! [`CircularBuffer`] provides methods akin the ones for the standard
//! [`VecDeque`](std::collections::VecDeque) and [`LinkedList`](std::collections::LinkedList). The
//! list below includes the most common methods, but see the [`CircularBuffer` struct
//! documentation](CircularBuffer) to see more.
//!
//! ## Adding/removing elements
//!
//! * [`push_back()`](CircularBuffer::push_back), [`push_front()`](CircularBuffer::push_front)
//! * [`pop_back()`](CircularBuffer::pop_back), [`pop_front()`](CircularBuffer::pop_front)
//! * [`swap_remove_back()`](CircularBuffer::swap_remove_back),
//!   [`swap_remove_front()`](CircularBuffer::swap_remove_front)
//!
//! ## Getting/mutating elements
//!
//! * [`get()`](CircularBuffer::get), [`get_mut()`](CircularBuffer::get_mut)
//! * [`front()`](CircularBuffer::front), [`front_mut()`](CircularBuffer::front_mut)
//! * [`back()`](CircularBuffer::back), [`back_mut()`](CircularBuffer::back_mut)
//! * [`nth_front()`](CircularBuffer::nth_front), [`nth_front_mut()`](CircularBuffer::nth_front_mut)
//! * [`nth_back()`](CircularBuffer::nth_back), [`nth_back_mut()`](CircularBuffer::nth_back_mut)
//!
//! ## Adding multiple elements at once
//!
//! * [`extend()`](CircularBuffer::extend),
//!   [`extend_from_slice()`](CircularBuffer::extend_from_slice)
//! * [`fill()`](CircularBuffer::fill), [`fill_with()`](CircularBuffer::fill_with)
//! * [`fill_spare()`](CircularBuffer::fill), [`fill_spare_with()`](CircularBuffer::fill_with)
//!
//! ## Iterators
//!
//! * [`into_iter()`](FixedCircularBuffer::into_iter)
//! * [`iter()`](CircularBuffer::iter), [`iter_mut()`](CircularBuffer::iter_mut)
//! * [`range()`](CircularBuffer::range), [`range_mut()`](CircularBuffer::range_mut)
//! * [`drain()`](CircularBuffer::drain)
//!
//! ## Writing/reading bytes
//!
//! For the special case of a `CircularBuffer` containing `u8` elements, bytes can be written and
//! read using the standard [`Write`](std::io::Write) and [`Read`](std::io::Read) traits. Writing
//! past the buffer capacity will overwrite the bytes at the start of the buffer, and reading
//! elements will consume elements from the buffer.
//!
//! ```
//! # #[allow(unused_must_use)]
//! # #[cfg(feature = "std")]
//! # {
//! use circular_buffer::FixedCircularBuffer;
//! use std::io::Read;
//! use std::io::Write;
//!
//! let mut buf = FixedCircularBuffer::<u8, 5>::new();
//! assert_eq!(buf, b"");
//!
//! write!(buf, "hello");
//! assert_eq!(buf, b"hello");
//!
//! write!(buf, "this string will overflow the buffer and wrap around");
//! assert_eq!(buf, b"round");
//!
//! let mut s = String::new();
//! buf.read_to_string(&mut s)
//!     .expect("failed to read from buffer");
//! assert_eq!(s, "round");
//! assert_eq!(buf, b"");
//! # }
//! ```
//!
//! For `no_std` environments, this crate provides optional integration with the [`embedded_io`] and
//! [`embedded_io_async`] crates.
//!
//! # Time complexity
//!
//! Most of the methods implemented by [`CircularBuffer`] run in constant time. Some of the methods
//! may run in linear time if the type of the elements implements [`Drop`], as each element needs
//! to be deallocated one-by-one.
//!
//! | Method                                                                                                                                                                                     | Complexity                                                           |
//! |--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|----------------------------------------------------------------------|
//! | [`push_back()`](CircularBuffer::push_back), [`push_front()`](CircularBuffer::push_front)                                                                                                   | *O*(1)                                                               |
//! | [`pop_back()`](CircularBuffer::pop_back), [`pop_front()`](CircularBuffer::pop_front)                                                                                                       | *O*(1)                                                               |
//! | [`remove(i)`](CircularBuffer::remove)                                                                                                                                                      | *O*(*n* − *i*)                                                       |
//! | [`truncate_back(i)`](CircularBuffer::truncate_back), [`truncate_front(i)`](CircularBuffer::truncate_front)                                                                                 | *O*(*n* − *i*) for types that implement [`Drop`], *O*(1) otherwise   |
//! | [`clear()`](CircularBuffer::clear)                                                                                                                                                         | *O*(*n*) for types that implement [`Drop`], *O*(1) otherwise         |
//! | [`drain(i..j)`](CircularBuffer::drain)                                                                                                                                                     | *O*(*n* − *j*)                                                       |
//! | [`fill()`](CircularBuffer::fill), [`fill_with()`](CircularBuffer::fill_with)                                                                                                               | *O*(*c* + *n*) for types that implement [`Drop`], *O*(*c*) otherwise |
//! | [`fill_spare()`](CircularBuffer::fill_spare), [`fill_spare_with()`](CircularBuffer::fill_spare_with)                                                                                       | *O*(*c* − *n*)                                                       |
//! | [`get()`](CircularBuffer::get), [`front()`](CircularBuffer::front), [`back()`](CircularBuffer::back), [`nth_front()`](CircularBuffer::nth_front), [`nth_back()`](CircularBuffer::nth_back) | *O*(1)                                                               |
//! | [`swap()`](CircularBuffer::swap), [`swap_remove_front()`](CircularBuffer::swap_remove_front), [`swap_remove_back()`](CircularBuffer::swap_remove_back)                                     | *O*(1)                                                               |
//! | [`as_slices()`](CircularBuffer::as_slices), [`as_mut_slices()`](CircularBuffer::as_mut_slices)                                                                                             | *O*(1)                                                               |
//! | [`len()`](CircularBuffer::len), [`capacity()`](CircularBuffer::capacity)                                                                                                                   | *O*(1)                                                               |
//!
//! Notation: *n* is the [length](CircularBuffer::len) of the buffer, *c* is the
//! [capacity](CircularBuffer::capacity) of the buffer, *i* and *j* are variables.
//!
//! # Stack vs heap
//!
//! The [`FixedCircularBuffer`] struct is compact and has a fixed size specified at compile time, so
//! it may live on the stack. This can provide optimal performance for small buffers as memory
//! allocation can be avoided.
//!
//! For large buffers, or for buffers that need to be passed around often, it can be useful to
//! allocate the buffer on the heap. Use a [`Box`](std::boxed) for that:
//!
//! ```
//! # #[cfg(feature = "std")]
//! # {
//! use circular_buffer::FixedCircularBuffer;
//!
//! let mut buf = FixedCircularBuffer::<u32, 4096>::boxed();
//! assert_eq!(buf.len(), 0);
//!
//! for i in 0..1024 {
//!     buf.push_back(i);
//! }
//! assert_eq!(buf.len(), 1024);
//!
//! buf.truncate_back(128);
//! assert_eq!(buf.len(), 128);
//! # }
//! ```
//!
//! For buffers whose capacity is not known at compile time, [`HeapCircularBuffer`] is the solution:
//!
//! ```
//! # #[cfg(feature = "alloc")]
//! # {
//! use circular_buffer::HeapCircularBuffer;
//!
//! let mut buf = HeapCircularBuffer::<char>::with_capacity(3);
//! buf.push_back('a');
//! buf.push_back('b');
//! buf.push_back('c');
//! buf.push_back('d');
//! assert_eq!(buf, ['b', 'c', 'd']);
//!
//! buf.resize(5);
//! buf.push_back('e');
//! buf.push_back('f');
//! buf.push_back('g');
//! assert_eq!(buf, ['c', 'd', 'e', 'f', 'g']);
//! # }
//! ```
//!
//! # `no_std`
//!
//! This crate can be used in a [`no_std` environment], although the I/O features and
//! heap-allocation features won't be available by default in `no_std` mode. By default, this crate
//! uses `std`; to use this crate in `no_std` mode, disable the default features for this crate in
//! your `Cargo.toml`:
//!
//! ```text
//! [dependencies]
//! circular-buffer = { version = "0.1", default-features = false }
//! ```
//!
//! When using `no_std` mode, this crate supports heap-allocation features through the [`alloc`
//! crate](alloc). To enable the use of the `alloc` crate, enable the `alloc` feature:
//!
//! ```text
//! [dependencies]
//! circular-buffer = { version = "0.1", default-features = false, features = ["alloc"] }
//! ```
//!
//! # Cargo feature flags
//!
//! * `std`: enables support for the [`std` library] (enabled by default).
//! * `alloc`: enables support for the [`alloc` crate] (enabled by default).
//! * `embedded-io`: enables implementation for the [`embedded_io`]
//! * `embedded-io-async`: enables implementation for the [`embedded_io_async`] traits.
//!
//! [circular buffer]: https://en.wikipedia.org/wiki/Circular_buffer
//! [`std` library]: https://doc.rust-lang.org/std/
//! [`alloc` crate]: https://doc.rust-lang.org/alloc/
//! [`no_std` environment]: https://docs.rust-embedded.org/book/intro/no-std.html
//! [`embedded_io`]: https://docs.rs/embedded-io/
//! [`embedded_io_async`]: https://docs.rs/embedded-io-async/

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(clippy::dbg_macro)]
#![warn(clippy::print_stderr)]
#![warn(clippy::print_stdout)]
#![warn(clippy::missing_safety_doc)]
#![warn(clippy::unnecessary_safety_doc)]
#![warn(clippy::unnecessary_safety_comment)]
#![warn(clippy::undocumented_unsafe_blocks)]
#![warn(missing_debug_implementations)]
#![warn(missing_docs)]
#![warn(unreachable_pub)]
#![warn(unused_qualifications)]
#![doc(test(attr(deny(warnings))))]

#[cfg(feature = "alloc")]
extern crate alloc;

mod cmp;
mod debug;
mod drain;
mod embedded_io;
mod hash;
mod io;
mod iter;
mod tests;

pub mod fixed;

#[cfg(feature = "alloc")]
pub mod heap;

use core::mem;
use core::mem::MaybeUninit;
use core::ops::Index;
use core::ops::IndexMut;
use core::ops::Range;
use core::ops::RangeBounds;
use core::ptr;

#[cfg(all(not(feature = "std"), feature = "alloc"))]
use alloc::vec::Vec;

pub use crate::drain::Drain;
pub use crate::fixed::FixedCircularBuffer;
pub use crate::iter::Iter;
pub use crate::iter::IterMut;

#[cfg(feature = "alloc")]
pub use crate::heap::HeapCircularBuffer;

/// Returns `(x + y) % m` without risk of overflows if `x + y` cannot fit in `usize`.
///
/// `x` and `y` are expected to be less than, or equal to `m`.
#[inline]
const fn add_mod(x: usize, y: usize, m: usize) -> usize {
    debug_assert!(m > 0);
    debug_assert!(x <= m);
    debug_assert!(y <= m);
    let (z, overflow) = x.overflowing_add(y);
    (z + (overflow as usize) * (usize::MAX % m + 1)) % m
}

/// Returns `(x - y) % m` without risk of underflows if `x - y` is negative.
///
/// `x` and `y` are expected to be less than, or equal to `m`.
#[inline]
const fn sub_mod(x: usize, y: usize, m: usize) -> usize {
    debug_assert!(m > 0);
    debug_assert!(x <= m);
    debug_assert!(y <= m);
    add_mod(x, m - y, m)
}

/// Internal structure shared by `CircularBuffer`, `FixedCircularBuffer`, and `HeapCircularBuffer`.
///
/// The main purpose of this structure is to allow safe coercion to `CircularBuffer`. It may go
/// away once `core::ptr::from_raw_parts()` is stabilized.
struct Inner<T: ?Sized> {
    size: usize,
    start: usize,
    items: T,
}

/// A reference to a circular buffer.
///
/// This type can be thought as the equivalent of a Rust [slice], in the sense that it _points_ to
/// the data held by a circular buffer (either a [`FixedCircularBuffer`] or a
/// [`HeapCircularBuffer`]) but does not actually own the data. The relationship between the types
/// `CircularBuffer<T>`, `FixedCircularBuffer<T, N>`, and `HeapCircularBuffer<T>` is akin to the
/// relationship between types `[T]` (slice), `[T; N]` (array), `Vec<T>`. In particular:
///
/// - Both [`FixedCircularBuffer`] and [`HeapCircularBuffer`] can be [dereferenced] to a
///   `CircularBuffer`.
/// - Most of the circular buffer logic (such as adding/removing/getting elements) is implemented in
///   `CircularBuffer`.
///
/// [dereferenced]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#the-dereference-operator
///
/// You generally don't need to interact with `CircularBuffer` directly, although you may want to
/// use it as an input type to functions as shown in the following example.
///
/// # Examples
///
/// ```
/// use circular_buffer::{CircularBuffer, FixedCircularBuffer};
///
/// fn push_some_elements(buf: &mut CircularBuffer<u32>) {
///     buf.push_back(1);
///     buf.push_back(2);
///     buf.push_back(3);
/// }
///
/// let mut fixed_buf = FixedCircularBuffer::<u32, 5>::new();
/// push_some_elements(&mut fixed_buf);
/// assert_eq!(fixed_buf, [1, 2, 3]);
/// ```
#[repr(transparent)]
pub struct CircularBuffer<T> {
    inner: Inner<[MaybeUninit<T>]>,
}

impl<T> CircularBuffer<T> {
    /// Returns the number of elements in the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<u32, 16>::new();
    /// assert_eq!(buf.len(), 0);
    ///
    /// buf.push_back(1);
    /// buf.push_back(2);
    /// buf.push_back(3);
    /// assert_eq!(buf.len(), 3);
    /// ```
    #[inline]
    pub const fn len(&self) -> usize {
        self.inner.size
    }

    /// Returns the capacity of the buffer.
    ///
    /// This is the maximum number of elements that the buffer can hold.
    ///
    /// This method always returns the generic const parameter `N`.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    /// let buf = FixedCircularBuffer::<u32, 16>::new();
    /// assert_eq!(buf.capacity(), 16);
    /// ```
    #[inline]
    pub const fn capacity(&self) -> usize {
        self.inner.items.len()
    }

    /// Returns `true` if the buffer contains 0 elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<u32, 16>::new();
    /// assert!(buf.is_empty());
    ///
    /// buf.push_back(1);
    /// assert!(!buf.is_empty());
    /// ```
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.inner.size == 0
    }

    /// Returns `true` if the number of elements in the buffer matches the buffer capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<u32, 5>::new();
    /// assert!(!buf.is_full());
    ///
    /// buf.push_back(1);
    /// assert!(!buf.is_full());
    ///
    /// buf.push_back(2);
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// buf.push_back(5);
    /// assert!(buf.is_full());
    /// ```
    #[inline]
    pub const fn is_full(&self) -> bool {
        self.inner.size == self.capacity()
    }

    /// Returns an iterator over the elements of the buffer.
    ///
    /// The iterator advances from front to back. Use [`.rev()`](Iter::rev) to advance from
    /// back to front.
    ///
    /// # Examples
    ///
    /// Iterate from front to back:
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let buf = FixedCircularBuffer::<char, 5>::from_iter("abc".chars());
    /// let mut it = buf.iter();
    ///
    /// assert_eq!(it.next(), Some(&'a'));
    /// assert_eq!(it.next(), Some(&'b'));
    /// assert_eq!(it.next(), Some(&'c'));
    /// assert_eq!(it.next(), None);
    /// ```
    ///
    /// Iterate from back to front:
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let buf = FixedCircularBuffer::<char, 5>::from_iter("abc".chars());
    /// let mut it = buf.iter().rev();
    ///
    /// assert_eq!(it.next(), Some(&'c'));
    /// assert_eq!(it.next(), Some(&'b'));
    /// assert_eq!(it.next(), Some(&'a'));
    /// assert_eq!(it.next(), None);
    /// ```
    #[inline]
    #[must_use]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter::new(self)
    }

    /// Returns an iterator over the elements of the buffer that allows modifying each value.
    ///
    /// The iterator advances from front to back. Use [`.rev()`](Iter::rev) to advance from back to
    /// front.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<u32, 5>::from([1, 2, 3]);
    /// for elem in buf.iter_mut() {
    ///     *elem += 5;
    /// }
    /// assert_eq!(buf, [6, 7, 8]);
    /// ```
    #[inline]
    #[must_use]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut::new(self)
    }

    /// Returns an iterator over the specified range of elements of the buffer.
    ///
    /// The iterator advances from front to back. Use [`.rev()`](Iter::rev) to advance from back to
    /// front.
    ///
    /// # Panics
    ///
    /// If the start of the range is greater than the end, or if the end is greater than the length
    /// of the buffer.
    ///
    /// # Examples
    ///
    /// Iterate from front to back:
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let buf = FixedCircularBuffer::<char, 16>::from_iter("abcdefghi".chars());
    /// let mut it = buf.range(3..6);
    ///
    /// assert_eq!(it.next(), Some(&'d'));
    /// assert_eq!(it.next(), Some(&'e'));
    /// assert_eq!(it.next(), Some(&'f'));
    /// assert_eq!(it.next(), None);
    /// ```
    ///
    /// Iterate from back to front:
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let buf = FixedCircularBuffer::<char, 16>::from_iter("abcdefghi".chars());
    /// let mut it = buf.range(3..6).rev();
    ///
    /// assert_eq!(it.next(), Some(&'f'));
    /// assert_eq!(it.next(), Some(&'e'));
    /// assert_eq!(it.next(), Some(&'d'));
    /// assert_eq!(it.next(), None);
    /// ```
    #[inline]
    #[must_use]
    pub fn range<R>(&self, range: R) -> Iter<'_, T>
    where
        R: RangeBounds<usize>,
    {
        Iter::over_range(self, range)
    }

    /// Returns an iterator over the specified range of elements of the buffer that allows
    /// modifying each value.
    ///
    /// The iterator advances from front to back. Use [`.rev()`](Iter::rev) to advance from back to
    /// front.
    ///
    /// # Panics
    ///
    /// If the start of the range is greater than the end, or if the end is greater than the length
    /// of the buffer.
    ///
    /// # Examples
    ///
    /// Iterate from front to back:
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<i32, 16>::from_iter([1, 2, 3, 4, 5, 6]);
    /// for elem in buf.range_mut(..3) {
    ///     *elem *= -1;
    /// }
    /// assert_eq!(buf, [-1, -2, -3, 4, 5, 6]);
    /// ```
    #[inline]
    #[must_use]
    pub fn range_mut<R>(&mut self, range: R) -> IterMut<'_, T>
    where
        R: RangeBounds<usize>,
    {
        IterMut::over_range(self, range)
    }

    /// Removes the specified range from the buffer in bulk, returning the removed elements as an
    /// iterator. If the iterator is dropped before being fully consumed, it drops the remaining
    /// removed elements.
    ///
    /// # Panics
    ///
    /// If the start of the range is greater than the end, or if the end is greater than the length
    /// of the buffer.
    ///
    /// # Leaking
    ///
    /// If the returned iterator goes out of scope without being dropped (for example, due to
    /// calling [`mem::forget()`] on it), the buffer may have lost and leaked arbitrary elements,
    /// including elements outside of the range.
    ///
    /// The current implementation leaks all the elements of the buffer if the iterator is leaked,
    /// but this behavior may change in the future.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 6>::from_iter("abcdef".chars());
    /// let drained = buf.drain(3..).collect::<Vec<char>>();
    ///
    /// assert_eq!(drained, ['d', 'e', 'f']);
    /// assert_eq!(buf, ['a', 'b', 'c']);
    /// ```
    ///
    /// Not consuming the draining iterator still removes the range of elements:
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 6>::from_iter("abcdef".chars());
    /// buf.drain(3..);
    ///
    /// assert_eq!(buf, ['a', 'b', 'c']);
    /// ```
    #[inline]
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, T>
    where
        R: RangeBounds<usize>,
    {
        Drain::over_range(self, range)
    }

    /// Rearranges the internal memory of the buffer so that all elements are in a contiguous
    /// slice, which is then returned.
    ///
    /// This method does not allocate and does not change the order of the inserted elements.
    /// Because it returns a mutable slice, any [slice methods](slice) may be called on the
    /// elements of the buffer, such as sorting methods.
    ///
    /// Once the internal storage is contiguous, the [`as_slices()`](Self::as_slices) and
    /// [`as_mut_slices()`](Self::as_mut_slices) methods will return the entire contents of the
    /// deque in a single slice. Adding new elements to the buffer may make the buffer disjoint (not
    /// contiguous).
    ///
    /// # Complexity
    ///
    /// If the buffer is disjoint (not contiguous), this method takes *O*(*N*) time, where *N* is
    /// the capacity of the buffer.
    ///
    /// If the buffer is already contiguous, this method takes *O*(1) time.
    ///
    /// This means that this method may be called multiple times on the same buffer without a
    /// performance penalty (provided that no new elements are added to the buffer in between
    /// calls).
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// // Create a new buffer, adding more elements than its capacity
    /// let mut buf = FixedCircularBuffer::<u32, 4>::from_iter([1, 4, 3, 0, 2, 5]);
    /// assert_eq!(buf, [3, 0, 2, 5]);
    ///
    /// // The buffer is disjoint: as_slices() returns two non-empty slices
    /// assert_eq!(buf.as_slices(), (&[3, 0][..], &[2, 5][..]));
    ///
    /// // Make the buffer contiguous
    /// assert_eq!(buf.make_contiguous(), &mut [3, 0, 2, 5]);
    /// // as_slices() now returns a single non-empty slice
    /// assert_eq!(buf.as_slices(), (&[3, 0, 2, 5][..], &[][..]));
    /// // The order of the elements in the buffer did not get modified
    /// assert_eq!(buf, [3, 0, 2, 5]);
    ///
    /// // Make the buffer contiguous and sort its elements
    /// buf.make_contiguous().sort();
    /// assert_eq!(buf, [0, 2, 3, 5]);
    /// ```
    pub fn make_contiguous(&mut self) -> &mut [T] {
        if self.capacity() == 0 || self.inner.size == 0 {
            return &mut [];
        }

        debug_assert!(self.inner.start < self.capacity(), "start out-of-bounds");
        debug_assert!(self.inner.size <= self.capacity(), "size out-of-bounds");

        let start = self.inner.start;
        let end = add_mod(self.inner.start, self.inner.size, self.capacity());

        let slice = if start < end {
            // Already contiguous; nothing to do
            &mut self.inner.items[start..end]
        } else {
            // Not contiguous; need to rotate
            self.inner.start = 0;
            self.inner.items.rotate_left(start);
            &mut self.inner.items[..self.inner.size]
        };

        // SAFETY: The elements in the slice are guaranteed to be initialized
        unsafe { slice.assume_init_mut() }
    }

    /// Returns a pair of slices which contain the elements of this buffer.
    ///
    /// The second slice may be empty if the internal buffer is contiguous.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 4>::new();
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// buf.push_back('c');
    /// buf.push_back('d');
    ///
    /// // Buffer is contiguous; second slice is empty
    /// assert_eq!(buf.as_slices(), (&['a', 'b', 'c', 'd'][..], &[][..]));
    ///
    /// buf.push_back('e');
    /// buf.push_back('f');
    ///
    /// // Buffer is disjoint; both slices are non-empty
    /// assert_eq!(buf.as_slices(), (&['c', 'd'][..], &['e', 'f'][..]));
    /// ```
    #[inline]
    pub fn as_slices(&self) -> (&[T], &[T]) {
        if self.capacity() == 0 || self.inner.size == 0 {
            return (&[], &[]);
        }

        debug_assert!(self.inner.start < self.capacity(), "start out-of-bounds");
        debug_assert!(self.inner.size <= self.capacity(), "size out-of-bounds");

        let start = self.inner.start;
        let end = add_mod(self.inner.start, self.inner.size, self.capacity());

        let (front, back) = if start < end {
            (&self.inner.items[start..end], &[][..])
        } else {
            let (back, front) = self.inner.items.split_at(start);
            (front, &back[..end])
        };

        // SAFETY: The elements in these slices are guaranteed to be initialized
        unsafe { (front.assume_init_ref(), back.assume_init_ref()) }
    }

    /// Returns a pair of mutable slices which contain the elements of this buffer.
    ///
    /// These slices can be used to modify or replace the elements in the buffer.
    ///
    /// The second slice may be empty if the internal buffer is contiguous.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 4>::new();
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// buf.push_back('c');
    /// buf.push_back('d');
    /// buf.push_back('e');
    /// buf.push_back('f');
    ///
    /// assert_eq!(buf, ['c', 'd', 'e', 'f']);
    ///
    /// let (left, right) = buf.as_mut_slices();
    /// assert_eq!(left, &mut ['c', 'd'][..]);
    /// assert_eq!(right, &mut ['e', 'f'][..]);
    ///
    /// left[0] = 'z';
    ///
    /// assert_eq!(buf, ['z', 'd', 'e', 'f']);
    /// ```
    #[inline]
    pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
        if self.capacity() == 0 || self.inner.size == 0 {
            return (&mut [][..], &mut [][..]);
        }

        debug_assert!(self.inner.start < self.capacity(), "start out-of-bounds");
        debug_assert!(self.inner.size <= self.capacity(), "size out-of-bounds");

        let start = self.inner.start;
        let end = add_mod(self.inner.start, self.inner.size, self.capacity());

        let (front, back) = if start < end {
            (&mut self.inner.items[start..end], &mut [][..])
        } else {
            let (back, front) = self.inner.items.split_at_mut(start);
            (front, &mut back[..end])
        };

        // SAFETY: The elements in these slices are guaranteed to be initialized
        unsafe { (front.assume_init_mut(), back.assume_init_mut()) }
    }

    #[inline]
    const fn front_maybe_uninit_mut(&mut self) -> &mut MaybeUninit<T> {
        debug_assert!(self.inner.size > 0, "empty buffer");
        debug_assert!(self.inner.start < self.capacity(), "start out-of-bounds");
        &mut self.inner.items[self.inner.start]
    }

    #[inline]
    const fn front_maybe_uninit(&self) -> &MaybeUninit<T> {
        debug_assert!(self.inner.size > 0, "empty buffer");
        debug_assert!(self.inner.size <= self.capacity(), "size out-of-bounds");
        debug_assert!(self.inner.start < self.capacity(), "start out-of-bounds");
        &self.inner.items[self.inner.start]
    }

    #[inline]
    const fn back_maybe_uninit(&self) -> &MaybeUninit<T> {
        debug_assert!(self.inner.size > 0, "empty buffer");
        debug_assert!(self.inner.size <= self.capacity(), "size out-of-bounds");
        debug_assert!(self.inner.start < self.capacity(), "start out-of-bounds");
        let back = add_mod(self.inner.start, self.inner.size - 1, self.capacity());
        &self.inner.items[back]
    }

    #[inline]
    const fn back_maybe_uninit_mut(&mut self) -> &mut MaybeUninit<T> {
        debug_assert!(self.inner.size > 0, "empty buffer");
        debug_assert!(self.inner.size <= self.capacity(), "size out-of-bounds");
        debug_assert!(self.inner.start < self.capacity(), "start out-of-bounds");
        let back = add_mod(self.inner.start, self.inner.size - 1, self.capacity());
        &mut self.inner.items[back]
    }

    #[inline]
    const fn get_maybe_uninit(&self, index: usize) -> &MaybeUninit<T> {
        debug_assert!(self.inner.size > 0, "empty buffer");
        debug_assert!(index < self.capacity(), "index out-of-bounds");
        debug_assert!(self.inner.start < self.capacity(), "start out-of-bounds");
        let index = add_mod(self.inner.start, index, self.capacity());
        &self.inner.items[index]
    }

    #[inline]
    const fn get_maybe_uninit_mut(&mut self, index: usize) -> &mut MaybeUninit<T> {
        debug_assert!(self.inner.size > 0, "empty buffer");
        debug_assert!(index < self.capacity(), "index out-of-bounds");
        debug_assert!(self.inner.start < self.capacity(), "start out-of-bounds");
        let index = add_mod(self.inner.start, index, self.capacity());
        &mut self.inner.items[index]
    }

    #[inline]
    fn slices_uninit_mut(&mut self) -> (&mut [MaybeUninit<T>], &mut [MaybeUninit<T>]) {
        if self.capacity() == 0 {
            return (&mut [][..], &mut [][..]);
        }

        debug_assert!(self.inner.start < self.capacity(), "start out-of-bounds");
        debug_assert!(self.inner.size <= self.capacity(), "size out-of-bounds");

        let start = self.inner.start;
        let end = add_mod(start, self.inner.size, self.capacity());
        if end < start {
            (&mut self.inner.items[end..start], &mut [][..])
        } else {
            let (left, right) = self.inner.items.split_at_mut(end);
            let left = &mut left[..start];
            (right, left)
        }
    }

    #[inline]
    const fn inc_start(&mut self) {
        debug_assert!(self.inner.start < self.capacity(), "start out-of-bounds");
        self.inner.start = add_mod(self.inner.start, 1, self.capacity());
    }

    #[inline]
    const fn dec_start(&mut self) {
        debug_assert!(self.inner.start < self.capacity(), "start out-of-bounds");
        self.inner.start = sub_mod(self.inner.start, 1, self.capacity());
    }

    #[inline]
    const fn inc_size(&mut self) {
        debug_assert!(self.inner.size <= self.capacity(), "size out-of-bounds");
        debug_assert!(self.inner.size < self.capacity(), "size at capacity limit");
        self.inner.size += 1;
    }

    #[inline]
    const fn dec_size(&mut self) {
        debug_assert!(self.inner.size > 0, "size is 0");
        self.inner.size -= 1;
    }

    #[inline]
    unsafe fn drop_range(&mut self, range: Range<usize>) {
        if range.is_empty() {
            return;
        }

        debug_assert!(self.inner.start < self.capacity(), "start out-of-bounds");
        debug_assert!(self.inner.size <= self.capacity(), "size out-of-bounds");
        debug_assert!(
            range.start < self.inner.size,
            "start of range out-of-bounds"
        );
        debug_assert!(range.end <= self.inner.size, "end of range out-of-bounds");
        debug_assert!(range.start < range.end, "start of range is past its end");
        debug_assert!(
            range.start == 0 || range.end == self.inner.size,
            "range does not include boundary of the buffer"
        );

        // Drops all the items in the slice when dropped. This is needed to ensure that all
        // elements are dropped in case a panic occurs during the drop of a single element.
        struct Dropper<'a, T>(&'a mut [MaybeUninit<T>]);

        impl<T> Drop for Dropper<'_, T> {
            #[inline]
            fn drop(&mut self) {
                // SAFETY: the caller of `drop_range` is responsible to check that this slice was
                // initialized.
                unsafe {
                    ptr::drop_in_place(self.0.assume_init_mut());
                }
            }
        }

        let drop_from = add_mod(self.inner.start, range.start, self.capacity());
        let drop_to = add_mod(self.inner.start, range.end, self.capacity());

        let (right, left) = if drop_from < drop_to {
            (&mut self.inner.items[drop_from..drop_to], &mut [][..])
        } else {
            let (left, right) = self.inner.items.split_at_mut(drop_from);
            let left = &mut left[..drop_to];
            (right, left)
        };

        let _left = Dropper(left);
        let _right = Dropper(right);
    }

    /// Returns a reference to the back element, or `None` if the buffer is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 4>::new();
    /// assert_eq!(buf.back(), None);
    ///
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// buf.push_back('c');
    /// assert_eq!(buf.back(), Some(&'c'));
    /// ```
    #[inline]
    pub const fn back(&self) -> Option<&T> {
        if self.capacity() == 0 || self.inner.size == 0 {
            // Nothing to do
            return None;
        }
        // SAFETY: `size` is non-zero; back element is guaranteed to be initialized
        Some(unsafe { self.back_maybe_uninit().assume_init_ref() })
    }

    /// Returns a mutable reference to the back element, or `None` if the buffer is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 4>::new();
    /// assert_eq!(buf.back_mut(), None);
    ///
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// buf.push_back('c');
    /// match buf.back_mut() {
    ///     None => (),
    ///     Some(x) => *x = 'z',
    /// }
    /// assert_eq!(buf, ['a', 'b', 'z']);
    /// ```
    #[inline]
    pub const fn back_mut(&mut self) -> Option<&mut T> {
        if self.capacity() == 0 || self.inner.size == 0 {
            // Nothing to do
            return None;
        }
        // SAFETY: `size` is non-zero; back element is guaranteed to be initialized
        Some(unsafe { self.back_maybe_uninit_mut().assume_init_mut() })
    }

    /// Returns a reference to the front element, or `None` if the buffer is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 4>::new();
    /// assert_eq!(buf.front(), None);
    ///
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// buf.push_back('c');
    /// assert_eq!(buf.front(), Some(&'a'));
    /// ```
    #[inline]
    pub const fn front(&self) -> Option<&T> {
        if self.capacity() == 0 || self.inner.size == 0 {
            // Nothing to do
            return None;
        }
        // SAFETY: `size` is non-zero; front element is guaranteed to be initialized
        Some(unsafe { self.front_maybe_uninit().assume_init_ref() })
    }

    /// Returns a mutable reference to the front element, or `None` if the buffer is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 4>::new();
    /// assert_eq!(buf.front_mut(), None);
    ///
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// buf.push_back('c');
    /// match buf.front_mut() {
    ///     None => (),
    ///     Some(x) => *x = 'z',
    /// }
    /// assert_eq!(buf, ['z', 'b', 'c']);
    /// ```
    #[inline]
    pub const fn front_mut(&mut self) -> Option<&mut T> {
        if self.capacity() == 0 || self.inner.size == 0 {
            // Nothing to do
            return None;
        }
        // SAFETY: `size` is non-zero; front element is guaranteed to be initialized
        Some(unsafe { self.front_maybe_uninit_mut().assume_init_mut() })
    }

    /// Returns a reference to the element at the given index from the front of the buffer, or
    /// `None` if the element does not exist.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// This is the same as [`nth_front()`](Self::nth_front).
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 5>::new();
    /// assert_eq!(buf.get(1), None);
    ///
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// buf.push_back('c');
    /// buf.push_back('d');
    /// assert_eq!(buf.get(1), Some(&'b'));
    /// ```
    #[inline]
    pub const fn get(&self, index: usize) -> Option<&T> {
        if self.capacity() == 0 || index >= self.inner.size {
            // Nothing to do
            return None;
        }
        // SAFETY: `index` is in a valid range; it is guaranteed to point to an initialized element
        Some(unsafe { self.get_maybe_uninit(index).assume_init_ref() })
    }

    /// Returns a mutable reference to the element at the given index, or `None` if the element
    /// does not exist.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// This is the same as [`nth_front_mut()`](Self::nth_front_mut).
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 5>::new();
    /// assert_eq!(buf.get_mut(1), None);
    ///
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// buf.push_back('c');
    /// buf.push_back('d');
    /// match buf.get_mut(1) {
    ///     None => (),
    ///     Some(x) => *x = 'z',
    /// }
    /// assert_eq!(buf, ['a', 'z', 'c', 'd']);
    /// ```
    #[inline]
    pub const fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if self.capacity() == 0 || index >= self.inner.size {
            // Nothing to do
            return None;
        }
        // SAFETY: `index` is in a valid range; it is guaranteed to point to an initialized element
        Some(unsafe { self.get_maybe_uninit_mut(index).assume_init_mut() })
    }

    /// Returns a reference to the element at the given index from the front of the buffer, or
    /// `None` if the element does not exist.
    ///
    /// Like most indexing operations, the count starts from zero, so `nth_front(0)` returns the
    /// first value, `nth_front(1)` the second, and so on. Element at index 0 is the front of the
    /// queue.
    ///
    /// This is the same as [`get()`](Self::get).
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 5>::new();
    /// assert_eq!(buf.nth_front(1), None);
    ///
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// buf.push_back('c');
    /// buf.push_back('d');
    /// assert_eq!(buf.nth_front(1), Some(&'b'));
    /// ```
    #[inline]
    pub const fn nth_front(&self, index: usize) -> Option<&T> {
        self.get(index)
    }

    /// Returns a mutable reference to the element at the given index from the front of the buffer,
    /// or `None` if the element does not exist.
    ///
    /// Like most indexing operations, the count starts from zero, so `nth_front_mut(0)` returns
    /// the first value, `nth_front_mut(1)` the second, and so on. Element at index 0 is the front
    /// of the queue.
    ///
    /// This is the same as [`get_mut()`](Self::get_mut).
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 5>::new();
    /// assert_eq!(buf.nth_front_mut(1), None);
    ///
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// buf.push_back('c');
    /// buf.push_back('d');
    /// match buf.nth_front_mut(1) {
    ///     None => (),
    ///     Some(x) => *x = 'z',
    /// }
    /// assert_eq!(buf, ['a', 'z', 'c', 'd']);
    /// ```
    #[inline]
    pub const fn nth_front_mut(&mut self, index: usize) -> Option<&mut T> {
        self.get_mut(index)
    }

    /// Returns a reference to the element at the given index from the back of the buffer, or
    /// `None` if the element does not exist.
    ///
    /// Like most indexing operations, the count starts from zero, so `nth_back(0)` returns the
    /// first value, `nth_back(1)` the second, and so on. Element at index 0 is the back of the
    /// queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 5>::new();
    /// assert_eq!(buf.nth_back(1), None);
    ///
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// buf.push_back('c');
    /// buf.push_back('d');
    /// assert_eq!(buf.nth_back(1), Some(&'c'));
    /// ```
    #[inline]
    pub const fn nth_back(&self, index: usize) -> Option<&T> {
        // TODO: Switch back to using `?` once it's stabilized in `const` contexts
        let index = match self.inner.size.checked_sub(index) {
            Some(index) => index,
            None => return None,
        };
        let index = match index.checked_sub(1) {
            Some(index) => index,
            None => return None,
        };
        self.get(index)
    }

    /// Returns a mutable reference to the element at the given index from the back of the buffer,
    /// or `None` if the element does not exist.
    ///
    /// Like most indexing operations, the count starts from zero, so `nth_back_mut(0)` returns the
    /// first value, `nth_back_mut(1)` the second, and so on. Element at index 0 is the back of the
    /// queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 5>::new();
    /// assert_eq!(buf.nth_back_mut(1), None);
    ///
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// buf.push_back('c');
    /// buf.push_back('d');
    /// match buf.nth_back_mut(1) {
    ///     None => (),
    ///     Some(x) => *x = 'z',
    /// }
    /// assert_eq!(buf, ['a', 'b', 'z', 'd']);
    /// ```
    #[inline]
    pub const fn nth_back_mut(&mut self, index: usize) -> Option<&mut T> {
        // TODO: Switch back to using `?` once it's stabilized in `const` contexts
        let index = match self.inner.size.checked_sub(index) {
            Some(index) => index,
            None => return None,
        };
        let index = match index.checked_sub(1) {
            Some(index) => index,
            None => return None,
        };
        self.get_mut(index)
    }

    /// Appends an element to the back of the buffer.
    ///
    /// If the buffer is full, the element at the front of the buffer is overwritten and returned.
    ///
    /// See also [`try_push_back()`](Self::try_push_back) for a non-overwriting version of this
    /// method.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 3>::new();
    ///
    /// assert_eq!(buf.push_back('a'), None);
    /// assert_eq!(buf, ['a']);
    ///
    /// assert_eq!(buf.push_back('b'), None);
    /// assert_eq!(buf, ['a', 'b']);
    ///
    /// assert_eq!(buf.push_back('c'), None);
    /// assert_eq!(buf, ['a', 'b', 'c']);
    ///
    /// // The buffer is now full; adding more values causes the front elements to be removed and
    /// // returned
    /// assert_eq!(buf.push_back('d'), Some('a'));
    /// assert_eq!(buf, ['b', 'c', 'd']);
    ///
    /// assert_eq!(buf.push_back('e'), Some('b'));
    /// assert_eq!(buf, ['c', 'd', 'e']);
    ///
    /// assert_eq!(buf.push_back('f'), Some('c'));
    /// assert_eq!(buf, ['d', 'e', 'f']);
    /// ```
    pub const fn push_back(&mut self, item: T) -> Option<T> {
        if self.capacity() == 0 {
            // Nothing to do
            return Some(item);
        }

        if self.inner.size >= self.capacity() {
            // At capacity; need to replace the front item
            //
            // SAFETY: if size is greater than 0, the front item is guaranteed to be initialized.
            let replaced_item = mem::replace(
                unsafe { self.front_maybe_uninit_mut().assume_init_mut() },
                item,
            );
            self.inc_start();
            Some(replaced_item)
        } else {
            // Some uninitialized slots left; append at the end
            self.inc_size();
            self.back_maybe_uninit_mut().write(item);
            None
        }
    }

    /// Appends an element to the back of the buffer.
    ///
    /// If the buffer is full, the buffer is not modified and the given element is returned as an
    /// error.
    ///
    /// See also [`push_back()`](Self::push_back) for a version of this method that overwrites the
    /// front of the buffer when full.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 3>::new();
    ///
    /// assert_eq!(buf.try_push_back('a'), Ok(()));
    /// assert_eq!(buf, ['a']);
    ///
    /// assert_eq!(buf.try_push_back('b'), Ok(()));
    /// assert_eq!(buf, ['a', 'b']);
    ///
    /// assert_eq!(buf.try_push_back('c'), Ok(()));
    /// assert_eq!(buf, ['a', 'b', 'c']);
    ///
    /// // The buffer is now full; adding more values results in an error
    /// assert_eq!(buf.try_push_back('d'), Err('d'))
    /// ```
    pub fn try_push_back(&mut self, item: T) -> Result<(), T> {
        if self.capacity() == 0 {
            // Nothing to do
            return Ok(());
        }
        if self.inner.size >= self.capacity() {
            // At capacity; return the pushed item as error
            Err(item)
        } else {
            // Some uninitialized slots left; append at the end
            self.inc_size();
            self.back_maybe_uninit_mut().write(item);
            Ok(())
        }
    }

    /// Appends an element to the front of the buffer.
    ///
    /// If the buffer is full, the element at the back of the buffer is overwritten and returned.
    ///
    /// See also [`try_push_front()`](Self::try_push_front) for a non-overwriting version of this
    /// method.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 3>::new();
    ///
    /// assert_eq!(buf.push_front('a'), None);
    /// assert_eq!(buf, ['a']);
    ///
    /// assert_eq!(buf.push_front('b'), None);
    /// assert_eq!(buf, ['b', 'a']);
    ///
    /// assert_eq!(buf.push_front('c'), None);
    /// assert_eq!(buf, ['c', 'b', 'a']);
    ///
    /// // The buffer is now full; adding more values causes the back elements to be dropped
    /// assert_eq!(buf.push_front('d'), Some('a'));
    /// assert_eq!(buf, ['d', 'c', 'b']);
    ///
    /// assert_eq!(buf.push_front('e'), Some('b'));
    /// assert_eq!(buf, ['e', 'd', 'c']);
    ///
    /// assert_eq!(buf.push_front('f'), Some('c'));
    /// assert_eq!(buf, ['f', 'e', 'd']);
    /// ```
    pub const fn push_front(&mut self, item: T) -> Option<T> {
        if self.capacity() == 0 {
            // Nothing to do
            return Some(item);
        }

        if self.inner.size >= self.capacity() {
            // At capacity; need to replace the back item
            //
            // SAFETY: if size is greater than 0, the back item is guaranteed to be initialized.
            let replaced_item = mem::replace(
                unsafe { self.back_maybe_uninit_mut().assume_init_mut() },
                item,
            );
            self.dec_start();
            Some(replaced_item)
        } else {
            // Some uninitialized slots left; insert at the start
            self.inc_size();
            self.dec_start();
            self.front_maybe_uninit_mut().write(item);
            None
        }
    }

    /// Appends an element to the front of the buffer.
    ///
    /// If the buffer is full, the buffer is not modified and the given element is returned as an
    /// error.
    ///
    /// See also [`push_front()`](Self::push_front) for a version of this method that overwrites the
    /// back of the buffer when full.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 3>::new();
    ///
    /// assert_eq!(buf.try_push_front('a'), Ok(()));
    /// assert_eq!(buf, ['a']);
    ///
    /// assert_eq!(buf.try_push_front('b'), Ok(()));
    /// assert_eq!(buf, ['b', 'a']);
    ///
    /// assert_eq!(buf.try_push_front('c'), Ok(()));
    /// assert_eq!(buf, ['c', 'b', 'a']);
    ///
    /// // The buffer is now full; adding more values results in an error
    /// assert_eq!(buf.try_push_front('d'), Err('d'));
    /// ```
    pub fn try_push_front(&mut self, item: T) -> Result<(), T> {
        if self.capacity() == 0 {
            // Nothing to do
            return Ok(());
        }
        if self.inner.size >= self.capacity() {
            // At capacity; return the pushed item as error
            Err(item)
        } else {
            // Some uninitialized slots left; insert at the start
            self.inc_size();
            self.dec_start();
            self.front_maybe_uninit_mut().write(item);
            Ok(())
        }
    }

    /// Removes and returns an element from the back of the buffer.
    ///
    /// If the buffer is empty, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 3>::from(['a', 'b', 'c']);
    ///
    /// assert_eq!(buf.pop_back(), Some('c'));
    /// assert_eq!(buf.pop_back(), Some('b'));
    /// assert_eq!(buf.pop_back(), Some('a'));
    /// assert_eq!(buf.pop_back(), None);
    /// ```
    pub const fn pop_back(&mut self) -> Option<T> {
        if self.capacity() == 0 || self.inner.size == 0 {
            // Nothing to do
            return None;
        }

        // SAFETY: if size is greater than 0, the back item is guaranteed to be initialized.
        let back = unsafe { self.back_maybe_uninit().assume_init_read() };
        self.dec_size();
        Some(back)
    }

    /// Removes and returns an element from the front of the buffer.
    ///
    /// If the buffer is empty, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 3>::from(['a', 'b', 'c']);
    ///
    /// assert_eq!(buf.pop_front(), Some('a'));
    /// assert_eq!(buf.pop_front(), Some('b'));
    /// assert_eq!(buf.pop_front(), Some('c'));
    /// assert_eq!(buf.pop_front(), None);
    /// ```
    pub const fn pop_front(&mut self) -> Option<T> {
        if self.capacity() == 0 || self.inner.size == 0 {
            // Nothing to do
            return None;
        }

        // SAFETY: if size is greater than 0, the front item is guaranteed to be initialized.
        let front = unsafe { self.front_maybe_uninit().assume_init_read() };
        self.dec_size();
        self.inc_start();
        Some(front)
    }

    /// Removes and returns an element at the specified index.
    ///
    /// If the index is out of bounds, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 3>::from(['a', 'b', 'c']);
    ///
    /// assert_eq!(buf.remove(1), Some('b'));
    /// assert_eq!(buf, ['a', 'c']);
    ///
    /// assert_eq!(buf.remove(5), None);
    /// ```
    pub const fn remove(&mut self, index: usize) -> Option<T> {
        if self.capacity() == 0 || index >= self.inner.size {
            return None;
        }

        let index = add_mod(self.inner.start, index, self.capacity());
        let back_index = add_mod(self.inner.start, self.inner.size - 1, self.capacity());

        // SAFETY: `index` is in a valid range; the element is guaranteed to be initialized
        let item = unsafe { self.inner.items[index].assume_init_read() };

        // SAFETY: the pointers being moved are in a valid range; the elements behind those
        // pointers are guaranteed to be initialized
        unsafe {
            // TODO: optimize for the case where `index < len - index` (i.e. when copying items to
            // the right is cheaper than moving items to the left)
            let ptr = self.inner.items.as_mut_ptr();
            if back_index >= index {
                // Move the values at the right of `index` by 1 position to the left
                ptr::copy(ptr.add(index).add(1), ptr.add(index), back_index - index);
            } else {
                // Move the values at the right of `index` by 1 position to the left
                ptr::copy(
                    ptr.add(index).add(1),
                    ptr.add(index),
                    self.capacity() - index - 1,
                );
                // Move the leftmost value to the end of the array
                ptr::copy(ptr, ptr.add(self.capacity() - 1), 1);
                // Move the values at the left of `back_index` by 1 position to the left
                ptr::copy(ptr.add(1), ptr, back_index);
            }
        }

        self.dec_size();
        Some(item)
    }

    /// Swap the element at index `i` with the element at index `j`.
    ///
    /// # Panics
    ///
    /// If either `i` or `j` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 5>::from(['a', 'b', 'c', 'd']);
    /// assert_eq!(buf, ['a', 'b', 'c', 'd']);
    ///
    /// buf.swap(0, 3);
    /// assert_eq!(buf, ['d', 'b', 'c', 'a']);
    /// ```
    ///
    /// Trying to swap an invalid index panics:
    ///
    /// ```should_panic
    /// use circular_buffer::FixedCircularBuffer;
    /// let mut buf = FixedCircularBuffer::<char, 5>::from(['a', 'b', 'c', 'd']);
    /// buf.swap(0, 7);
    /// ```
    pub const fn swap(&mut self, i: usize, j: usize) {
        assert!(i < self.inner.size, "i index out-of-bounds");
        assert!(j < self.inner.size, "j index out-of-bounds");
        if i != j {
            let i = add_mod(self.inner.start, i, self.capacity());
            let j = add_mod(self.inner.start, j, self.capacity());
            // SAFETY: these are valid pointers
            unsafe {
                ptr::swap_nonoverlapping(&mut self.inner.items[i], &mut self.inner.items[j], 1)
            };
        }
    }

    /// Removes the element at `index` and returns it, replacing it with the back of the buffer.
    ///
    /// Returns `None` if `index` is out-of-bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 5>::from(['a', 'b', 'c', 'd']);
    /// assert_eq!(buf, ['a', 'b', 'c', 'd']);
    ///
    /// assert_eq!(buf.swap_remove_back(2), Some('c'));
    /// assert_eq!(buf, ['a', 'b', 'd']);
    ///
    /// assert_eq!(buf.swap_remove_back(7), None);
    /// ```
    pub const fn swap_remove_back(&mut self, index: usize) -> Option<T> {
        if index >= self.inner.size {
            return None;
        }
        self.swap(index, self.inner.size - 1);
        self.pop_back()
    }

    /// Removes the element at `index` and returns it, replacing it with the front of the buffer.
    ///
    /// Returns `None` if `index` is out-of-bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<char, 5>::from(['a', 'b', 'c', 'd']);
    /// assert_eq!(buf, ['a', 'b', 'c', 'd']);
    ///
    /// assert_eq!(buf.swap_remove_front(2), Some('c'));
    /// assert_eq!(buf, ['b', 'a', 'd']);
    ///
    /// assert_eq!(buf.swap_remove_front(7), None);
    /// ```
    pub const fn swap_remove_front(&mut self, index: usize) -> Option<T> {
        if index >= self.inner.size {
            return None;
        }
        self.swap(index, 0);
        self.pop_front()
    }

    /// Fills the entire capacity of `self` with elements by cloning `value`.
    ///
    /// The elements already present in the buffer (if any) are all replaced by clones of `value`,
    /// and the spare capacity of the buffer is also filled with clones of `value`.
    ///
    /// This is equivalent to clearing the buffer and adding clones of `value` until reaching the
    /// maximum capacity.
    ///
    /// If you want to replace only the existing elements of the buffer, without affecting the spare
    /// capacity, use [`as_mut_slices()`](Self::as_mut_slices) and call [`slice::fill()`] on the
    /// resulting slices.
    ///
    /// See also: [`fill_with()`](Self::fill_with), [`fill_spare()`](Self::fill_spare),
    /// [`fill_spare_with()`](Self::fill_spare_with).
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<u32, 10>::from([1, 2, 3]);
    /// assert_eq!(buf, [1, 2, 3]);
    ///
    /// buf.fill(9);
    /// assert_eq!(buf, [9, 9, 9, 9, 9, 9, 9, 9, 9, 9]);
    /// ```
    ///
    /// If you want to replace existing elements only:
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<u32, 10>::from([1, 2, 3]);
    /// assert_eq!(buf, [1, 2, 3]);
    ///
    /// let (front, back) = buf.as_mut_slices();
    /// front.fill(9);
    /// back.fill(9);
    /// assert_eq!(buf, [9, 9, 9]);
    /// ```
    pub fn fill(&mut self, value: T)
    where
        T: Clone,
    {
        self.clear();
        self.fill_spare(value);
    }

    /// Fills the entire capacity of `self` with elements by calling a closure.
    ///
    /// The elements already present in the buffer (if any) are all replaced by the result of the
    /// closure, and the spare capacity of the buffer is also filled with the result of the
    /// closure.
    ///
    /// This is equivalent to clearing the buffer and adding the result of the closure until
    /// reaching the maximum capacity.
    ///
    /// If you want to replace only the existing elements of the buffer, without affecting the spare
    /// capacity, use [`as_mut_slices()`](Self::as_mut_slices) and call [`slice::fill_with()`] on
    /// the resulting slices.
    ///
    /// See also: [`fill()`](Self::fill), [`fill_spare()`](Self::fill_spare),
    /// [`fill_spare_with()`](Self::fill_spare_with).
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<u32, 10>::from([1, 2, 3]);
    /// assert_eq!(buf, [1, 2, 3]);
    ///
    /// let mut x = 2;
    /// buf.fill_with(|| {
    ///     x *= 2;
    ///     x
    /// });
    /// assert_eq!(buf, [4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]);
    /// ```
    ///
    /// If you want to replace existing elements only:
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<u32, 10>::from([1, 2, 3]);
    /// assert_eq!(buf, [1, 2, 3]);
    ///
    /// let mut x = 2;
    /// let (front, back) = buf.as_mut_slices();
    /// front.fill_with(|| {
    ///     x *= 2;
    ///     x
    /// });
    /// back.fill_with(|| {
    ///     x *= 2;
    ///     x
    /// });
    /// assert_eq!(buf, [4, 8, 16]);
    /// ```
    pub fn fill_with<F>(&mut self, f: F)
    where
        F: FnMut() -> T,
    {
        self.clear();
        self.fill_spare_with(f);
    }

    /// Fills the spare capacity of `self` with elements by cloning `value`.
    ///
    /// The elements already present in the buffer (if any) are unaffected.
    ///
    /// This is equivalent to adding clones of `value` to the buffer until reaching the maximum
    /// capacity.
    ///
    /// See also: [`fill()`](Self::fill), [`fill_with()`](Self::fill_with),
    /// [`fill_spare_with()`](Self::fill_spare_with).
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<u32, 10>::from([1, 2, 3]);
    /// assert_eq!(buf, [1, 2, 3]);
    ///
    /// buf.fill_spare(9);
    /// assert_eq!(buf, [1, 2, 3, 9, 9, 9, 9, 9, 9, 9]);
    /// ```
    pub fn fill_spare(&mut self, value: T)
    where
        T: Clone,
    {
        if self.inner.size == self.capacity() {
            return;
        }
        // TODO Optimize
        while self.inner.size < self.capacity() - 1 {
            self.push_back(value.clone());
        }
        self.push_back(value);
    }

    /// Fills the spare capacity of `self` with elements by calling a closure.
    ///
    /// The elements already present in the buffer (if any) are unaffected.
    ///
    /// This is equivalent adding the result of the closure to the buffer until reaching the
    /// maximum capacity.
    ///
    /// See also: [`fill()`](Self::fill), [`fill_with()`](Self::fill_with),
    /// [`fill_spare()`](Self::fill_spare).
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<u32, 10>::from([1, 2, 3]);
    /// assert_eq!(buf, [1, 2, 3]);
    ///
    /// let mut x = 2;
    /// buf.fill_spare_with(|| {
    ///     x *= 2;
    ///     x
    /// });
    /// assert_eq!(buf, [1, 2, 3, 4, 8, 16, 32, 64, 128, 256]);
    /// ```
    pub fn fill_spare_with<F>(&mut self, mut f: F)
    where
        F: FnMut() -> T,
    {
        if self.capacity() == 0 {
            return;
        }
        // TODO Optimize
        while self.inner.size < self.capacity() {
            self.push_back(f());
        }
    }

    /// Shortens the buffer, keeping only the front `len` elements and dropping the rest.
    ///
    /// If `len` is equal or greater to the buffer's current length, this has no effect.
    ///
    /// Calling `truncate_back(0)` is equivalent to [`clear()`](Self::clear).
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<u32, 4>::from([10, 20, 30]);
    ///
    /// buf.truncate_back(1);
    /// assert_eq!(buf, [10]);
    ///
    /// // Truncating to a length that is greater than the buffer's length has no effect
    /// buf.truncate_back(8);
    /// assert_eq!(buf, [10]);
    /// ```
    pub fn truncate_back(&mut self, len: usize) {
        if self.capacity() == 0 || len >= self.inner.size {
            // Nothing to do
            return;
        }

        let drop_range = len..self.inner.size;
        // SAFETY: `drop_range` is a valid range, so elements within are guaranteed to be
        // initialized. The `size` of the buffer is shrunk before dropping, so no value will be
        // dropped twice in case of panics.
        unsafe { self.drop_range(drop_range) };
        self.inner.size = len;
    }

    /// Shortens the buffer, keeping only the back `len` elements and dropping the rest.
    ///
    /// If `len` is equal or greater to the buffer's current length, this has no effect.
    ///
    /// Calling `truncate_front(0)` is equivalent to [`clear()`](Self::clear).
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<u32, 4>::from([10, 20, 30]);
    ///
    /// buf.truncate_front(1);
    /// assert_eq!(buf, [30]);
    ///
    /// // Truncating to a length that is greater than the buffer's length has no effect
    /// buf.truncate_front(8);
    /// assert_eq!(buf, [30]);
    /// ```
    pub fn truncate_front(&mut self, len: usize) {
        if self.capacity() == 0 || len >= self.inner.size {
            // Nothing to do
            return;
        }

        let drop_len = self.inner.size - len;
        let drop_range = 0..drop_len;
        // SAFETY: `drop_range` is a valid range, so elements within are guaranteed to be
        // initialized. The `start` of the buffer is shrunk before dropping, so no value will be
        // dropped twice in case of panics.
        unsafe { self.drop_range(drop_range) };
        self.inner.start = add_mod(self.inner.start, drop_len, self.capacity());
        self.inner.size = len;
    }

    /// Drops all the elements in the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf = FixedCircularBuffer::<u32, 4>::from([10, 20, 30]);
    /// assert_eq!(buf, [10, 20, 30]);
    /// buf.clear();
    /// assert_eq!(buf, []);
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.truncate_back(0)
    }
}

impl<T> CircularBuffer<T>
where
    T: Clone,
{
    /// Clones and appends all the elements from the slice to the back of the buffer.
    ///
    /// This is an optimized version of [`extend()`](Self::extend) for slices.
    ///
    /// If slice contains more values than the available capacity, the elements at the front of the
    /// buffer are dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let mut buf: FixedCircularBuffer<u32, 5> = FixedCircularBuffer::from([1, 2, 3]);
    /// buf.extend_from_slice(&[4, 5, 6, 7]);
    /// assert_eq!(buf, [3, 4, 5, 6, 7]);
    /// ```
    pub fn extend_from_slice(&mut self, other: &[T]) {
        if self.capacity() == 0 {
            return;
        }

        debug_assert!(self.inner.start < self.capacity(), "start out-of-bounds");
        debug_assert!(self.inner.size <= self.capacity(), "size out-of-bounds");

        if other.len() < self.capacity() {
            // All the elements of `other` fit into the buffer
            let free_size = self.capacity() - self.inner.size;
            let final_size = if other.len() < free_size {
                // All the elements of `other` fit at the back of the buffer
                self.inner.size + other.len()
            } else {
                // Some of the elements of `other` need to overwrite the front of the buffer
                let truncate_to = self.capacity() - other.len();
                self.truncate_front(truncate_to);
                self.capacity()
            };

            let (right, left) = self.slices_uninit_mut();

            let write_len = core::cmp::min(right.len(), other.len());
            right[..write_len].write_clone_of_slice(&other[..write_len]);

            let other = &other[write_len..];
            debug_assert!(left.len() >= other.len());
            let write_len = other.len();
            left[..write_len].write_clone_of_slice(other);

            self.inner.size = final_size;
        } else {
            // `other` overwrites the whole buffer; get only the last `N` elements from `other` and
            // overwrite
            self.clear();
            self.inner.start = 0;

            let other = &other[other.len() - self.capacity()..];
            debug_assert_eq!(self.inner.items.len(), other.len());
            self.inner.items.write_clone_of_slice(other);

            self.inner.size = self.capacity();
        }
    }

    /// Clones the elements of the buffer into a new [`Vec`], leaving the buffer unchanged.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    ///
    /// let buf: FixedCircularBuffer<u32, 5> = FixedCircularBuffer::from([1, 2, 3]);
    /// let vec: Vec<u32> = buf.to_vec();
    ///
    /// assert_eq!(buf, [1, 2, 3]);
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    #[must_use]
    #[cfg(feature = "alloc")]
    pub fn to_vec(&self) -> Vec<T> {
        let mut vec = Vec::with_capacity(self.inner.size);
        vec.extend(self.iter().cloned());
        debug_assert_eq!(vec.len(), self.inner.size);
        vec
    }
}

impl<T> Index<usize> for CircularBuffer<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).expect("index out-of-bounds")
    }
}

impl<T> IndexMut<usize> for CircularBuffer<T> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.get_mut(index).expect("index out-of-bounds")
    }
}

impl<T> Extend<T> for CircularBuffer<T> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        // TODO Optimize
        iter.into_iter().for_each(|item| {
            self.push_back(item);
        });
    }
}

impl<'a, T> Extend<&'a T> for CircularBuffer<T>
where
    T: Copy,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'a T>,
    {
        // TODO Optimize
        iter.into_iter().for_each(|item| {
            self.push_back(*item);
        });
    }
}

impl<'a, T> IntoIterator for &'a CircularBuffer<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self)
    }
}

impl<'a, T> IntoIterator for &'a mut CircularBuffer<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IterMut::new(self)
    }
}
