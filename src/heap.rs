//! This module provides [`HeapCircularBuffer`], a circular buffer variant with
//! runtime determined capacity. This variant is only available in `std`
//! environments under the `use_std` feature.
//!
//! # Examples
//!
//! ```
//! use circular_buffer::heap::HeapCircularBuffer;
//!
//! // This does _not_ need to be known at compile time. It could
//! // be loaded for example from a file or database query.
//! let capacity = 5; 
//! // Initialize a new, empty circular buffer with a capacity of `capacity` elements
//! let mut buf = HeapCircularBuffer::<u32>::with_capacity(capacity);
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
//! [`HeapCircularBuffer`] has the same interface as [`CircularBuffer`].
//! Checkout the [struct documentation] and [crate documentation][Interface] for
//! more details.
//!
//! # Time complexity
//! See the [crate documentation][TimeComplexity] for more details
//!
//! [`CircularBuffer`]: crate::CircularBuffer
//! [struct documentation]: HeapCircularBuffer
//! [Interface]: crate#interface
//! [TimeComplexity]: crate#time-complexity 

use core::{ptr, fmt};
use core::cmp::Ordering;
use core::mem::{MaybeUninit, self};
use core::ops::RangeBounds;
use crate::{backend::Backend, Iter, IterMut};
use crate::unstable_const_impl;

pub use crate::drain::HeapDrain;
pub use crate::iter::HeapIntoIter;


/// A fixed-size circular buffer allocated on the heap.
///
/// A `HeapCircularBuffer` can be allocted with runtime known capacity.
///
/// See the [module-level documentation](self) for more details and examples.
#[derive(Ord, Eq, Hash)]
#[repr(transparent)]
pub struct HeapCircularBuffer<T> {
    backend: Backend<T, Box<[MaybeUninit<T>]>>,
}

impl <T> HeapCircularBuffer<T> {
     /// Returns an empty [`HeapCircularBuffer`].
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::heap::HeapCircularBuffer;
    /// let buf = HeapCircularBuffer::<u32>::with_capacity(16);
    /// assert_eq!(buf, []);
    /// ```
    #[inline]
    #[must_use]
    pub fn with_capacity(cap: usize) -> Self {
        let slice = if cap == 0 || mem::size_of::<T>() == 0 {
            ptr::slice_from_raw_parts_mut(ptr::NonNull::dangling().as_ptr(), cap)
        } else {
            let layout = std::alloc::Layout::array::<T>(cap).expect("layout overflow");
            // SAFETY: `T` is not a ZST, and `cap` is not 0
            let ptr = unsafe { std::alloc::alloc(layout) as *mut MaybeUninit<T> };
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }
            ptr::slice_from_raw_parts_mut(ptr, cap)
        };
        Self {
            // SAFETY: "It is valid to convert both ways between a Box and a raw
            // pointer allocated with the Global allocator, given that the Layout
            // used with the allocator is correct for the type."
            // https://doc.rust-lang.org/stable/std/boxed/index.html#memory-layout
            backend: unsafe { Backend::new(Box::from_raw(slice)) }
        }
    }
    /// Returns the capacity of the buffer.
    ///
    /// This is the maximum number of elements that the buffer can hold.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::heap::HeapCircularBuffer;
    /// let mut buf = HeapCircularBuffer::<u32>::with_capacity(16);
    /// assert_eq!(buf.capacity(), 16);
    /// ```
    #[inline]
    pub const fn capacity(&self) -> usize {
        self.backend.items.len()
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
    /// use circular_buffer::heap::HeapCircularBuffer;
    ///
    /// let mut buf = HeapCircularBuffer::<char>::with_capacity(6);
    /// buf.extend("abcdef".chars());
    /// let drained = buf.drain(3..).collect::<Vec<char>>();
    ///
    /// assert_eq!(drained, ['d', 'e', 'f']);
    /// assert_eq!(buf, ['a', 'b', 'c']);
    /// ```
    ///
    /// Not consuming the draining iterator still removes the range of elements:
    ///
    /// ```
    /// use circular_buffer::heap::HeapCircularBuffer;
    ///
    /// let mut buf = HeapCircularBuffer::<char>::with_capacity(6);
    /// buf.extend("abcdef".chars());
    /// let _ = buf.drain(3..);
    ///
    /// assert_eq!(buf, ['a', 'b', 'c']);
    /// ```
    #[inline]
    #[must_use]
    pub fn drain<R>(&mut self, range: R) -> HeapDrain<'_, T>
        where R: RangeBounds<usize>
    {
        HeapDrain(self.backend.drain(range))
    }

    pub(crate) fn into_backend(self) -> Backend<T, Box<[MaybeUninit<T>]>> {
        self.backend
    }

    super::impl_buffer!();
}

impl<T> HeapCircularBuffer<T>
    where T: Clone
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
    /// use circular_buffer::heap::HeapCircularBuffer;
    ///
    /// let mut buf: HeapCircularBuffer<u32> = HeapCircularBuffer::with_capacity(5);
    /// buf.extend([1, 2, 3]);
    /// 
    /// buf.extend_from_slice(&[4, 5, 6, 7]);
    /// assert_eq!(buf, [3, 4, 5, 6, 7]);
    /// ```
    pub fn extend_from_slice(&mut self, other: &[T]) {
        self.backend.extend_from_slice(other)
    }

    /// Clones the elements of the buffer into a new [`Vec`], leaving the buffer unchanged.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::heap::HeapCircularBuffer;
    ///
    /// let mut buf: HeapCircularBuffer<u32> = HeapCircularBuffer::with_capacity(5);
    /// buf.extend([1, 2, 3]);
    /// let vec: Vec<u32> = buf.to_vec();
    ///
    /// assert_eq!(buf, [1, 2, 3]);
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    #[must_use]
    #[cfg(feature = "use_std")]
    pub fn to_vec(&self) -> Vec<T> {
        self.backend.to_vec()
    }
}

impl<T> Extend<T> for HeapCircularBuffer<T> {
    fn extend<I>(&mut self, iter: I)
        where I: IntoIterator<Item = T>
    {
        self.backend.extend(iter)
    }
}

impl<'a, T> Extend<&'a T> for HeapCircularBuffer<T>
    where T: Copy
{
    fn extend<I>(&mut self, iter: I)
        where I: IntoIterator<Item = &'a T>
    {
        self.backend.extend(iter)
    }
}

unstable_const_impl! {
    impl<{T}> const IntoIterator for HeapCircularBuffer<T> {
        type Item = T;
        type IntoIter = HeapIntoIter<T>;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            HeapIntoIter(self.backend.into_iter())
        }
    }
}

unstable_const_impl! {
    impl<{'a, T}> const IntoIterator for &'a HeapCircularBuffer<T> {
        type Item = &'a T;
        type IntoIter = Iter<'a, T>;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            Iter::new(&self.backend)
        }
    }
}

impl<T, U> PartialEq<HeapCircularBuffer<U>> for HeapCircularBuffer<T>
    where T: PartialEq<U>
{
    fn eq(&self, other: &HeapCircularBuffer<U>) -> bool {
        self.backend.eq(&other.backend)
    }
}

impl<T, U> PartialEq<[U]> for HeapCircularBuffer<T>
    where T: PartialEq<U>
{
    fn eq(&self, other: &[U]) -> bool {
        self.backend.eq(other)
    }
}

impl<const M: usize, T, U> PartialEq<[U; M]> for HeapCircularBuffer<T>
    where T: PartialEq<U>
{
    #[inline]
    fn eq(&self, other: &[U; M]) -> bool {
        self == &other[..]
    }
}

impl<'a, T, U> PartialEq<&'a [U]> for HeapCircularBuffer<T>
    where T: PartialEq<U>
{
    #[inline]
    fn eq(&self, other: &&'a [U]) -> bool {
        self == *other
    }
}

impl<'a, T, U> PartialEq<&'a mut [U]> for HeapCircularBuffer<T>
    where T: PartialEq<U>
{
    #[inline]
    fn eq(&self, other: &&'a mut [U]) -> bool {
        self == *other
    }
}

impl<'a, const M: usize, T, U> PartialEq<&'a [U; M]> for HeapCircularBuffer<T>
    where T: PartialEq<U>
{
    #[inline]
    fn eq(&self, other: &&'a [U; M]) -> bool {
        self == *other
    }
}

impl<'a, const M: usize, T, U> PartialEq<&'a mut [U; M]> for HeapCircularBuffer<T>
    where T: PartialEq<U>
{
    #[inline]
    fn eq(&self, other: &&'a mut [U; M]) -> bool {
        self == *other
    }
}

impl<T, U> PartialOrd<HeapCircularBuffer<U>> for HeapCircularBuffer<T>
    where T: PartialOrd<U>
{
    fn partial_cmp(&self, other: &HeapCircularBuffer<U>) -> Option<Ordering> {
        self.backend.partial_cmp(&other.backend)
    }
}

impl<T> Clone for HeapCircularBuffer<T>
    where T: Clone
{
    fn clone(&self) -> Self {
        // TODO Optimize
        let mut this = Self::with_capacity(self.capacity());
        this.extend(self.iter().cloned());
        this

    }

    fn clone_from(&mut self, other: &Self) {
        // TODO Optimize
        self.clear();
        self.extend(other.iter().cloned());
    }
}

impl<T> fmt::Debug for HeapCircularBuffer<T>
    where T: fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.backend.fmt(f)
    }
}

macro_rules! USE {
    () => { "use circular_buffer::heap::HeapCircularBuffer;" };
}

macro_rules! NEW {
    ($N:literal,$ty:ty) => {
        concat!("let mut buf = HeapCircularBuffer::<",stringify!($ty),">::with_capacity(",$N,");")
    };
}
use {USE, NEW};