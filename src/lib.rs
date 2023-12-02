//! This crate implements a [circular buffer], also known as cyclic buffer, circular queue or ring.
//!
//! The main struct is [`CircularBuffer`]. It can live on the stack and does not require any heap
//! memory allocation. A `CircularBuffer` is sequence of elements with a maximum capacity: elements
//! can be added to the buffer, and once the maximum capacity is reached, the elements at the start
//! of the buffer are discarded and overwritten.
//!
//! [circular buffer]: https://en.wikipedia.org/wiki/Circular_buffer
//!
//! # Examples
//!
//! ```
//! use circular_buffer::CircularBuffer;
//!
//! // Initialize a new, empty circular buffer with a capacity of 5 elements
//! let mut buf = CircularBuffer::<5, u32>::new();
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
//! list below includes the most common methods, but see the
//! [`CircularBuffer` struct documentation](CircularBuffer) to see more.
//!
//! ## Adding/removing elements
//!
//! * [`push_back()`](CircularBuffer::push_back)
//! * [`push_front()`](CircularBuffer::push_front)
//! * [`pop_back()`](CircularBuffer::pop_back)
//! * [`pop_front()`](CircularBuffer::pop_front)
//! * [`swap_remove_back()`](CircularBuffer::swap_remove_back)
//! * [`swap_remove_front()`](CircularBuffer::swap_remove_front)
//!
//! ## Getting/mutating elements
//!
//! * [`front()`](CircularBuffer::front), [`front_mut()`](CircularBuffer::front_mut)
//! * [`back()`](CircularBuffer::back), [`back_mut()`](CircularBuffer::back_mut)
//! * [`get()`](CircularBuffer::get), [`get_mut()`](CircularBuffer::get_mut)
//!
//! ## Iterators
//!
//! * [`into_iter()`](CircularBuffer::into_iter)
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
//! use circular_buffer::CircularBuffer;
//! use std::io::Read;
//! use std::io::Write;
//!
//! let mut buf = CircularBuffer::<5, u8>::new();
//! assert_eq!(buf, b"");
//!
//! write!(buf, "hello");
//! assert_eq!(buf, b"hello");
//!
//! write!(buf, "this string will overflow the buffer and wrap around");
//! assert_eq!(buf, b"round");
//!
//! let mut s = String::new();
//! buf.read_to_string(&mut s).expect("failed to read from buffer");
//! assert_eq!(s, "round");
//! assert_eq!(buf, b"");
//! ```
//!
//! # Time complexity
//!
//! Most of the methods implemented by [`CircularBuffer`] run in constant time. Some of the methods
//! may run in linear time if the type of the elements implements [`Drop`], as each element needs
//! to be deallocated one-by-one.
//!
//! | Method                                                                                                                                                 | Complexity                                                         |
//! |--------------------------------------------------------------------------------------------------------------------------------------------------------|--------------------------------------------------------------------|
//! | [`push_back()`](CircularBuffer::push_back), [`push_front()`](CircularBuffer::push_front)                                                               | *O*(1)                                                             |
//! | [`pop_back()`](CircularBuffer::pop_back), [`pop_front()`](CircularBuffer::pop_front)                                                                   | *O*(1)                                                             |
//! | [`remove(i)`](CircularBuffer::remove)                                                                                                                  | *O*(*n* − *i*)                                                     |
//! | [`truncate_back(i)`](CircularBuffer::truncate_back), [`truncate_front(i)`](CircularBuffer::truncate_front)                                             | *O*(*n* − *i*) for types that implement [`Drop`], *O*(1) otherwise |
//! | [`clear()`](CircularBuffer::clear)                                                                                                                     | *O*(*n*) for types that implement [`Drop`], *O*(1) otherwise       |
//! | [`drain(i..j)`](CircularBuffer::drain)                                                                                                                 | *O*(*n* − *j*)                                                     |
//! | [`front()`](CircularBuffer::front), [`back()`](CircularBuffer::back), [`get()`](CircularBuffer::get)                                                   | *O*(1)                                                             |
//! | [`swap()`](CircularBuffer::swap), [`swap_remove_front()`](CircularBuffer::swap_remove_front), [`swap_remove_back()`](CircularBuffer::swap_remove_back) | *O*(1)                                                             |
//! | [`as_slices()`](CircularBuffer::as_slices), [`as_mut_slices()`](CircularBuffer::as_mut_slices)                                                         | *O*(1)                                                             |
//! | [`len()`](CircularBuffer::len), [`capacity()`](CircularBuffer::capacity)                                                                               | *O*(1)                                                             |
//!
//! # Stack vs heap
//!
//! The [`CircularBuffer`] struct is compact and has a fixed size, so it may live on the stack.
//! This can provide optimal performance for small buffers as memory allocation can be avoided.
//!
//! For large buffers, or for buffers that need to be passed around often, it can be useful to
//! allocate the buffer on the heap. Use a [`Box`](std::boxed) for that:
//!
//! ```
//! use circular_buffer::CircularBuffer;
//!
//! let mut buf = CircularBuffer::<4096, u32>::boxed();
//! assert_eq!(buf.len(), 0);
//!
//! for i in 0..1024 {
//!     buf.push_back(i);
//! }
//! assert_eq!(buf.len(), 1024);
//!
//! buf.truncate_back(128);
//! assert_eq!(buf.len(), 128);
//! ```
//!
//! # `no_std`
//!
//! This crate can be used in a [`no_std` environment], although the I/O features and
//! heap-allocation features won't be available in `no_std` mode. By default, this crate uses
//! `std`; to use this crate in `no_std` mode, disable the default features for this crate in your
//! `Cargo.toml`:
//!
//! ```text
//! [dependencies]
//! circular-buffer = { version = "0.1", features = [] }
//! ```
//!
//! [`no_std` environment]: https://docs.rust-embedded.org/book/intro/no-std.html

#![cfg_attr(not(feature = "use_std"), no_std)]

#![cfg_attr(feature = "unstable", feature(const_maybe_uninit_uninit_array))]
#![cfg_attr(feature = "unstable", feature(const_trait_impl))]
#![cfg_attr(feature = "unstable", feature(maybe_uninit_slice))]
#![cfg_attr(feature = "unstable", feature(maybe_uninit_uninit_array))]
#![cfg_attr(feature = "unstable", feature(maybe_uninit_write_slice))]
#![cfg_attr(feature = "unstable", feature(one_sided_range))]
#![cfg_attr(feature = "unstable", feature(slice_take))]

#![cfg_attr(all(feature = "unstable", feature = "use_std"), feature(new_uninit))]

#![warn(missing_debug_implementations)]
#![warn(missing_docs)]
#![warn(pointer_structural_match)]
#![warn(unreachable_pub)]
#![warn(unused_qualifications)]

mod drain;
mod iter;
mod backend;

#[cfg(feature = "use_std")]
mod io;

#[cfg(test)]
mod tests;

#[cfg(feature = "use_std")]
pub mod heap;

use core::cmp::Ordering;
use core::fmt;
use core::hash::Hash;
use core::mem::MaybeUninit;
use core::mem;
use core::ops::RangeBounds;
use core::ptr;
use backend::Backend;


pub use crate::drain::StaticDrain as Drain;
pub use crate::iter::StaticIntoIter as IntoIter;
pub use crate::iter::Iter;
pub use crate::iter::IterMut;

#[cfg(feature = "unstable")]
macro_rules! unstable_const_impl {
    (
        $( #[ $meta:meta ] )*
        impl $( <{ $( $generics:tt )* }> )? const $trait:ident for $type:ty { $( $tt:tt )* }
    ) => {
        $(#[$meta])*
        impl $(<$($generics)*>)? const $trait for $type { $($tt)* }
    }
}

#[cfg(not(feature = "unstable"))]
macro_rules! unstable_const_impl {
    (
        $( #[ $meta:meta ] )*
        impl $( <{ $( $generics:tt )* }> )? const $trait:ident for $type:ty { $( $tt:tt )* }
    ) => {
        $(#[$meta])*
        impl $(<$($generics)*>)? $trait for $type { $($tt)* }
    }
}
pub(crate) use unstable_const_impl;

macro_rules! impl_iter_traits {
    ($( <{ $( $generics:tt )* }> )? - $type:ty) => {
        impl $(<$($generics)*>)? Iterator for $type {
            type Item = T;
        
            #[inline]
            fn next(&mut self) -> Option<Self::Item> {
                self.0.next()
            }

            #[inline]
            fn size_hint(&self) -> (usize, Option<usize>) {
                self.0.size_hint()
            }
        }
        
        impl $(<$($generics)*>)? ExactSizeIterator for $type {
            #[inline]
            fn len(&self) -> usize {
                self.0.len()
            }
        }
        
        impl $(<$($generics)*>)? FusedIterator for $type {}
        
        impl $(<$($generics)*>)? DoubleEndedIterator for $type {
            #[inline]
            fn next_back(&mut self) -> Option<Self::Item> {
                self.0.next_back()
            }
        }
        
        
        impl $(<$($generics)*>)? fmt::Debug for $type 
            where T: fmt::Debug
        {   
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.0.fmt(f)
            }
        }
    };
}
pub(crate) use impl_iter_traits;

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

#[inline]
const unsafe fn slice_assume_init_ref<T>(slice: &[MaybeUninit<T>]) -> &[T] {
    #[cfg(feature = "unstable")]
    { MaybeUninit::slice_assume_init_ref(slice) }
    #[cfg(not(feature = "unstable"))]
    { &*(slice as *const [MaybeUninit<T>] as *const [T]) }
}

#[inline]
unsafe fn slice_assume_init_mut<T>(slice: &mut [MaybeUninit<T>]) -> &mut [T] {
    #[cfg(feature = "unstable")]
    { MaybeUninit::slice_assume_init_mut(slice) }
    #[cfg(not(feature = "unstable"))]
    { &mut *(slice as *mut [MaybeUninit<T>] as *mut [T]) }
}

/// A fixed-size circular buffer.
///
/// A `CircularBuffer` may live on the stack. Wrap the `CircularBuffer` in a [`Box`](std::boxed)
/// using [`CircularBuffer::boxed()`] if you need the struct to be heap-allocated.
///
/// See the [module-level documentation](self) for more details and examples.
#[derive(Ord, Eq, Hash)]
#[repr(transparent)]
pub struct CircularBuffer<const N: usize, T> {
    backend: Backend<T, [MaybeUninit<T>; N]>,
}

impl<const N: usize, T> CircularBuffer<N, T> {
    /// Returns an empty `CircularBuffer`.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::CircularBuffer;
    /// let buf = CircularBuffer::<16, u32>::new();
    /// assert_eq!(buf, []);
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        #[cfg(feature = "unstable")]
        {
            Self {
                size: 0,
                start: 0,
                items: MaybeUninit::uninit_array(),
            }
        }
        #[cfg(not(feature = "unstable"))]
        {
            Self {
                backend: Backend {
                    size: 0,
                    start: 0,
                    items: unsafe { MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init() },
                },
            }
        }
    }

    /// Returns an empty heap-allocated `CircularBuffer`.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::CircularBuffer;
    /// let buf = CircularBuffer::<1024, f64>::boxed();
    /// assert_eq!(buf.len(), 0);
    /// ```
    #[must_use]
    #[cfg(feature = "use_std")]
    #[cfg(feature = "unstable")]
    pub fn boxed() -> Box<Self> {
        let mut uninit: Box<MaybeUninit<Self>> = Box::new_uninit();
        let ptr = uninit.as_mut_ptr();

        unsafe {
            // SAFETY: the pointer contains enough memory to contain `Self` and `addr_of_mut`
            // ensures that the address written to is properly aligned.
            std::ptr::addr_of_mut!((*ptr).size).write(0);
            std::ptr::addr_of_mut!((*ptr).start).write(0);

            // SAFETY: `size` and `start` have been properly initialized to 0; `items` does not
            // need to be initialized if `size` is 0
            uninit.assume_init()
        }
    }

    /// Returns an empty heap-allocated `CircularBuffer`.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::CircularBuffer;
    /// let buf = CircularBuffer::<1024, f64>::boxed();
    /// assert_eq!(buf.len(), 0);
    /// ```
    #[must_use]
    #[cfg(feature = "use_std")]
    #[cfg(not(feature = "unstable"))]
    pub fn boxed() -> Box<Self> {
        // SAFETY: this is emulating the code above, just using direct allocation and raw pointers
        // instead of MaybeUninit. Only `size` and `start` need to be initialized to 0; `items`
        // does not need to be initialized if `size` is 0.
        unsafe {
            let layout = std::alloc::Layout::new::<Self>();
            let ptr = std::alloc::alloc(layout) as *mut Self;
            std::ptr::addr_of_mut!((*ptr).backend.size).write(0);
            std::ptr::addr_of_mut!((*ptr).backend.start).write(0);
            Box::from_raw(ptr)
        }
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
    /// use circular_buffer::CircularBuffer;
    /// let mut buf = CircularBuffer::<16, u32>::new();
    /// assert_eq!(buf.capacity(), 16);
    /// ```
    #[inline]
    pub const fn capacity(&self) -> usize {
        N
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
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<6, char>::from_iter("abcdef".chars());
    /// let drained = buf.drain(3..).collect::<Vec<char>>();
    ///
    /// assert_eq!(drained, ['d', 'e', 'f']);
    /// assert_eq!(buf, ['a', 'b', 'c']);
    /// ```
    ///
    /// Not consuming the draining iterator still removes the range of elements:
    ///
    /// ```
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<6, char>::from_iter("abcdef".chars());
    /// let _ = buf.drain(3..);
    ///
    /// assert_eq!(buf, ['a', 'b', 'c']);
    /// ```
    #[inline]
    #[must_use]
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, N, T>
        where R: RangeBounds<usize>
    {
        Drain(self.backend.drain(range))
    }

    pub(crate) fn into_backend(self) -> Backend<T, [MaybeUninit<T>; N]> {
        self.backend
    }

    impl_buffer!();
}

macro_rules! impl_buffer {
    () => {
        /// Returns the number of elements in the buffer.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(16, u32)]
        /// assert_eq!(buf.len(), 0);
        ///
        /// buf.push_back(1);
        /// buf.push_back(2);
        /// buf.push_back(3);
        /// assert_eq!(buf.len(), 3);
        /// ```
        #[inline]
        pub const fn len(&self) -> usize {
            self.backend.len()
        }

        /// Returns `true` if the buffer contains 0 elements.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(16, u32)]
        /// assert!(buf.is_empty());
        ///
        /// buf.push_back(1);
        /// assert!(!buf.is_empty());
        /// ```
        #[inline]
        pub const fn is_empty(&self) -> bool {
            self.backend.is_empty()
        }

        /// Returns `true` if the number of elements in the buffer matches the buffer capacity.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(5, u32)]
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
            self.len() == self.capacity()
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
        #[doc = USE!()]
        ///
        #[doc = NEW!(5, char)]
        /// buf.extend("abc".chars());
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
        #[doc = USE!()]
        ///
        #[doc = NEW!(5, char)]
        /// buf.extend("abc".chars());
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
            self.backend.iter()
        }

        /// Returns an iterator over the elements of the buffer that allows modifying each value.
        ///
        /// The iterator advances from front to back. Use [`.rev()`](Iter::rev) to advance from back to
        /// front.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(5, u32)]
        /// buf.extend([1, 2, 3]);
        /// for elem in buf.iter_mut() {
        ///     *elem += 5;
        /// }
        /// assert_eq!(buf, [6, 7, 8]);
        /// ```
        #[inline]
        #[must_use]
        pub fn iter_mut(&mut self) -> IterMut<'_, T> {
            self.backend.iter_mut()
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
        #[doc = USE!()]
        ///
        #[doc = NEW!(16, char)]
        /// buf.extend("abcdefghi".chars());
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
        #[doc = USE!()]
        ///
        #[doc = NEW!(16, char)]
        /// buf.extend("abcdefghi".chars());
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
            where R: RangeBounds<usize>
        {
            self.backend.range(range)
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
        #[doc = USE!()]
        ///
        #[doc = NEW!(16, i32)]
        /// buf.extend([1, 2, 3, 4, 5, 6]);
        /// for elem in buf.range_mut(..3) {
        ///     *elem *= -1;
        /// }
        /// assert_eq!(buf, [-1, -2, -3, 4, 5, 6]);
        /// ```
        #[inline]
        #[must_use]
        pub fn range_mut<R>(&mut self, range: R) -> IterMut<'_, T>
            where R: RangeBounds<usize>
        {
            self.backend.range_mut(range)
        }

        /// Rearranges the internal memory of the buffer so that all elements are in a contiguous
        /// slice, which is then returned.
        ///
        /// This method does not allocate and does not change the order of the inserted elements.
        /// Because it returns a mutable slice, any [slice methods](slice) may be called on the
        /// elements of the buffer, such as sorting methods.
        ///
        /// Once the internal storage is contiguous, the [`as_slices()`](Self::as_slices) and
        /// [`as_mut_slices()`](Self::as_mut_slices) methods will return the entire contents
        /// of the deque in a single slice. Adding new elements to the buffer may make the buffer
        /// disjoint (not contiguous).
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
        #[doc = USE!()]
        ///
        /// // Create a new buffer, adding more elements than its capacity
        #[doc = NEW!(4, u32)]
        /// buf.extend([1, 4, 3, 0, 2, 5]);
        /// assert_eq!(buf, [3, 0, 2, 5]);
        ///
        /// // The buffer is disjoint: as_slices() returns two non-empty slices
        /// assert_eq!(buf.as_slices(), (&[3, 0][..], &[2, 5][..]));
        ///
        /// // Make the buffer contiguous
        /// assert_eq!(buf.make_contiguous(), &mut [3, 0, 2, 5]);
        /// // as_slices() now returns a single non-empty slice
        /// assert_eq!(buf.as_slices(), (&[3, 0, 2, 5][..], &[][..]));
        /// // The buffer order of the elements in the buffer did not get modified
        /// assert_eq!(buf, [3, 0, 2, 5]);
        ///
        /// // Make the buffer contiguous and sort its elements
        /// buf.make_contiguous().sort();
        /// assert_eq!(buf, [0, 2, 3, 5]);
        /// ```
        pub fn make_contiguous(&mut self) -> &mut [T] {
        self.backend.make_contiguous()
        }

        /// Returns a pair of slices which contain the elements of this buffer.
        ///
        /// The second slice may be empty if the internal buffer is contiguous.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(4, char)]
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
            self.backend.as_slices()
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
        #[doc = USE!()]
        ///
        #[doc = NEW!(4, char)]
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
            self.backend.as_mut_slices()
        }
        
        /// Returns a reference to the back element, or `None` if the buffer is empty.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(4, char)]
        /// assert_eq!(buf.back(), None);
        ///
        /// buf.push_back('a');
        /// buf.push_back('b');
        /// buf.push_back('c');
        /// assert_eq!(buf.back(), Some(&'c'));
        /// ```
        #[inline]
        pub fn back(&self) -> Option<&T> {
            self.backend.back()
        }

        /// Returns a mutable reference to the back element, or `None` if the buffer is empty.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(4, char)]
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
        pub fn back_mut(&mut self) -> Option<&mut T> {
            self.backend.back_mut()
        }

        /// Returns a reference to the front element, or `None` if the buffer is empty.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(4, char)]
        /// assert_eq!(buf.front(), None);
        ///
        /// buf.push_back('a');
        /// buf.push_back('b');
        /// buf.push_back('c');
        /// assert_eq!(buf.front(), Some(&'a'));
        /// ```
        #[inline]
        pub fn front(&self) -> Option<&T> {
            self.backend.front()
        }

        /// Returns a mutable reference to the front element, or `None` if the buffer is empty.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(4, char)]
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
        pub fn front_mut(&mut self) -> Option<&mut T> {
            self.backend.front_mut()
        }

        /// Returns a reference to the element at the given index, or `None` if the element does not
        /// exist.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(4, char)]
        /// assert_eq!(buf.get(1), None);
        ///
        /// buf.push_back('a');
        /// buf.push_back('b');
        /// buf.push_back('c');
        /// assert_eq!(buf.get(1), Some(&'b'));
        /// ```
        #[inline]
        pub fn get(&self, index: usize) -> Option<&T> {
            self.backend.get(index)
        }

        /// Returns a mutable reference to the element at the given index, or `None` if the element
        /// does not exist.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(4, char)]
        /// assert_eq!(buf.get_mut(1), None);
        ///
        /// buf.push_back('a');
        /// buf.push_back('b');
        /// buf.push_back('c');
        /// match buf.get_mut(1) {
        ///     None => (),
        ///     Some(x) => *x = 'z',
        /// }
        /// assert_eq!(buf, ['a', 'z', 'c']);
        /// ```
        #[inline]
        pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
            self.backend.get_mut(index)
        }

        /// Appends an element to the back of the buffer.
        ///
        /// If the buffer is full, the element at the front of the buffer is automatically dropped and
        /// overwritten.
        ///
        /// See also [`try_push_back()`](Self::try_push_back) for a non-overwriting version
        /// of this method.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(3, char)]
        ///
        /// buf.push_back('a'); assert_eq!(buf, ['a']);
        /// buf.push_back('b'); assert_eq!(buf, ['a', 'b']);
        /// buf.push_back('c'); assert_eq!(buf, ['a', 'b', 'c']);
        /// // The buffer is now full; adding more values causes the front elements to be dropped
        /// buf.push_back('d'); assert_eq!(buf, ['b', 'c', 'd']);
        /// buf.push_back('e'); assert_eq!(buf, ['c', 'd', 'e']);
        /// buf.push_back('f'); assert_eq!(buf, ['d', 'e', 'f']);
        /// ```
        pub fn push_back(&mut self, item: T) {
            self.backend.push_back(item)
        }

        /// Appends an element to the back of the buffer.
        ///
        /// If the buffer is full, the buffer is not modified and the given element is returned as an
        /// error.
        ///
        /// See also [`push_back()`](Self::push_back) for a version of this method that
        /// overwrites the front of the buffer when full.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(3, char)]
        ///
        /// assert_eq!(buf.try_push_back('a'), Ok(())); assert_eq!(buf, ['a']);
        /// assert_eq!(buf.try_push_back('b'), Ok(())); assert_eq!(buf, ['a', 'b']);
        /// assert_eq!(buf.try_push_back('c'), Ok(())); assert_eq!(buf, ['a', 'b', 'c']);
        /// // The buffer is now full; adding more values results in an error
        /// assert_eq!(buf.try_push_back('d'), Err('d'))
        /// ```
        pub fn try_push_back(&mut self, item: T) -> Result<(), T> {
            self.backend.try_push_back(item)
        }

        /// Appends an element to the front of the buffer.
        ///
        /// If the buffer is full, the element at the back of the buffer is automatically dropped and
        /// overwritten.
        ///
        /// See also [`try_push_front()`](Self::try_push_front) for a non-overwriting version
        /// of this method.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(3, char)]
        ///
        /// buf.push_front('a'); assert_eq!(buf, ['a']);
        /// buf.push_front('b'); assert_eq!(buf, ['b', 'a']);
        /// buf.push_front('c'); assert_eq!(buf, ['c', 'b', 'a']);
        /// // The buffer is now full; adding more values causes the back elements to be dropped
        /// buf.push_front('d'); assert_eq!(buf, ['d', 'c', 'b']);
        /// buf.push_front('e'); assert_eq!(buf, ['e', 'd', 'c']);
        /// buf.push_front('f'); assert_eq!(buf, ['f', 'e', 'd']);
        /// ```
        pub fn push_front(&mut self, item: T) {
            self.backend.push_front(item)
        }

        /// Appends an element to the front of the buffer.
        ///
        /// If the buffer is full, the buffer is not modified and the given element is returned as an
        /// error.
        ///
        /// See also [`push_front()`](Self::push_front) for a version of this method that
        /// overwrites the back of the buffer when full.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(3, char)]
        ///
        /// assert_eq!(buf.try_push_front('a'), Ok(())); assert_eq!(buf, ['a']);
        /// assert_eq!(buf.try_push_front('b'), Ok(())); assert_eq!(buf, ['b', 'a']);
        /// assert_eq!(buf.try_push_front('c'), Ok(())); assert_eq!(buf, ['c', 'b', 'a']);
        /// // The buffer is now full; adding more values results in an error
        /// assert_eq!(buf.try_push_front('d'), Err('d'));
        /// ```
        pub fn try_push_front(&mut self, item: T) -> Result<(), T> {
            self.backend.try_push_front(item)
        }

        /// Removes and returns an element from the back of the buffer.
        ///
        /// If the buffer is empty, `None` is returned.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(3, char)]
        /// buf.extend(['a', 'b', 'c']);
        ///
        /// assert_eq!(buf.pop_back(), Some('c'));
        /// assert_eq!(buf.pop_back(), Some('b'));
        /// assert_eq!(buf.pop_back(), Some('a'));
        /// assert_eq!(buf.pop_back(), None);
        /// ```
        pub fn pop_back(&mut self) -> Option<T> {
            self.backend.pop_back()
        }

        /// Removes and returns an element from the front of the buffer.
        ///
        /// If the buffer is empty, `None` is returned.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(3, char)]
        /// buf.extend(['a', 'b', 'c']);
        ///
        /// assert_eq!(buf.pop_front(), Some('a'));
        /// assert_eq!(buf.pop_front(), Some('b'));
        /// assert_eq!(buf.pop_front(), Some('c'));
        /// assert_eq!(buf.pop_front(), None);
        /// ```
        pub fn pop_front(&mut self) -> Option<T> {
            self.backend.pop_front()
        }

        /// Removes and returns an element at the specified index.
        ///
        /// If the index is out of bounds, `None` is returned.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(3, char)]
        /// buf.extend(['a', 'b', 'c']);
        ///
        /// assert_eq!(buf.remove(1), Some('b'));
        /// assert_eq!(buf, ['a', 'c']);
        ///
        /// assert_eq!(buf.remove(5), None);
        /// ```
        pub fn remove(&mut self, index: usize) -> Option<T> {
            self.backend.remove(index)
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
        #[doc = USE!()]
        ///
        #[doc = NEW!(5, char)]
        /// buf.extend(['a', 'b', 'c', 'd']);
        /// assert_eq!(buf, ['a', 'b', 'c', 'd']);
        ///
        /// buf.swap(0, 3);
        /// assert_eq!(buf, ['d', 'b', 'c', 'a']);
        /// ```
        ///
        /// Trying to swap an invalid index panics:
        ///
        /// ```should_panic
        #[doc = USE!()]
        #[doc = NEW!(5, char)]
        /// buf.extend(['a', 'b', 'c', 'd']);
        /// buf.swap(0, 7);
        /// ```
        pub fn swap(&mut self, i: usize, j: usize) {
            self.backend.swap(i, j)
        }

        /// Removes the element at `index` and returns it, replacing it with the back of the buffer.
        ///
        /// Returns `None` if `index` is out-of-bounds.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(5, char)]
        /// buf.extend(['a', 'b', 'c', 'd']);
        /// assert_eq!(buf, ['a', 'b', 'c', 'd']);
        ///
        /// assert_eq!(buf.swap_remove_back(2), Some('c'));
        /// assert_eq!(buf, ['a', 'b', 'd']);
        ///
        /// assert_eq!(buf.swap_remove_back(7), None);
        /// ```
        pub fn swap_remove_back(&mut self, index: usize) -> Option<T> {
            self.backend.swap_remove_back(index)
        }

        /// Removes the element at `index` and returns it, replacing it with the front of the buffer.
        ///
        /// Returns `None` if `index` is out-of-bounds.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(5, char)]
        /// buf.extend(['a', 'b', 'c', 'd']);
        /// assert_eq!(buf, ['a', 'b', 'c', 'd']);
        ///
        /// assert_eq!(buf.swap_remove_front(2), Some('c'));
        /// assert_eq!(buf, ['b', 'a', 'd']);
        ///
        /// assert_eq!(buf.swap_remove_front(7), None);
        /// ```
        pub fn swap_remove_front(&mut self, index: usize) -> Option<T> {
        self.backend.swap_remove_front(index)
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
        #[doc = USE!()]
        ///
        #[doc = NEW!(4, u32)]
        /// buf.extend([10, 20, 30]);
        ///
        /// buf.truncate_back(1);
        /// assert_eq!(buf, [10]);
        ///
        /// // Truncating to a length that is greater than the buffer's length has no effect
        /// buf.truncate_back(8);
        /// assert_eq!(buf, [10]);
        /// ```
        pub fn truncate_back(&mut self, len: usize) {
            self.backend.truncate_back(len)
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
        #[doc = USE!()]
        ///
        #[doc = NEW!(4, u32)]
        /// buf.extend([10, 20, 30]);
        ///
        /// buf.truncate_front(1);
        /// assert_eq!(buf, [30]);
        ///
        /// // Truncating to a length that is greater than the buffer's length has no effect
        /// buf.truncate_front(8);
        /// assert_eq!(buf, [30]);
        /// ```
        pub fn truncate_front(&mut self, len: usize) {
            self.backend.truncate_front(len)
        }

        /// Drops all the elements in the buffer.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = USE!()]
        ///
        #[doc = NEW!(4, u32)]
        /// buf.extend([10, 20, 30]);
        /// assert_eq!(buf, [10, 20, 30]);
        /// buf.clear();
        /// assert_eq!(buf, []);
        /// ```
        #[inline]
        pub fn clear(&mut self) {
            self.backend.clear()
        }
    }
}
pub(crate) use impl_buffer;

impl<const N: usize, T> CircularBuffer<N, T>
    where T: Clone
{
    /// Clones and appends all the elements from the slice to the back of the buffer.
    ///
    /// This is an optimized version of [`extend()`](CircularBuffer::extend) for slices.
    ///
    /// If slice contains more values than the available capacity, the elements at the front of the
    /// buffer are dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf: CircularBuffer<5, u32> = CircularBuffer::from([1, 2, 3]);
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
    /// use circular_buffer::CircularBuffer;
    ///
    /// let buf: CircularBuffer<5, u32> = CircularBuffer::from([1, 2, 3]);
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

unstable_const_impl! {
    impl<{const N: usize, T}> const Default for CircularBuffer<N, T> {
        #[inline]
        fn default() -> Self {
            Self::new()
        }
    }
}

impl<const N: usize, const M: usize, T> From<[T; M]> for CircularBuffer<N, T> {
    fn from(mut arr: [T; M]) -> Self {
        #[cfg(feature = "unstable")]
        let mut elems = MaybeUninit::<T>::uninit_array();
        #[cfg(not(feature = "unstable"))]
        let mut elems = unsafe { MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init() };
        let arr_ptr = &arr as *const T as *const MaybeUninit<T>;
        let elems_ptr = &mut elems as *mut MaybeUninit<T>;
        let size = if N >= M { M } else { N };

        // SAFETY:
        // - `M - size` is non-negative, and `arr_ptr.add(M - size)` points to a memory location
        //   that contains exactly `size` elements
        // - `elems_ptr` points to a memory location that contains exactly `N` elements, and `N` is
        //   greater than or equal to `size`
        unsafe { ptr::copy_nonoverlapping(arr_ptr.add(M - size), elems_ptr, size); }

        // Prevent destructors from running on those elements that we've taken ownership of; only
        // destroy the elements that were discareded
        //
        // SAFETY: All elements in `arr` are initialized; `forget` will make sure that destructors
        // are not run twice
        unsafe { ptr::drop_in_place(&mut arr[..M - size]); }
        mem::forget(arr);

        let backend = Backend { size, start: 0, items: elems };
        Self { backend }
    }
}

impl<const N: usize, T> FromIterator<T> for CircularBuffer<N, T> {
    fn from_iter<I>(iter: I) -> Self
        where I: IntoIterator<Item = T>
    {
        // TODO Optimize
        let mut buf = Self::new();
        iter.into_iter().for_each(|item| buf.push_back(item));
        buf
    }
}

impl<const N: usize, T> Extend<T> for CircularBuffer<N, T> {
    fn extend<I>(&mut self, iter: I)
        where I: IntoIterator<Item = T>
    {
        self.backend.extend(iter)
    }
}

impl<'a, const N: usize, T> Extend<&'a T> for CircularBuffer<N, T>
    where T: Copy
{
    fn extend<I>(&mut self, iter: I)
        where I: IntoIterator<Item = &'a T>
    {
        self.backend.extend(iter)
    }
}

unstable_const_impl! {
    impl<{const N: usize, T}> const IntoIterator for CircularBuffer<N, T> {
        type Item = T;
        type IntoIter = IntoIter<N, T>;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            IntoIter(self.backend.into_iter())
        }
    }
}

unstable_const_impl! {
    impl<{'a, const N: usize, T}> const IntoIterator for &'a CircularBuffer<N, T> {
        type Item = &'a T;
        type IntoIter = Iter<'a, T>;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            Iter::new(&self.backend)
        }
    }
}

impl<const N: usize, const M: usize, T, U> PartialEq<CircularBuffer<M, U>> for CircularBuffer<N, T>
    where T: PartialEq<U>
{
    fn eq(&self, other: &CircularBuffer<M, U>) -> bool {
        self.backend.eq(&other.backend)
    }
}

impl<const N: usize, T, U> PartialEq<[U]> for CircularBuffer<N, T>
    where T: PartialEq<U>
{
    fn eq(&self, other: &[U]) -> bool {
        self.backend.eq(other)
    }
}

impl<const N: usize, const M: usize, T, U> PartialEq<[U; M]> for CircularBuffer<N, T>
    where T: PartialEq<U>
{
    #[inline]
    fn eq(&self, other: &[U; M]) -> bool {
        self == &other[..]
    }
}

impl<'a, const N: usize, T, U> PartialEq<&'a [U]> for CircularBuffer<N, T>
    where T: PartialEq<U>
{
    #[inline]
    fn eq(&self, other: &&'a [U]) -> bool {
        self == *other
    }
}

impl<'a, const N: usize, T, U> PartialEq<&'a mut [U]> for CircularBuffer<N, T>
    where T: PartialEq<U>
{
    #[inline]
    fn eq(&self, other: &&'a mut [U]) -> bool {
        self == *other
    }
}

impl<'a, const N: usize, const M: usize, T, U> PartialEq<&'a [U; M]> for CircularBuffer<N, T>
    where T: PartialEq<U>
{
    #[inline]
    fn eq(&self, other: &&'a [U; M]) -> bool {
        self == *other
    }
}

impl<'a, const N: usize, const M: usize, T, U> PartialEq<&'a mut [U; M]> for CircularBuffer<N, T>
    where T: PartialEq<U>
{
    #[inline]
    fn eq(&self, other: &&'a mut [U; M]) -> bool {
        self == *other
    }
}

impl<const N: usize, const M: usize, T, U> PartialOrd<CircularBuffer<M, U>> for CircularBuffer<N, T>
    where T: PartialOrd<U>
{
    fn partial_cmp(&self, other: &CircularBuffer<M, U>) -> Option<Ordering> {
        self.backend.partial_cmp(&other.backend)
    }
}

impl<const N: usize, T> Clone for CircularBuffer<N, T>
    where T: Clone
{
    fn clone(&self) -> Self {
        // TODO Optimize
        Self::from_iter(self.iter().cloned())
    }

    fn clone_from(&mut self, other: &Self) {
        // TODO Optimize
        self.clear();
        self.extend(other.iter().cloned());
    }
}

impl<const N: usize, T> fmt::Debug for CircularBuffer<N, T>
    where T: fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.backend.fmt(f)
    }
}

macro_rules! USE {
    () => { "use circular_buffer::CircularBuffer;" };
}
macro_rules! NEW {
    ($N:literal,$ty:ty) => {
        concat!("let mut buf = CircularBuffer::<",$N,", ",stringify!($ty),">::new();")
    };
}
use {USE, NEW};