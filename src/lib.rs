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
//! assert_eq!(buf.to_vec(), vec![1, 2, 3]);
//!
//! // Add more elements to fill the buffer capacity completely
//! buf.push_back(4);
//! buf.push_back(5);
//! assert_eq!(buf.to_vec(), vec![1, 2, 3, 4, 5]);
//!
//! // Adding more elements than the buffer can contain causes the front elements to be
//! // automatically dropped
//! buf.push_back(6);
//! assert_eq!(buf.to_vec(), vec![2, 3, 4, 5, 6]); // `1` got dropped to make room for `6`
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

#![cfg_attr(feature = "unstable", feature(const_maybe_uninit_assume_init))]
#![cfg_attr(feature = "unstable", feature(const_maybe_uninit_uninit_array))]
#![cfg_attr(feature = "unstable", feature(const_mut_refs))]
#![cfg_attr(feature = "unstable", feature(const_slice_index))]
#![cfg_attr(feature = "unstable", feature(const_slice_split_at_mut))]
#![cfg_attr(feature = "unstable", feature(const_slice_split_at_not_mut))]
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

mod iter;

#[cfg(feature = "use_std")]
mod io;

#[cfg(test)]
mod tests;

use core::cmp::Ordering;
use core::fmt;
use core::hash::Hash;
use core::hash::Hasher;
use core::mem::MaybeUninit;
use core::mem;
use core::ops::Range;
use core::ops::RangeBounds;
use core::ptr;

pub use crate::iter::IntoIter;
pub use crate::iter::Iter;
pub use crate::iter::IterMut;

macro_rules! unstable_const_fn {
    (
        $( #[ $meta:meta ] )*
        $vis:vis const fn $fn:ident $( <{ $( $generics:tt )* }> )? ( $( $arg:tt )* )
        $( -> $out:ty )? { $( $tt:tt )* }
    ) => {
        #[cfg(feature = "unstable")]
        $(#[$meta])*
        $vis const fn $fn $(<$($generics)*>)? ($($arg)*) $(-> $out)? { $($tt)* }

        #[cfg(not(feature = "unstable"))]
        $(#[$meta])*
        $vis fn $fn $(<$($generics)*>)? ($($arg)*) $(-> $out)? { $($tt)* }
    }
}

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

use unstable_const_fn;

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

/// A fixed-size circular buffer.
///
/// A `CircularBuffer` may live on the stack. Wrap the `CircularBuffer` in a [`Box`](std::boxed)
/// using [`CircularBuffer::boxed()`] if you need the struct to be heap-allocated.
///
/// See the [module-level documentation](self) for more details and examples.
pub struct CircularBuffer<const N: usize, T> {
    size: usize,
    start: usize,
    items: [MaybeUninit<T>; N],
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
                size: 0,
                start: 0,
                items: unsafe { MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init() },
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
            std::ptr::addr_of_mut!((*ptr).size).write(0);
            std::ptr::addr_of_mut!((*ptr).start).write(0);
            Box::from_raw(ptr)
        }
    }

    /// Returns the number of elements in the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<16, u32>::new();
    /// assert_eq!(buf.len(), 0);
    ///
    /// buf.push_back(1);
    /// buf.push_back(2);
    /// buf.push_back(3);
    /// assert_eq!(buf.len(), 3);
    /// ```
    #[inline]
    pub const fn len(&self) -> usize {
        self.size
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


    /// Returns `true` if the buffer contains 0 elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<16, u32>::new();
    /// assert!(buf.is_empty());
    ///
    /// buf.push_back(1);
    /// assert!(!buf.is_empty());
    /// ```
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Returns `true` if the number of elements in the buffer matches the buffer capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<5, u32>::new();
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
        self.size == N
    }

    unstable_const_fn! {
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
        /// use circular_buffer::CircularBuffer;
        ///
        /// let buf = CircularBuffer::<5, char>::from_iter("abc".chars());
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
        /// use circular_buffer::CircularBuffer;
        ///
        /// let buf = CircularBuffer::<5, char>::from_iter("abc".chars());
        /// let mut it = buf.iter().rev();
        ///
        /// assert_eq!(it.next(), Some(&'c'));
        /// assert_eq!(it.next(), Some(&'b'));
        /// assert_eq!(it.next(), Some(&'a'));
        /// assert_eq!(it.next(), None);
        /// ```
        #[inline]
        #[must_use]
        pub const fn iter(&self) -> Iter<'_, T> {
            Iter::new(self)
        }
    }

    unstable_const_fn! {
        /// Returns an iterator over the elements of the buffer that allows modifying each value.
        ///
        /// The iterator advances from front to back. Use [`.rev()`](Iter::rev) to advance from
        /// back to front.
        ///
        /// # Examples
        ///
        /// ```
        /// use circular_buffer::CircularBuffer;
        ///
        /// let mut buf = CircularBuffer::<5, u32>::from([1, 2, 3]);
        /// for elem in buf.iter_mut() {
        ///     *elem += 5;
        /// }
        /// assert_eq!(buf, [6, 7, 8]);
        /// ```
        #[inline]
        #[must_use]
        pub const fn iter_mut(&mut self) -> IterMut<'_, T> {
            IterMut::new(self)
        }
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
    /// use circular_buffer::CircularBuffer;
    ///
    /// let buf = CircularBuffer::<16, char>::from_iter("abcdefghi".chars());
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
    /// use circular_buffer::CircularBuffer;
    ///
    /// let buf = CircularBuffer::<16, char>::from_iter("abcdefghi".chars());
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
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<16, i32>::from_iter([1, 2, 3, 4, 5, 6]);
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
        IterMut::over_range(self, range)
    }

    // TODO #[inline]
    // TODO #[must_use]
    // TODO pub const fn drain(&mut self) -> Drain<'_, N, T> {
    // TODO     todo!()
    // TODO }

    unstable_const_fn! {
        /// Returns a pair of slices which contain the elements of this buffer.
        ///
        /// The second slice may be empty if the internal buffer is contiguous.
        ///
        /// # Examples
        ///
        /// ```
        /// use circular_buffer::CircularBuffer;
        ///
        /// let mut buf = CircularBuffer::<4, char>::new();
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
        pub const fn as_slices(&self) -> (&[T], &[T]) {
            if N == 0 || self.size == 0 {
                return (&[], &[]);
            }

            debug_assert!(self.start < N, "start out-of-bounds");
            debug_assert!(self.size <= N, "size out-of-bounds");

            let start = self.start;
            let end = add_mod(self.start, self.size, N);

            let (left, right) = if start < end {
                (&self.items[start..end], &[][..])
            } else {
                let (right, left) = self.items.split_at(end);
                let left = &left[start - end..];
                (left, right)
            };

            // SAFETY: The elements in these slices are guaranteed to be initialized
            #[cfg(feature = "unstable")]
            unsafe {
                (MaybeUninit::slice_assume_init_ref(left),
                 MaybeUninit::slice_assume_init_ref(right))
            }
            #[cfg(not(feature = "unstable"))]
            unsafe {
                (&*(left as *const [MaybeUninit<T>] as *const [T]),
                 &*(right as *const [MaybeUninit<T>] as *const [T]))
            }
        }
    }

    unstable_const_fn! {
        /// Returns a pair of mutable slices which contain the elements of this buffer.
        ///
        /// These slices can be used to modify or replace the elements in the buffer.
        ///
        /// The second slice may be empty if the internal buffer is contiguous.
        ///
        /// # Examples
        ///
        /// ```
        /// use circular_buffer::CircularBuffer;
        ///
        /// let mut buf = CircularBuffer::<4, char>::new();
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
        pub const fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
            if N == 0 || self.size == 0 {
                return (&mut [][..], &mut [][..]);
            }

            debug_assert!(self.start < N, "start out-of-bounds");
            debug_assert!(self.size <= N, "size out-of-bounds");

            let start = self.start;
            let end = add_mod(self.start, self.size, N);

            let (left, right) = if start < end {
                (&mut self.items[start..end], &mut [][..])
            } else {
                let (right, left) = self.items.split_at_mut(end);
                let left = &mut left[start - end..];
                (left, right)
            };

            // SAFETY: The elements in these slices are guaranteed to be initialized
            #[cfg(feature = "unstable")]
            unsafe {
                (MaybeUninit::slice_assume_init_mut(left),
                 MaybeUninit::slice_assume_init_mut(right))
            }
            #[cfg(not(feature = "unstable"))]
            unsafe {
                (&mut *(left as *mut [MaybeUninit<T>] as *mut [T]),
                 &mut *(right as *mut [MaybeUninit<T>] as *mut [T]))
            }
        }
    }

    #[inline]
    fn front_maybe_uninit_mut(&mut self) -> &mut MaybeUninit<T> {
        debug_assert!(self.size > 0, "empty buffer");
        debug_assert!(self.start < N, "start out-of-bounds");
        &mut self.items[self.start]
    }

    #[inline]
    const fn front_maybe_uninit(&self) -> &MaybeUninit<T> {
        debug_assert!(self.size > 0, "empty buffer");
        debug_assert!(self.size <= N, "size out-of-bounds");
        debug_assert!(self.start < N, "start out-of-bounds");
        &self.items[self.start]
    }

    #[inline]
    const fn back_maybe_uninit(&self) -> &MaybeUninit<T> {
        debug_assert!(self.size > 0, "empty buffer");
        debug_assert!(self.size <= N, "size out-of-bounds");
        debug_assert!(self.start < N, "start out-of-bounds");
        let back = add_mod(self.start, self.size - 1, N);
        &self.items[back]
    }

    #[inline]
    fn back_maybe_uninit_mut(&mut self) -> &mut MaybeUninit<T> {
        debug_assert!(self.size > 0, "empty buffer");
        debug_assert!(self.size <= N, "size out-of-bounds");
        debug_assert!(self.start < N, "start out-of-bounds");
        let back = add_mod(self.start, self.size - 1, N);
        &mut self.items[back]
    }

    #[inline]
    const fn get_maybe_uninit(&self, index: usize) -> &MaybeUninit<T> {
        debug_assert!(self.size > 0, "empty buffer");
        debug_assert!(index < N, "index out-of-bounds");
        debug_assert!(self.start < N, "start out-of-bounds");
        let index = add_mod(self.start, index, N);
        &self.items[index]
    }

    #[inline]
    fn get_maybe_uninit_mut(&mut self, index: usize) -> &mut MaybeUninit<T> {
        debug_assert!(self.size > 0, "empty buffer");
        debug_assert!(index < N, "index out-of-bounds");
        debug_assert!(self.start < N, "start out-of-bounds");
        let index = add_mod(self.start, index, N);
        &mut self.items[index]
    }

    #[inline]
    fn slices_uninit_mut(&mut self) -> (&mut [MaybeUninit<T>], &mut [MaybeUninit<T>]) {
        if N == 0 {
            return (&mut [][..], &mut [][..]);
        }

        debug_assert!(self.start < N, "start out-of-bounds");
        debug_assert!(self.size <= N, "size out-of-bounds");

        let start = self.start;
        let end = add_mod(start, self.size, N);
        if end < start {
            (&mut self.items[end..start], &mut [][..])
        } else {
            let (left, right) = self.items.split_at_mut(end);
            let left = &mut left[..start];
            (right, left)
        }
    }

    #[inline]
    fn inc_start(&mut self) {
        debug_assert!(self.start < N, "start out-of-bounds");
        self.start = add_mod(self.start, 1, N);
    }

    #[inline]
    fn dec_start(&mut self) {
        debug_assert!(self.start < N, "start out-of-bounds");
        self.start = sub_mod(self.start, 1, N);
    }

    #[inline]
    fn inc_size(&mut self) {
        debug_assert!(self.size <= N, "size out-of-bounds");
        self.size += 1;
        debug_assert!(self.size <= N, "size exceeding capacity");
    }

    #[inline]
    fn dec_size(&mut self) {
        debug_assert!(self.size > 0, "size is 0");
        self.size -= 1;
    }

    #[inline]
    unsafe fn drop_range(&mut self, range: Range<usize>) {
        if range.is_empty() {
            return;
        }

        debug_assert!(self.start < N, "start out-of-bounds");
        debug_assert!(self.size <= N, "size out-of-bounds");
        debug_assert!(range.end <= self.size, "end of range out-of-bounds");
        debug_assert!(range.start == 0 || range.end == self.size,
                      "range does not include boundary of the buffer");

        // Drops all the items in the slice when dropped. This is needed to ensure that all
        // elements are dropped in case a panic occurs during the drop of a single element.
        struct Dropper<'a, T>(&'a mut [MaybeUninit<T>]);

        impl<'a, T> Drop for Dropper<'a, T> {
            #[inline]
            fn drop(&mut self) {
                // SAFETY: the caller of `drop_range` is responsible to check that this slice was
                // initialized.
                #[cfg(feature = "unstable")]
                unsafe { ptr::drop_in_place(MaybeUninit::slice_assume_init_mut(self.0)); }
                #[cfg(not(feature = "unstable"))]
                unsafe { ptr::drop_in_place(&mut *(self.0 as *mut [MaybeUninit<T>] as *mut [T])); }
            }
        }

        let drop_from = add_mod(self.start, range.start, N);
        let drop_to = add_mod(self.start, range.end, N);

        let (right, left) = if drop_from < drop_to {
            (&mut self.items[drop_from..drop_to], &mut [][..])
        } else {
            let (left, right) = self.items.split_at_mut(drop_from);
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
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<4, char>::new();
    /// assert_eq!(buf.back(), None);
    ///
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// buf.push_back('c');
    /// assert_eq!(buf.back(), Some(&'c'));
    /// ```
    #[inline]
    pub fn back(&self) -> Option<&T> {
        if N == 0 || self.size == 0 {
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
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<4, char>::new();
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
        if N == 0 || self.size == 0 {
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
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<4, char>::new();
    /// assert_eq!(buf.front(), None);
    ///
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// buf.push_back('c');
    /// assert_eq!(buf.front(), Some(&'a'));
    /// ```
    #[inline]
    pub fn front(&self) -> Option<&T> {
        if N == 0 || self.size == 0 {
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
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<4, char>::new();
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
        if N == 0 || self.size == 0 {
            // Nothing to do
            return None;
        }
        // SAFETY: `size` is non-zero; front element is guaranteed to be initialized
        Some(unsafe { self.front_maybe_uninit_mut().assume_init_mut() })
    }

    /// Returns a reference to the element at the given index, or `None` if the element does not
    /// exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<4, char>::new();
    /// assert_eq!(buf.get(1), None);
    ///
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// buf.push_back('c');
    /// assert_eq!(buf.get(1), Some(&'b'));
    /// ```
    #[inline]
    pub fn get(&self, index: usize) -> Option<&T> {
        if N == 0 || index >= self.size {
            // Nothing to do
            return None;
        }
        // SAFETY: `index` is in a valid range; it is guaranteed to point to an initialized element
        Some(unsafe { self.get_maybe_uninit(index).assume_init_ref() })
    }

    /// Returns a mutable reference to the element at the given index, or `None` if the element
    /// does not exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<4, char>::new();
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
        if N == 0 || index >= self.size {
            // Nothing to do
            return None;
        }
        // SAFETY: `index` is in a valid range; it is guaranteed to point to an initialized element
        Some(unsafe { self.get_maybe_uninit_mut(index).assume_init_mut() })
    }

    /// Appends an element to the back of the buffer.
    ///
    /// If the buffer is full, the element at the front of the buffer is removed and returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<3, char>::new();
    ///
    /// assert_eq!(buf.push_back('a'), None);      assert_eq!(buf, ['a']);
    /// assert_eq!(buf.push_back('b'), None);      assert_eq!(buf, ['a', 'b']);
    /// assert_eq!(buf.push_back('c'), None);      assert_eq!(buf, ['a', 'b', 'c']);
    /// // The buffer is now full; adding more values causes the front elements to be
    /// // removed and returned
    /// assert_eq!(buf.push_back('d'), Some('a')); assert_eq!(buf, ['b', 'c', 'd']);
    /// assert_eq!(buf.push_back('e'), Some('b')); assert_eq!(buf, ['c', 'd', 'e']);
    /// assert_eq!(buf.push_back('f'), Some('c')); assert_eq!(buf, ['d', 'e', 'f']);
    /// ```
    pub fn push_back(&mut self, item: T) -> Option<T> {
        if N == 0 {
            // Nothing to do
            return Some(item);
        }

        if self.size >= N {
            // At capacity; need to replace the front item
            //
            // SAFETY: if size is greater than 0, the front item is guaranteed to be initialized.
            let replaced_item = mem::replace(
                unsafe { self.front_maybe_uninit_mut().assume_init_mut() },
                item);
            self.inc_start();

            Some(replaced_item)
        } else {
            // Some uninitialized slots left; append at the end
            self.inc_size();
            self.back_maybe_uninit_mut().write(item);

            None
        }
    }

    /// Appends an element to the front of the buffer.
    ///
    /// If the buffer is full, the element at the back of the buffer is removed and returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<3, char>::new();
    ///
    /// assert_eq!(buf.push_front('a'), None);      assert_eq!(buf, ['a']);
    /// assert_eq!(buf.push_front('b'), None);      assert_eq!(buf, ['b', 'a']);
    /// assert_eq!(buf.push_front('c'), None);      assert_eq!(buf, ['c', 'b', 'a']);
    /// // The buffer is now full; adding more values causes the back elements to be
    /// // removed and returned
    /// assert_eq!(buf.push_front('d'), Some('a')); assert_eq!(buf, ['d', 'c', 'b']);
    /// assert_eq!(buf.push_front('e'), Some('b')); assert_eq!(buf, ['e', 'd', 'c']);
    /// assert_eq!(buf.push_front('f'), Some('c')); assert_eq!(buf, ['f', 'e', 'd']);
    /// ```
    pub fn push_front(&mut self, item: T) -> Option<T> {
        if N == 0 {
            // Nothing to do
            return Some(item);
        }

        if self.size >= N {
            // At capacity; need to replace the back item
            //
            // SAFETY: if size is greater than 0, the back item is guaranteed to be initialized.
            let replaced_item = mem::replace(
                unsafe { self.back_maybe_uninit_mut().assume_init_mut() },
                item);
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

    /// Removes and returns an element from the back of the buffer.
    ///
    /// If the buffer is empty, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<3, char>::from(['a', 'b', 'c']);
    ///
    /// assert_eq!(buf.pop_back(), Some('c'));
    /// assert_eq!(buf.pop_back(), Some('b'));
    /// assert_eq!(buf.pop_back(), Some('a'));
    /// assert_eq!(buf.pop_back(), None);
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        if N == 0 || self.size == 0 {
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
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<3, char>::from(['a', 'b', 'c']);
    ///
    /// assert_eq!(buf.pop_front(), Some('a'));
    /// assert_eq!(buf.pop_front(), Some('b'));
    /// assert_eq!(buf.pop_front(), Some('c'));
    /// assert_eq!(buf.pop_front(), None);
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        if N == 0 || self.size == 0 {
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
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<3, char>::from(['a', 'b', 'c']);
    ///
    /// assert_eq!(buf.remove(1), Some('b'));
    /// assert_eq!(buf, ['a', 'c']);
    ///
    /// assert_eq!(buf.remove(5), None);
    /// ```
    pub fn remove(&mut self, index: usize) -> Option<T> {
        if N == 0 || index >= self.size {
            return None;
        }

        let index = add_mod(self.start, index, N);
        let back_index = add_mod(self.start, self.size - 1, N);

        // SAFETY: `index` is in a valid range; the element is guaranteed to be initialized
        let item = unsafe { self.items[index].assume_init_read() };

        // SAFETY: the pointers being moved are in a valid range; the elements behind those
        // pointers are guaranteed to be initialized
        unsafe {
            let ptr = self.items.as_mut_ptr();
            if back_index >= index {
                // Move the values at the right of `index` by 1 position to the left
                ptr::copy(ptr.add(index).add(1), ptr.add(index), back_index - index);
            } else {
                // Move the values at the right of `index` by 1 position to the left
                ptr::copy(ptr.add(index).add(1), ptr.add(index), N - index);
                // Move the leftmost value to the end of the array
                ptr::copy(ptr, ptr.add(N - 1), 1);
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
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<5, char>::from(['a', 'b', 'c', 'd']);
    /// assert_eq!(buf, ['a', 'b', 'c', 'd']);
    ///
    /// buf.swap(0, 3);
    /// assert_eq!(buf, ['d', 'b', 'c', 'a']);
    /// ```
    ///
    /// Trying to swap an invalid index panics:
    ///
    /// ```should_panic
    /// use circular_buffer::CircularBuffer;
    /// let mut buf = CircularBuffer::<5, char>::from(['a', 'b', 'c', 'd']);
    /// buf.swap(0, 7);
    /// ```
    pub fn swap(&mut self, i: usize, j: usize) {
        assert!(i < self.size, "i index out-of-bounds");
        assert!(j < self.size, "j index out-of-bounds");
        if i != j {
            let i = add_mod(self.start, i, N);
            let j = add_mod(self.start, j, N);
            // SAFETY: these are valid pointers
            unsafe { ptr::swap_nonoverlapping(&mut self.items[i], &mut self.items[j], 1) };
        }
    }

    /// Removes the element at `index` and returns it, replacing it with the back of the buffer.
    ///
    /// Returns `None` if `index` is out-of-bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<5, char>::from(['a', 'b', 'c', 'd']);
    /// assert_eq!(buf, ['a', 'b', 'c', 'd']);
    ///
    /// assert_eq!(buf.swap_remove_back(2), Some('c'));
    /// assert_eq!(buf, ['a', 'b', 'd']);
    ///
    /// assert_eq!(buf.swap_remove_back(7), None);
    /// ```
    pub fn swap_remove_back(&mut self, index: usize) -> Option<T> {
        if index >= self.size {
            return None;
        }
        self.swap(index, self.size - 1);
        self.pop_back()
    }

    /// Removes the element at `index` and returns it, replacing it with the front of the buffer.
    ///
    /// Returns `None` if `index` is out-of-bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<5, char>::from(['a', 'b', 'c', 'd']);
    /// assert_eq!(buf, ['a', 'b', 'c', 'd']);
    ///
    /// assert_eq!(buf.swap_remove_front(2), Some('c'));
    /// assert_eq!(buf, ['b', 'a', 'd']);
    ///
    /// assert_eq!(buf.swap_remove_front(7), None);
    /// ```
    pub fn swap_remove_front(&mut self, index: usize) -> Option<T> {
        if index >= self.size {
            return None;
        }
        self.swap(index, 0);
        self.pop_front()
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
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<4, u32>::from([10, 20, 30]);
    ///
    /// buf.truncate_back(1);
    /// assert_eq!(buf, [10]);
    ///
    /// // Truncating to a length that is greater than the buffer's length has no effect
    /// buf.truncate_back(8);
    /// assert_eq!(buf, [10]);
    /// ```
    pub fn truncate_back(&mut self, len: usize) {
        if N == 0 || len >= self.size {
            // Nothing to do
            return;
        }

        let drop_range = len..self.size;
        // SAFETY: `drop_range` is a valid range, so elements within are guaranteed to be
        // initialized. The `size` of the buffer is shrunk before dropping, so no value will be
        // dropped twice in case of panics.
        unsafe { self.drop_range(drop_range) };
        self.size = len;
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
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<4, u32>::from([10, 20, 30]);
    ///
    /// buf.truncate_front(1);
    /// assert_eq!(buf, [30]);
    ///
    /// // Truncating to a length that is greater than the buffer's length has no effect
    /// buf.truncate_front(8);
    /// assert_eq!(buf, [30]);
    /// ```
    pub fn truncate_front(&mut self, len: usize) {
        if N == 0 || len >= self.size {
            // Nothing to do
            return;
        }

        let drop_len = self.size - len;
        let drop_range = 0..drop_len;
        // SAFETY: `drop_range` is a valid range, so elements within are guaranteed to be
        // initialized. The `start` of the buffer is shrunk before dropping, so no value will be
        // dropped twice in case of panics.
        unsafe { self.drop_range(drop_range) };
        self.start = add_mod(self.start, drop_len, N);
        self.size = len;
    }

    /// Drops all the elements in the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::CircularBuffer;
    ///
    /// let mut buf = CircularBuffer::<4, u32>::from([10, 20, 30]);
    /// assert_eq!(buf, [10, 20, 30]);
    /// buf.clear();
    /// assert_eq!(buf, []);
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.truncate_back(0)
    }
}

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
        if N == 0 {
            return;
        }

        debug_assert!(self.start < N, "start out-of-bounds");
        debug_assert!(self.size <= N, "size out-of-bounds");

        #[cfg(not(feature = "unstable"))]
        fn write_uninit_slice_cloned<T: Clone>(dst: &mut [MaybeUninit<T>], src: &[T]) {
            // Each call to `clone()` may panic, therefore we need to track how many elements we
            // successfully cloned so that we can drop them in case of panic. This `Guard` struct
            // does exactly that: it keeps track of how many items have been successfully cloned
            // and drops them if the guard is dropped.
            //
            // This implementation was highly inspired by the implementation of
            // `MaybeUninit::write_slice_cloned`
            struct Guard<'a, T> {
                dst: &'a mut [MaybeUninit<T>],
                initialized: usize,
            }

            impl<'a, T> Drop for Guard<'a, T> {
                fn drop(&mut self) {
                    let initialized = &mut self.dst[..self.initialized];
                    // SAFETY: this slice contain only initialized objects; `MaybeUninit<T>` has
                    // the same alignment and size as `T`
                    unsafe {
                        let initialized = &mut *(initialized as *mut [MaybeUninit<T>] as *mut [T]);
                        ptr::drop_in_place(initialized);
                    }
                }
            }

            debug_assert_eq!(dst.len(), src.len());
            let len = dst.len();
            let mut guard = Guard { dst, initialized: 0 };
            #[allow(clippy::needless_range_loop)]
            for i in 0..len {
                guard.dst[i].write(src[i].clone());
                guard.initialized += 1;
            }

            // All the `clone()` calls succeded; get rid of the guard without running its `drop()`
            // implementation
            mem::forget(guard);
        }

        if other.len() < N {
            // All the elements of `other` fit into the buffer
            let free_size = N - self.size;
            let final_size = if other.len() < free_size {
                // All the elements of `other` fit at the back of the buffer
                self.size + other.len()
            } else {
                // Some of the elements of `other` need to overwrite the front of the buffer
                self.truncate_front(N - other.len());
                N
            };

            let (right, left) = self.slices_uninit_mut();

            let write_len = core::cmp::min(right.len(), other.len());
            #[cfg(feature = "unstable")]
            MaybeUninit::write_slice_cloned(&mut right[..write_len], &other[..write_len]);
            #[cfg(not(feature = "unstable"))]
            write_uninit_slice_cloned(&mut right[..write_len], &other[..write_len]);

            let other = &other[write_len..];
            debug_assert!(left.len() >= other.len());
            let write_len = other.len();
            #[cfg(feature = "unstable")]
            MaybeUninit::write_slice_cloned(&mut left[..write_len], other);
            #[cfg(not(feature = "unstable"))]
            write_uninit_slice_cloned(&mut left[..write_len], other);

            self.size = final_size;
        } else {
            // `other` overwrites the whole buffer; get only the last `N` elements from `other` and
            // overwrite
            self.clear();
            self.start = 0;

            let other = &other[other.len() - N..];
            debug_assert_eq!(self.items.len(), other.len());
            #[cfg(feature = "unstable")]
            MaybeUninit::write_slice_cloned(&mut self.items, other);
            #[cfg(not(feature = "unstable"))]
            write_uninit_slice_cloned(&mut self.items, other);

            self.size = N;
        }
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
        let mut vec = Vec::with_capacity(self.size);
        vec.extend(self.iter().cloned());
        debug_assert_eq!(vec.len(), self.size);
        vec
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

        Self { size, start: 0, items: elems }
    }
}

impl<const N: usize, T> FromIterator<T> for CircularBuffer<N, T> {
    fn from_iter<I>(iter: I) -> Self
        where I: IntoIterator<Item = T>
    {
        // TODO Optimize
        let mut buf = Self::new();
        iter.into_iter().for_each(|item| { buf.push_back(item); });
        buf
    }
}

impl<const N: usize, T> Extend<T> for CircularBuffer<N, T> {
    fn extend<I>(&mut self, iter: I)
        where I: IntoIterator<Item = T>
    {
        // TODO Optimize
        iter.into_iter().for_each(|item| { self.push_back(item); });
    }
}

impl<'a, const N: usize, T> Extend<&'a T> for CircularBuffer<N, T>
    where T: Copy
{
    fn extend<I>(&mut self, iter: I)
        where I: IntoIterator<Item = &'a T>
    {
        // TODO Optimize
        iter.into_iter().for_each(|item| { self.push_back(*item); });
    }
}

unstable_const_impl! {
    impl<{const N: usize, T}> const IntoIterator for CircularBuffer<N, T> {
        type Item = T;
        type IntoIter = IntoIter<N, T>;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            IntoIter::new(self)
        }
    }
}

unstable_const_impl! {
    impl<{'a, const N: usize, T}> const IntoIterator for &'a CircularBuffer<N, T> {
        type Item = &'a T;
        type IntoIter = Iter<'a, T>;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            Iter::new(self)
        }
    }
}

impl<const N: usize, const M: usize, T, U> PartialEq<CircularBuffer<M, U>> for CircularBuffer<N, T>
    where T: PartialEq<U>
{
    fn eq(&self, other: &CircularBuffer<M, U>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        let (a_left, a_right) = self.as_slices();
        let (b_left, b_right) = other.as_slices();

        match a_left.len().cmp(&b_left.len()) {
            Ordering::Less => {
                let x = a_left.len();
                let y = b_left.len() - x;
                a_left[..] == b_left[..x] && a_right[..y] == b_left[x..] && a_right[y..] == b_right[..]
            },
            Ordering::Greater => {
                let x = b_left.len();
                let y = a_left.len() - x;
                a_left[..x] == b_left[..] && a_right[x..] == b_left[..y] && a_right[..] == b_right[y..]
            },
            Ordering::Equal => {
                debug_assert_eq!(a_left.len(), b_left.len());
                debug_assert_eq!(a_right.len(), b_right.len());
                a_left == b_left && a_right == b_right
            },
        }
    }
}

impl<const N: usize, T> Eq for CircularBuffer<N, T> where T: Eq {}

impl<const N: usize, T, U> PartialEq<[U]> for CircularBuffer<N, T>
    where T: PartialEq<U>
{
    fn eq(&self, other: &[U]) -> bool {
        if self.len() != other.len() {
            return false;
        }

        let (a_left, a_right) = self.as_slices();
        let (b_left, b_right) = other.split_at(a_left.len());

        debug_assert_eq!(a_left.len(), b_left.len());
        debug_assert_eq!(a_right.len(), b_right.len());
        a_left == b_left && a_right == b_right
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
        self.iter().partial_cmp(other.iter())
    }
}

impl<const N: usize, T> Ord for CircularBuffer<N, T>
    where T: Ord
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<const N: usize, T> Hash for CircularBuffer<N, T>
    where T: Hash
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.size.hash(state);
        self.iter().for_each(|item| item.hash(state));
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

impl<const N: usize, T> Drop for CircularBuffer<N, T> {
    #[inline]
    fn drop(&mut self) {
        // `clear()` will make sure that every element is dropped in a safe way
        self.clear();
    }
}

impl<const N: usize, T> fmt::Debug for CircularBuffer<N, T>
    where T: fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}
