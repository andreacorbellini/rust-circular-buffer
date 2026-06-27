// Copyright © 2023-2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

//! Fixed-size circular buffer.

use crate::CircularBuffer;
use crate::Inner;
use crate::Iter;
use crate::IterMut;
use core::borrow::Borrow;
use core::borrow::BorrowMut;
use core::mem;
use core::mem::MaybeUninit;
use core::ops::Deref;
use core::ops::DerefMut;
use core::ops::Index;
use core::ops::IndexMut;
use core::ptr;

#[cfg(all(not(feature = "std"), feature = "alloc"))]
use alloc::boxed::Box;

pub use crate::iter::fixed::IntoIter;

/// A fixed-size circular buffer.
///
/// A `FixedCircularBuffer` has a fixed capacity that is specified at compile-time, similar to an
/// [`array`]. It may live on the stack or be initialized in `const` contexts.
///
/// Wrap the `FixedCircularBuffer` in a [`Box`](std::boxed) using [`FixedCircularBuffer::boxed()`]
/// if you need the struct to be heap-allocated. Consider using
/// [`HeapCircularBuffer`](crate::HeapCircularBuffer) if the capacity cannot be specified at
/// compile-time.
///
/// See the [module-level documentation](crate) for more details and examples.
#[repr(transparent)]
pub struct FixedCircularBuffer<T, const N: usize> {
    inner: Inner<[MaybeUninit<T>; N]>,
}

impl<T, const N: usize> FixedCircularBuffer<T, N> {
    /// Returns an empty `FixedCircularBuffer`.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    /// let buf = FixedCircularBuffer::<u32, 16>::new();
    /// assert_eq!(buf.capacity(), 16);
    /// assert_eq!(buf.len(), 0);
    /// assert_eq!(buf, []);
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            inner: Inner {
                size: 0,
                start: 0,
                items: [const { MaybeUninit::uninit() }; N],
            },
        }
    }

    /// Returns an empty heap-allocated `FixedCircularBuffer`.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::FixedCircularBuffer;
    /// let buf = FixedCircularBuffer::<f64, 1024>::boxed();
    /// assert_eq!(buf.len(), 0);
    /// ```
    #[must_use]
    #[cfg(feature = "alloc")]
    pub fn boxed() -> Box<Self> {
        let mut uninit: Box<MaybeUninit<Self>> = Box::new_uninit();
        let ptr = uninit.as_mut_ptr();

        // SAFETY: the pointer contains enough memory to contain `Self` and `addr_of_mut` ensures
        // that the address written to is properly aligned.
        unsafe {
            core::ptr::addr_of_mut!((*ptr).inner.size).write(0);
            core::ptr::addr_of_mut!((*ptr).inner.start).write(0);
        }

        // SAFETY: `size` and `start` have been properly initialized to 0; `items` does not need to
        // be initialized if `size` is 0
        unsafe { uninit.assume_init() }
    }

    /// Returns a reference to this buffer.
    pub const fn as_circular_buffer(&self) -> &CircularBuffer<T> {
        // Mutate `&self.inner` from a thin-pointer of type `Inner<[X; N]>` to a fat-pointer of type
        // `Inner<[X]>`.
        let inner_unsized: &Inner<[MaybeUninit<T>]> = &self.inner;
        // Transmute the fat-pointer to a `CircularBuffer<T>`.
        //
        // SAFETY: `CircularBuffer` uses `repr(transparent)`, therefore it has the same layout and
        // representation as `Inner<[MaybeUninit<T>]>`.
        unsafe { mem::transmute(inner_unsized) }
    }

    /// Returns a mutable reference to this buffer.
    pub const fn as_mut_circular_buffer(&mut self) -> &mut CircularBuffer<T> {
        // Mutate `&mut self.inner` from a thin-pointer of type `Inner<[X; N]>` to a fat-pointer of
        // type `Inner<[X]>`.
        let inner_unsized: &mut Inner<[MaybeUninit<T>]> = &mut self.inner;
        // Transmute the fat-pointer to a `CircularBuffer<T>`.
        //
        // SAFETY: `CircularBuffer` uses `repr(transparent)`, therefore it has the same layout and
        // representation as `Inner<[MaybeUninit<T>]>`.
        unsafe { mem::transmute(inner_unsized) }
    }
}

impl<T, const N: usize> Default for FixedCircularBuffer<T, N> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize, const M: usize, T> From<[T; M]> for FixedCircularBuffer<T, N> {
    fn from(mut arr: [T; M]) -> Self {
        let mut elems = [const { MaybeUninit::uninit() }; N];
        let arr_ptr = &arr as *const T as *const MaybeUninit<T>;
        let elems_ptr = &mut elems as *mut MaybeUninit<T>;
        let size = if N >= M { M } else { N };

        // SAFETY:
        // - `M - size` is non-negative, and `arr_ptr.add(M - size)` points to a memory location
        //   that contains exactly `size` elements
        // - `elems_ptr` points to a memory location that contains exactly `N` elements, and `N` is
        //   greater than or equal to `size`
        unsafe {
            ptr::copy_nonoverlapping(arr_ptr.add(M - size), elems_ptr, size);
        }

        // Prevent destructors from running on those elements that we've taken ownership of; only
        // destroy the elements that were discareded
        //
        // SAFETY: All elements in `arr` are initialized; `forget` will make sure that destructors
        // are not run twice
        unsafe {
            ptr::drop_in_place(&mut arr[..M - size]);
        }
        mem::forget(arr);

        Self {
            inner: Inner {
                size,
                start: 0,
                items: elems,
            },
        }
    }
}

impl<T, const N: usize> FromIterator<T> for FixedCircularBuffer<T, N> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        // TODO Optimize
        let mut buf = Self::new();
        iter.into_iter().for_each(|item| {
            buf.push_back(item);
        });
        buf
    }
}

impl<T, const N: usize> Deref for FixedCircularBuffer<T, N> {
    type Target = CircularBuffer<T>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_circular_buffer()
    }
}

impl<T, const N: usize> DerefMut for FixedCircularBuffer<T, N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_circular_buffer()
    }
}

impl<T, const N: usize> Borrow<CircularBuffer<T>> for FixedCircularBuffer<T, N> {
    #[inline]
    fn borrow(&self) -> &CircularBuffer<T> {
        self.as_circular_buffer()
    }
}

impl<T, const N: usize> BorrowMut<CircularBuffer<T>> for FixedCircularBuffer<T, N> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut CircularBuffer<T> {
        self.as_mut_circular_buffer()
    }
}

impl<T, const N: usize> AsRef<CircularBuffer<T>> for FixedCircularBuffer<T, N> {
    #[inline]
    fn as_ref(&self) -> &CircularBuffer<T> {
        self.as_circular_buffer()
    }
}

impl<T, const N: usize> AsMut<CircularBuffer<T>> for FixedCircularBuffer<T, N> {
    #[inline]
    fn as_mut(&mut self) -> &mut CircularBuffer<T> {
        self.as_mut_circular_buffer()
    }
}

impl<T, const N: usize> Extend<T> for FixedCircularBuffer<T, N> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        self.deref_mut().extend(iter);
    }
}

impl<'a, T, const N: usize> Extend<&'a T> for FixedCircularBuffer<T, N>
where
    T: Copy,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'a T>,
    {
        self.deref_mut().extend(iter);
    }
}

impl<T, const N: usize> Index<usize> for FixedCircularBuffer<T, N> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        self.deref().index(index)
    }
}

impl<T, const N: usize> IndexMut<usize> for FixedCircularBuffer<T, N> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.deref_mut().index_mut(index)
    }
}

impl<T, const N: usize> IntoIterator for FixedCircularBuffer<T, N> {
    type Item = T;
    type IntoIter = IntoIter<T, N>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self)
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a FixedCircularBuffer<T, N> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self)
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a mut FixedCircularBuffer<T, N> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IterMut::new(self)
    }
}

impl<T, const N: usize> Clone for FixedCircularBuffer<T, N>
where
    T: Clone,
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

impl<T, const N: usize> Drop for FixedCircularBuffer<T, N> {
    #[inline]
    fn drop(&mut self) {
        // `clear()` will make sure that every element is dropped in a safe way
        self.clear();
    }
}
