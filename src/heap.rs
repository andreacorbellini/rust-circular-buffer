// Copyright © 2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

//! Heap-allocated, variable-size circular buffer.

use crate::CircularBuffer;
use crate::Inner;
use crate::Iter;
use crate::IterMut;
use crate::add_mod;
use ::alloc::alloc;
use ::alloc::alloc::Layout;
use ::alloc::alloc::LayoutError;
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
use ::alloc::boxed::Box;

pub use crate::iter::heap::IntoIter;

/// A heap-allocated, variable-size circular buffer.
///
/// A `HeapCircularBuffer` can be allocated at runtime with an arbitrary capacity, similar to a
/// [`Vec`]. The capacity of the buffer can be adjusted using [`resize()`](Self::resize).
///
/// See the [module-level documentation](crate) for more details and examples.
#[repr(transparent)]
pub struct HeapCircularBuffer<T> {
    inner: Box<Inner<[MaybeUninit<T>]>>,
}

impl<T> HeapCircularBuffer<T> {
    #[inline]
    fn layout_for(capacity: usize) -> Layout {
        Self::try_layout_for(capacity).expect("capacity overflow")
    }

    #[inline]
    fn try_layout_for(capacity: usize) -> Result<Layout, LayoutError> {
        Ok(Layout::new::<Inner<()>>()
            .extend(Layout::array::<T>(capacity)?)?
            .0
            .pad_to_align())
    }

    #[inline]
    fn wide_inner_ptr(raw_ptr: *mut u8, capacity: usize) -> *mut Inner<[MaybeUninit<T>]> {
        // `raw_ptr` is a thin-pointer `*mut u8`. We need to convert it to a wide-pointer. We use
        // `slice_from_raw_parts_mut()` for that, which will return a `*mut [u8]`. Here we rely on
        // the implicit assumption that a wide-pointer for `[u8]` is the same as a wide-pointer for
        // `[T]`.
        //
        // TODO: Switch to `ptr::from_raw_parts_mut()` once it's stabilized.
        ptr::slice_from_raw_parts_mut(raw_ptr, capacity) as *mut Inner<[MaybeUninit<T>]>
    }

    /// Returns an empty `HeapCircularBuffer` with the specified capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::HeapCircularBuffer;
    /// let buf = HeapCircularBuffer::<u32>::with_capacity(16);
    /// assert_eq!(buf.capacity(), 16);
    /// assert_eq!(buf.len(), 0);
    /// assert_eq!(buf, []);
    /// ```
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        let layout = Self::layout_for(capacity);
        debug_assert!(layout.size() > 0);

        // SAFETY: `layout` has a non-zero size: even if `capacity` is 0, there are two `usize`
        // fields (`start` and `size`).
        let ptr = unsafe { alloc::alloc(layout) };
        if ptr.is_null() {
            alloc::handle_alloc_error(layout);
        }

        // Convert `ptr` from a `*mut u8` to a `*mut Inner<[MaybeUninit<T>]>`
        let ptr = Self::wide_inner_ptr(ptr, capacity);

        // SAFETY: At this point, `ptr` should point to a memory location that is:
        // - valid for reads and writes;
        // - is properly aligned and sized for `Inner<[MaybeUninit<T>]>` where the slice has the
        //   specified `capacity`.
        let inner = unsafe {
            ptr::addr_of_mut!((*ptr).start).write(0);
            ptr::addr_of_mut!((*ptr).size).write(0);
            Box::from_raw(ptr)
        };

        debug_assert_eq!(layout, Layout::for_value(&*inner));
        debug_assert_eq!(inner.items.len(), capacity);

        Self { inner }
    }

    /// Changes the capacity of the buffer, without changing its elements.
    ///
    /// # Panics
    ///
    /// If `new_capacity` is lower than the number of elements in the buffer.
    ///
    /// # Examples
    ///
    /// Increasing capacity:
    ///
    /// ```
    /// use circular_buffer::HeapCircularBuffer;
    ///
    /// let mut buf = HeapCircularBuffer::<char>::with_capacity(3);
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// buf.push_back('c');
    /// buf.push_back('d');
    /// assert_eq!(buf, ['b', 'c', 'd']);
    ///
    /// buf.resize(5);
    /// buf.push_back('e');
    /// buf.push_back('f');
    /// buf.push_back('g');
    /// assert_eq!(buf, ['c', 'd', 'e', 'f', 'g']);
    /// ```
    ///
    /// Decreasing capacity is fine as long as the new capacity leaves enough room for existing
    /// elements:
    ///
    /// ```
    /// use circular_buffer::HeapCircularBuffer;
    ///
    /// let mut buf = HeapCircularBuffer::<char>::with_capacity(3);
    /// assert_eq!(buf.capacity(), 3);
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// assert_eq!(buf, ['a', 'b']);
    ///
    /// buf.resize(2);
    /// assert_eq!(buf.capacity(), 2);
    /// assert_eq!(buf, ['a', 'b']);
    /// ```
    ///
    /// Decreasing capacity panics if the buffer is too large:
    ///
    /// ```should_panic
    /// use circular_buffer::HeapCircularBuffer;
    ///
    /// let mut buf = HeapCircularBuffer::<char>::with_capacity(3);
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// buf.push_back('c');
    ///
    /// buf.resize(2); // panics
    /// ```
    pub fn resize(&mut self, new_capacity: usize) {
        if new_capacity == self.capacity() {
            // Nothing to do.
            return;
        }

        assert!(
            new_capacity >= self.inner.size,
            "new capacity is lower than the length of the buffer"
        );

        // Ensure that the elements of the buffer are not "wrapping around" the boundary of the
        // memory slice, because that boundary is going to change after the capacity is adjusted.
        let items_start_ptr = self.make_contiguous().as_ptr() as *const MaybeUninit<T>;

        if self.capacity() > 0 {
            // Now that the buffer is contiguous, the elements may still be over the new boundary.
            // We need to check for that condition, and, if necessary, shift the elements back so
            // that they fit within the new boundary.
            let start = self.inner.start;
            let end = add_mod(self.inner.start, self.inner.size, self.capacity());
            debug_assert!(
                start <= end,
                "start index should preceed end index after a call to `make_contiguous()`"
            );

            if end >= new_capacity {
                // The elements exist outside of the new boundary. We need to shift them back.
                //
                // SAFETY: Both the source and destination pointers are valid, properly aligned, and
                // they belong to the same object (`self.inner.items`). Because we're changing
                // `start`, the source items will not be accessible, so effectively we're moving
                // them.
                unsafe { items_start_ptr.copy_to(self.inner.items.as_mut_ptr(), self.inner.size) };
                self.inner.start = 0;
            }
        }

        let old_layout = Layout::for_value(&*self.inner);
        let new_layout = Self::layout_for(new_capacity);
        debug_assert!(new_layout.size() > 0);

        // SAFETY: `read()` is called on a valid memory location that comes from a valid reference.
        // The `Box` is copied, but its copy in `self` is not accessed again, and is later
        // overwritten.
        let old_ptr = Box::into_raw(unsafe { ptr::addr_of!(self.inner).read() }) as *mut u8;

        // SAFETY:
        // - `old_ptr` was allocated via the global allocator;
        // - `old_layout` is the layout for this object;
        // - `new_layout.size()` is greater than 0 (even if `new_capacity` is 0) because there are
        //   two `usize` fields in `Inner`;
        // - `new_layout.size()` does not overflow `isize` after rounding, because it comes from a
        //   `Layout` object, which already provides such guarantees.
        let new_ptr = unsafe { alloc::realloc(old_ptr, old_layout, new_layout.size()) };
        if new_ptr.is_null() {
            alloc::handle_alloc_error(new_layout);
        }

        let new_ptr = Self::wide_inner_ptr(new_ptr, new_capacity);

        // SAFETY: `new_ptr` is valid for reads and writes, is properly aligned, and sized.
        let inner = unsafe { Box::from_raw(new_ptr) };

        debug_assert_eq!(new_layout, Layout::for_value(&*inner));
        debug_assert_eq!(inner.items.len(), new_capacity);

        // SAFETY: `write()` is called on a valid memory location that comes from a valid reference.
        unsafe { ptr::addr_of_mut!(self.inner).write(inner) };
    }

    /// Returns a reference to this buffer.
    pub const fn as_circular_buffer(&self) -> &CircularBuffer<T> {
        // Transmute the inner pointer to a `CircularBuffer<T>`.
        //
        // SAFETY: `CircularBuffer` uses `repr(transparent)`, therefore it has the same layout and
        // representation as `Inner<[MaybeUninit<T>]>`.
        unsafe { mem::transmute(&*self.inner) }
    }

    /// Returns a mutable reference to this buffer.
    pub const fn as_mut_circular_buffer(&mut self) -> &mut CircularBuffer<T> {
        // Transmute the inner pointer to a `CircularBuffer<T>`.
        //
        // SAFETY: `CircularBuffer` uses `repr(transparent)`, therefore it has the same layout and
        // representation as `Inner<[MaybeUninit<T>]>`.
        unsafe { mem::transmute(&mut *self.inner) }
    }

    /// Consumes and leaks the buffer, returning a mutable reference to the contents as a
    /// [`CircularBuffer`].
    ///
    /// Note that the type `T` must outlive the chosen lifetime `'a`. If the type has only static
    /// references, or none at all, then this may be chosen to be `'static`.
    ///
    /// This function is mainly useful for data that lives for the remainder of the program’s life.
    /// Dropping the returned reference will cause a memory leak.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::CircularBuffer;
    /// use circular_buffer::HeapCircularBuffer;
    ///
    /// let mut buf = HeapCircularBuffer::<u32>::with_capacity(5);
    /// buf.extend([1, 2, 3]);
    ///
    /// let static_ref: &'static mut CircularBuffer<u32> = buf.leak();
    /// assert_eq!(static_ref, [1, 2, 3]);
    ///
    /// # // Miri will flag this test as having a memory leak (which is correct: a memory leak is
    /// # // precisely what this test intends to trigger). The following code ensures that
    /// # // destructors are run, so that Miri does not complain.
    /// # let _ = unsafe { Box::from_raw(static_ref) };
    /// ```
    pub fn leak<'a>(self) -> &'a mut CircularBuffer<T>
    where
        T: 'a,
    {
        // Wrap `self` into a `MaybeUninit` to ensure that destructors are not run.
        let buf = MaybeUninit::new(self);
        let buf = buf.as_ptr();

        // SAFETY: `read()` is called on a valid memory location that comes from a valid reference.
        // The `Box` is copied, which is not generally supported, but the call to `mem::forget()`
        // ensures that the `Box` does not exist in two places.
        let ptr = Box::into_raw(unsafe { ptr::addr_of!((*buf).inner).read() });

        // SAFETY: This is a valid pointer (because it comes from a `Box`), and we have exclusive
        // ownership of it (because we have erased all traces of the `Box`).
        let inner: &'a mut Inner<[MaybeUninit<T>]> = unsafe { &mut *ptr };

        // SAFETY: `CircularBuffer<T>` uses `repr(transparent)`, therefore it has the same layout
        // and representation as `Inner<[MaybeUninit<T>]>`.
        unsafe { mem::transmute::<&mut Inner<[MaybeUninit<T>]>, &'a mut CircularBuffer<T>>(inner) }
    }

    /// Converts the `HeapCircularBuffer<T>` into a `Box<CircularBuffer<T>>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use circular_buffer::HeapCircularBuffer;
    ///
    /// let mut buf = HeapCircularBuffer::<u32>::with_capacity(5);
    /// buf.extend([1, 2, 3]);
    ///
    /// let boxed_buf = buf.into_boxed_circular_buffer();
    /// assert_eq!(&*boxed_buf, [1, 2, 3]);
    /// ```
    pub fn into_boxed_circular_buffer(self) -> Box<CircularBuffer<T>> {
        // SAFETY: The pointer is valid because it comes from a reference, and we have exclusive
        // ownership of the memory that is pointed to.
        unsafe { Box::from_raw(self.leak()) }
    }
}

impl<T> Deref for HeapCircularBuffer<T> {
    type Target = CircularBuffer<T>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_circular_buffer()
    }
}

impl<T> DerefMut for HeapCircularBuffer<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_circular_buffer()
    }
}

impl<T> Borrow<CircularBuffer<T>> for HeapCircularBuffer<T> {
    #[inline]
    fn borrow(&self) -> &CircularBuffer<T> {
        self.as_circular_buffer()
    }
}

impl<T> BorrowMut<CircularBuffer<T>> for HeapCircularBuffer<T> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut CircularBuffer<T> {
        self.as_mut_circular_buffer()
    }
}

impl<T> AsRef<CircularBuffer<T>> for HeapCircularBuffer<T> {
    #[inline]
    fn as_ref(&self) -> &CircularBuffer<T> {
        self.as_circular_buffer()
    }
}

impl<T> AsMut<CircularBuffer<T>> for HeapCircularBuffer<T> {
    #[inline]
    fn as_mut(&mut self) -> &mut CircularBuffer<T> {
        self.as_mut_circular_buffer()
    }
}

impl<T> Index<usize> for HeapCircularBuffer<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        self.deref().index(index)
    }
}

impl<T> IndexMut<usize> for HeapCircularBuffer<T> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.deref_mut().index_mut(index)
    }
}

impl<T> IntoIterator for HeapCircularBuffer<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self)
    }
}

impl<'a, T> IntoIterator for &'a HeapCircularBuffer<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self)
    }
}

impl<'a, T> IntoIterator for &'a mut HeapCircularBuffer<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IterMut::new(self)
    }
}

impl<T> Clone for HeapCircularBuffer<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        let (front, back) = self.as_slices();
        let mut clone = Self::with_capacity(self.capacity());
        clone.extend_from_slice(front);
        clone.extend_from_slice(back);
        clone
    }

    fn clone_from(&mut self, other: &Self) {
        let (front, back) = other.as_slices();
        self.clear();
        self.resize(other.capacity());
        self.extend_from_slice(front);
        self.extend_from_slice(back);
    }
}

impl<T> Drop for HeapCircularBuffer<T> {
    #[inline]
    fn drop(&mut self) {
        // `clear()` will make sure that every element is dropped in a safe way
        self.clear();
    }
}
