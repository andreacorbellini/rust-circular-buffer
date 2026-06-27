// Copyright © 2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

use crate::CircularBuffer;
use crate::Inner;
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
        assert!(
            new_capacity >= self.len(),
            "new capacity is lower than the length of the buffer"
        );

        self.make_contiguous();

        let old_layout = Layout::for_value(&*self.inner);
        let new_layout = Self::layout_for(new_capacity);
        debug_assert!(new_layout.size() > 0);

        // SAFETY: `read()` is called on a valid memory location that comes from a valid reference.
        let old_ptr = Box::into_raw(unsafe { ptr::addr_of_mut!(self.inner).read() }) as *mut u8;

        // SAFETY:
        // - `old_ptr` was allocated via the global allocator;
        // - `old_layout` is the layout for this object;
        // - `new_layout.size()` is greater than 0 (even if `new_capacity` is 0) because there are
        //   two `usize` fields in `Inner`;
        // - `new_layout.size()` does not overflow `isize` after rounding, because it comes from a
        //   `Layout` object, which already provides such guarantees.
        let new_ptr = unsafe { alloc::realloc(old_ptr, old_layout, new_layout.size()) };

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
