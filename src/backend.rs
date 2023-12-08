use core::cmp::Ordering;
use core::ops::RangeBounds;
use core::ptr;
use core::{fmt, ops::Range};
use core::mem::MaybeUninit;
use core::hash::{Hash, Hasher};

use crate::{add_mod, slice_assume_init_ref, slice_assume_init_mut, sub_mod};
use crate::iter::{Iter, IterMut, IntoIter};
use crate::drain::Drain;

pub(crate) struct Backend<T, B>
    where B: AsSlice<Item = MaybeUninit<T>>
{
    pub(crate) size: usize,
    pub(crate) start: usize,
    pub(crate) items: B,
}

impl <T, B> Backend<T, B>
    where B: AsSlice<Item = MaybeUninit<T>>
{
    pub(crate) const  fn new(items: B) -> Self {
        Self { size: 0, start: 0, items }
    }

    #[inline]
    pub(crate) const fn len(&self) -> usize {
        self.size
    }

    #[inline]
    pub(crate) fn capacity(&self) -> usize {
        // TODO: this can be const once const fn in traits are stable
        self.items.as_slice().len()
    }

    #[inline]
    pub(crate) const fn is_empty(&self) -> bool {
        self.size == 0
    }

    #[inline]
    #[must_use]
    pub(crate) fn iter(&self) -> Iter<'_, T> {
        Iter::new(self)
    }

    #[inline]
    #[must_use]
    pub(crate) fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut::new(self)
    }

    #[inline]
    pub(crate) fn as_slices(&self) -> (&[T], &[T]) {
        if self.capacity() == 0 || self.size == 0 {
            return (&[], &[]);
        }

        debug_assert!(self.start < self.capacity(), "start out-of-bounds");
        debug_assert!(self.size <= self.capacity(), "size out-of-bounds");

        let start = self.start;
        let end = add_mod(self.start, self.size, self.capacity());

        let (front, back) = if start < end {
            (&self.items.as_slice()[start..end], &[][..])
        } else {
            let (back, front) = self.items.as_slice().split_at(start);
            (front, &back[..end])
        };

        // SAFETY: The elements in these slices are guaranteed to be initialized
        unsafe {
            (slice_assume_init_ref(front), slice_assume_init_ref(back))
        }
    }

    #[inline]
    pub(crate) fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
        if self.capacity() == 0 || self.size == 0 {
            return (&mut [][..], &mut [][..]);
        }

        debug_assert!(self.start < self.capacity(), "start out-of-bounds");
        debug_assert!(self.size <= self.capacity(), "size out-of-bounds");

        let start = self.start;
        let end = add_mod(self.start, self.size, self.capacity());

        let (front, back) = if start < end {
            (&mut self.items.as_slice_mut()[start..end], &mut [][..])
        } else {
            let (back, front) = self.items.as_slice_mut().split_at_mut(start);
            (front, &mut back[..end])
        };

        // SAFETY: The elements in these slices are guaranteed to be initialized
        unsafe {
            (slice_assume_init_mut(front), slice_assume_init_mut(back))
        }
    }

    #[inline]
    #[must_use]
    pub(crate) fn range<R>(&self, range: R) -> Iter<'_, T>
        where R: RangeBounds<usize>
    {
        Iter::over_range(self, range)
    }

    #[inline]
    #[must_use]
    pub(crate) fn range_mut<R>(&mut self, range: R) -> IterMut<'_, T>
        where R: RangeBounds<usize>
    {
        IterMut::over_range(self, range)
    }

    #[inline]
    #[must_use]
    pub(crate) fn drain<R>(&mut self, range: R) -> Drain<'_, T, B>
        where R: RangeBounds<usize>
    {
        Drain::over_range(self, range)
    }

    pub(crate) fn make_contiguous(&mut self) -> &mut [T] {
        if self.capacity() == 0 || self.size == 0 {
            return &mut []
        }

        debug_assert!(self.start < self.capacity(), "start out-of-bounds");
        debug_assert!(self.size <= self.capacity(), "size out-of-bounds");

        let start = self.start;
        let end = add_mod(self.start, self.size, self.capacity());

        let slice = if start < end {
            // Already contiguous; nothing to do
            &mut self.items.as_slice_mut()[start..end]
        } else {
            // Not contiguous; need to rotate
            self.start = 0;
            self.items.as_slice_mut().rotate_left(start);
            &mut self.items.as_slice_mut()[..self.size]
        };

        // SAFETY: The elements in the slice are guaranteed to be initialized
        unsafe { slice_assume_init_mut(slice) }
    }

    #[inline]
    pub(crate) fn back(&self) -> Option<&T> {
        if self.capacity() == 0 || self.size == 0 {
            // Nothing to do
            return None;
        }
        // SAFETY: `size` is non-zero; back element is guaranteed to be initialized
        Some(unsafe { self.back_maybe_uninit().assume_init_ref() })
    }

    #[inline]
    pub(crate) fn back_mut(&mut self) -> Option<&mut T> {
        if self.capacity() == 0 || self.size == 0 {
            // Nothing to do
            return None;
        }
        // SAFETY: `size` is non-zero; back element is guaranteed to be initialized
        Some(unsafe { self.back_maybe_uninit_mut().assume_init_mut() })
    }

    #[inline]
    pub(crate) fn front(&self) -> Option<&T> {
        if self.capacity() == 0 || self.size == 0 {
            // Nothing to do
            return None;
        }
        // SAFETY: `size` is non-zero; front element is guaranteed to be initialized
        Some(unsafe { self.front_maybe_uninit().assume_init_ref() })
    }

    #[inline]
    pub(crate) fn front_mut(&mut self) -> Option<&mut T> {
        if self.capacity() == 0 || self.size == 0 {
            // Nothing to do
            return None;
        }
        // SAFETY: `size` is non-zero; front element is guaranteed to be initialized
        Some(unsafe { self.front_maybe_uninit_mut().assume_init_mut() })
    }

    #[inline]
    pub(crate) fn get(&self, index: usize) -> Option<&T> {
        if self.capacity() == 0 || index >= self.size {
            // Nothing to do
            return None;
        }
        // SAFETY: `index` is in a valid range; it is guaranteed to point to an initialized element
        Some(unsafe { self.get_maybe_uninit(index).assume_init_ref() })
    }

    #[inline]
    pub(crate) fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if self.capacity() == 0 || index >= self.size {
            // Nothing to do
            return None;
        }
        // SAFETY: `index` is in a valid range; it is guaranteed to point to an initialized element
        Some(unsafe { self.get_maybe_uninit_mut(index).assume_init_mut() })
    }

    pub(crate) fn push_back(&mut self, item: T) {
        if self.capacity() == 0 {
            // Nothing to do
            return;
        }
        if self.size >= self.capacity() {
            // At capacity; need to replace the front item
            //
            // SAFETY: if size is greater than 0, the front item is guaranteed to be initialized.
            unsafe { ptr::drop_in_place(self.front_maybe_uninit_mut().as_mut_ptr()); }
            self.front_maybe_uninit_mut().write(item);
            self.inc_start();
        } else {
            // Some uninitialized slots left; append at the end
            self.inc_size();
            self.back_maybe_uninit_mut().write(item);
        }
    }

    pub(crate) fn try_push_back(&mut self, item: T) -> Result<(), T> {
        if self.capacity() == 0 {
            // Nothing to do
            return Ok(());
        }
        if self.size >= self.capacity(){
            // At capacity; return the pushed item as error
            Err(item)
        } else {
            // Some uninitialized slots left; append at the end
            self.inc_size();
            self.back_maybe_uninit_mut().write(item);
            Ok(())
        }
    }

    pub(crate) fn push_front(&mut self, item: T) {
        if self.capacity() == 0 {
            // Nothing to do
            return;
        }
        if self.size >= self.capacity() {
            // At capacity; need to replace the back item
            //
            // SAFETY: if size is greater than 0, the front item is guaranteed to be initialized.
            unsafe { ptr::drop_in_place(self.back_maybe_uninit_mut().as_mut_ptr()); }
            self.back_maybe_uninit_mut().write(item);
            self.dec_start();
        } else {
            // Some uninitialized slots left; insert at the start
            self.inc_size();
            self.dec_start();
            self.front_maybe_uninit_mut().write(item);
        }
    }

    pub(crate) fn try_push_front(&mut self, item: T) -> Result<(), T> {
        if self.capacity() == 0 {
            // Nothing to do
            return Ok(());
        }
        if self.size >= self.capacity() {
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

    pub(crate) fn pop_back(&mut self) -> Option<T> {
        if self.capacity() == 0 || self.size == 0 {
            // Nothing to do
            return None;
        }

        // SAFETY: if size is greater than 0, the back item is guaranteed to be initialized.
        let back = unsafe { self.back_maybe_uninit().assume_init_read() };
        self.dec_size();
        Some(back)
    }

    pub(crate) fn pop_front(&mut self) -> Option<T> {
        if self.capacity() == 0 || self.size == 0 {
            // Nothing to do
            return None;
        }

        // SAFETY: if size is greater than 0, the front item is guaranteed to be initialized.
        let back = unsafe { self.front_maybe_uninit().assume_init_read() };
        self.dec_size();
        self.inc_start();
        Some(back)
    }

    pub(crate) fn remove(&mut self, index: usize) -> Option<T> {
        if self.capacity() == 0 || index >= self.size {
            return None;
        }

        let index = add_mod(self.start, index, self.capacity());
        let back_index = add_mod(self.start, self.size - 1, self.capacity());

        // SAFETY: `index` is in a valid range; the element is guaranteed to be initialized
        let item = unsafe { self.items.as_slice()[index].assume_init_read() };

        // SAFETY: the pointers being moved are in a valid range; the elements behind those
        // pointers are guaranteed to be initialized
        unsafe {
            // TODO: optimize for the case where `index < len - index` (i.e. when copying items to
            // the right is cheaper than moving items to the left)
            let ptr = self.items.as_slice_mut().as_mut_ptr();
            if back_index >= index {
                // Move the values at the right of `index` by 1 position to the left
                ptr::copy(ptr.add(index).add(1), ptr.add(index), back_index - index);
            } else {
                // Move the values at the right of `index` by 1 position to the left
                ptr::copy(ptr.add(index).add(1), ptr.add(index), self.capacity() - index);
                // Move the leftmost value to the end of the array
                ptr::copy(ptr, ptr.add(self.capacity() - 1), 1);
                // Move the values at the left of `back_index` by 1 position to the left
                ptr::copy(ptr.add(1), ptr, back_index);
            }
        }

        self.dec_size();
        Some(item)
    }

    pub(crate) fn swap(&mut self, i: usize, j: usize) {
        assert!(i < self.size, "i index out-of-bounds");
        assert!(j < self.size, "j index out-of-bounds");
        if i != j {
            let i = add_mod(self.start, i, self.capacity());
            let j = add_mod(self.start, j, self.capacity());

            let items = self.items.as_slice_mut();
            // SAFETY: these are valid pointers
            unsafe { ptr::swap_nonoverlapping(&mut items[i], &mut items[j], 1) };
        }
    }

    pub(crate) fn swap_remove_back(&mut self, index: usize) -> Option<T> {
        if index >= self.size {
            return None;
        }
        self.swap(index, self.size - 1);
        self.pop_back()
    }

    pub(crate) fn swap_remove_front(&mut self, index: usize) -> Option<T> {
        if index >= self.size {
            return None;
        }
        self.swap(index, 0);
        self.pop_front()
    }

    pub(crate) fn truncate_back(&mut self, len: usize) {
        if self.capacity() == 0 || len >= self.size {
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

    pub(crate) fn truncate_front(&mut self, len: usize) {
        if self.capacity() == 0 || len >= self.size {
            // Nothing to do
            return;
        }

        let drop_len = self.size - len;
        let drop_range = 0..drop_len;
        // SAFETY: `drop_range` is a valid range, so elements within are guaranteed to be
        // initialized. The `start` of the buffer is shrunk before dropping, so no value will be
        // dropped twice in case of panics.
        unsafe { self.drop_range(drop_range) };
        self.start = add_mod(self.start, drop_len, self.capacity());
        self.size = len;
    }

    #[inline]
    pub(crate) fn clear(&mut self) {
        self.truncate_back(0)
    }

    #[inline]
    fn front_maybe_uninit_mut(&mut self) -> &mut MaybeUninit<T> {
        debug_assert!(self.size > 0, "empty buffer");
        debug_assert!(self.start < self.capacity(), "start out-of-bounds");
        &mut self.items.as_slice_mut()[self.start]
    }

    #[inline]
    fn front_maybe_uninit(&self) -> &MaybeUninit<T> {
        debug_assert!(self.size > 0, "empty buffer");
        debug_assert!(self.size <= self.capacity(), "size out-of-bounds");
        debug_assert!(self.start < self.capacity(), "start out-of-bounds");
        &self.items.as_slice()[self.start]
    }

    #[inline]
    fn back_maybe_uninit(&self) -> &MaybeUninit<T> {
        debug_assert!(self.size > 0, "empty buffer");
        debug_assert!(self.size <= self.capacity(), "size out-of-bounds");
        debug_assert!(self.start < self.capacity(), "start out-of-bounds");
        let back = add_mod(self.start, self.size - 1, self.capacity());
        &self.items.as_slice()[back]
    }

    #[inline]
    fn back_maybe_uninit_mut(&mut self) -> &mut MaybeUninit<T> {
        debug_assert!(self.size > 0, "empty buffer");
        debug_assert!(self.size <= self.capacity(), "size out-of-bounds");
        debug_assert!(self.start < self.capacity(), "start out-of-bounds");
        let back = add_mod(self.start, self.size - 1, self.capacity());
        &mut self.items.as_slice_mut()[back]
    }

    #[inline]
    fn get_maybe_uninit(&self, index: usize) -> &MaybeUninit<T> {
        debug_assert!(self.size > 0, "empty buffer");
        debug_assert!(index < self.capacity(), "index out-of-bounds");
        debug_assert!(self.start < self.capacity(), "start out-of-bounds");
        let index = add_mod(self.start, index, self.capacity());
        &self.items.as_slice()[index]
    }

    #[inline]
    fn get_maybe_uninit_mut(&mut self, index: usize) -> &mut MaybeUninit<T> {
        debug_assert!(self.size > 0, "empty buffer");
        debug_assert!(index < self.capacity(), "index out-of-bounds");
        debug_assert!(self.start < self.capacity(), "start out-of-bounds");
        let index = add_mod(self.start, index, self.capacity());
        &mut self.items.as_slice_mut()[index]
    }

    #[inline]
    fn slices_uninit_mut(&mut self) -> (&mut [MaybeUninit<T>], &mut [MaybeUninit<T>]) {
        if self.capacity() == 0 {
            return (&mut [][..], &mut [][..]);
        }

        debug_assert!(self.start < self.capacity(), "start out-of-bounds");
        debug_assert!(self.size <= self.capacity(), "size out-of-bounds");

        let start = self.start;
        let end = add_mod(start, self.size, self.capacity());
        if end < start {
            (&mut self.items.as_slice_mut()[end..start], &mut [][..])
        } else {
            let (left, right) = self.items.as_slice_mut().split_at_mut(end);
            let left = &mut left[..start];
            (right, left)
        }
    }

    #[inline]
    fn inc_start(&mut self) {
        debug_assert!(self.start < self.capacity(), "start out-of-bounds");
        self.start = add_mod(self.start, 1, self.capacity());
    }

    #[inline]
    fn dec_start(&mut self) {
        debug_assert!(self.start < self.capacity(), "start out-of-bounds");
        self.start = sub_mod(self.start, 1, self.capacity());
    }

    #[inline]
    fn inc_size(&mut self) {
        debug_assert!(self.size <= self.capacity(), "size out-of-bounds");
        debug_assert!(self.size < self.capacity(), "size at capacity limit");
        self.size += 1;
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

        debug_assert!(self.start < self.capacity(), "start out-of-bounds");
        debug_assert!(self.size <= self.capacity(), "size out-of-bounds");
        debug_assert!(range.start < self.size, "start of range out-of-bounds");
        debug_assert!(range.end <= self.size, "end of range out-of-bounds");
        debug_assert!(range.start < range.end, "start of range is past its end");
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
                unsafe { ptr::drop_in_place(slice_assume_init_mut(self.0)); }
            }
        }

        let drop_from = add_mod(self.start, range.start, self.capacity());
        let drop_to = add_mod(self.start, range.end, self.capacity());

        let (right, left) = if drop_from < drop_to {
            (&mut self.items.as_slice_mut()[drop_from..drop_to], &mut [][..])
        } else {
            let (left, right) = self.items.as_slice_mut().split_at_mut(drop_from);
            let left = &mut left[..drop_to];
            (right, left)
        };

        let _left = Dropper(left);
        let _right = Dropper(right);
    }
}

impl <T, B> Backend<T, B>
    where
        T: Clone,
        B: AsSlice<Item = MaybeUninit<T>>
{
    pub(crate) fn extend_from_slice(&mut self, other: &[T]) {
        if self.capacity() == 0 {
            return;
        }

        debug_assert!(self.start < self.capacity(), "start out-of-bounds");
        debug_assert!(self.size <= self.capacity(), "size out-of-bounds");

        #[cfg(not(feature = "unstable"))]
        fn write_uninit_slice_cloned<T: Clone>(dst: &mut [MaybeUninit<T>], src: &[T]) {
            use core::mem;

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

        if other.len() < self.capacity() {
            // All the elements of `other` fit into the buffer
            let free_size = self.capacity() - self.size;
            let final_size = if other.len() < free_size {
                // All the elements of `other` fit at the back of the buffer
                self.size + other.len()
            } else {
                // Some of the elements of `other` need to overwrite the front of the buffer
                self.truncate_front(self.capacity() - other.len());
                self.capacity()
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

            let other = &other[other.len() - self.capacity()..];
            debug_assert_eq!(self.items.as_slice().len(), other.len());
            #[cfg(feature = "unstable")]
            MaybeUninit::write_slice_cloned(self.items.as_slice_mut(), other);
            #[cfg(not(feature = "unstable"))]
            write_uninit_slice_cloned(self.items.as_slice_mut(), other);

            self.size = self.capacity();
        }
    }

    #[must_use]
    #[cfg(feature = "use_std")]
    pub(crate) fn to_vec(&self) -> Vec<T> {
        let mut vec = Vec::with_capacity(self.size);
        vec.extend(self.iter().cloned());
        debug_assert_eq!(vec.len(), self.size);
        vec
    }
}

impl<T, B> Extend<T> for Backend<T, B>
    where B: AsSlice<Item = MaybeUninit<T>>,
{
    fn extend<I>(&mut self, iter: I)
        where I: IntoIterator<Item = T>
    {
        // TODO Optimize
        iter.into_iter().for_each(|item| self.push_back(item));
    }
}

impl<'a, T, B> Extend<&'a T> for Backend<T, B>
    where
        T: Copy,
        B: AsSlice<Item = MaybeUninit<T>>
{
    fn extend<I>(&mut self, iter: I)
        where I: IntoIterator<Item = &'a T>
    {
        // TODO Optimize
        iter.into_iter().for_each(|item| self.push_back(*item));
    }
}

// TODO const impl?
impl<T, B> IntoIterator for Backend<T, B>
    where B: AsSlice<Item = MaybeUninit<T>>,
{
    type Item = T;
    type IntoIter = IntoIter<T, B>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self)
    }
}

// TODO const impl?
impl<'a, T: 'a, B> IntoIterator for &'a Backend<T, B>
    where B: AsSlice<Item = MaybeUninit<T>>,
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self)
    }
}

impl<T, U, B1, B2> PartialEq<Backend<U, B2>> for Backend<T, B1>
    where
        T: PartialEq<U>,
        B1: AsSlice<Item = MaybeUninit<T>>,
        B2: AsSlice<Item = MaybeUninit<U>>,
{
    fn eq(&self, other: &Backend<U, B2>) -> bool {
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
                a_left[..x] == b_left[..] && a_left[x..] == b_right[..y] && a_right[..] == b_right[y..]
            },
            Ordering::Equal => {
                debug_assert_eq!(a_left.len(), b_left.len());
                debug_assert_eq!(a_right.len(), b_right.len());
                a_left == b_left && a_right == b_right
            },
        }
    }
}

impl<T, U, B> PartialEq<[U]> for Backend<T, B>
    where
        T: PartialEq<U>,
        B: AsSlice<Item = MaybeUninit<T>>,
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


impl<T, B> Eq for Backend<T, B>
    where
        T: Eq,
        B: AsSlice<Item = MaybeUninit<T>>
{}

impl<T, U, B1, B2> PartialOrd<Backend<U, B2>> for Backend<T, B1>
    where
        T: PartialOrd<U>,
        B1: AsSlice<Item = MaybeUninit<T>>,
        B2: AsSlice<Item = MaybeUninit<U>>,
{
    fn partial_cmp(&self, other: &Backend<U, B2>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T, B> Ord for Backend<T, B>
    where
        T: Ord,
        B: AsSlice<Item = MaybeUninit<T>>
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T, B> Hash for Backend<T, B>
    where
        T: Hash,
        B: AsSlice<Item = MaybeUninit<T>>
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.size.hash(state);
        self.iter().for_each(|item| item.hash(state));
    }
}

impl<T, B> Drop for Backend<T, B>
    where B: AsSlice<Item = MaybeUninit<T>>
{
    #[inline]
    fn drop(&mut self) {
        // `clear()` will make sure that every element is dropped in a safe way
        self.clear();
    }
}

impl<T, B> fmt::Debug for Backend<T, B>
    where
        T: fmt::Debug,
        B: AsSlice<Item = MaybeUninit<T>>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

pub(crate) trait AsSlice {
    type Item;
    fn as_slice(&self)-> &[Self::Item];
    fn as_slice_mut(&mut self) -> &mut [Self::Item];
}

impl<const N: usize, T> AsSlice for [MaybeUninit<T>; N] {
    type Item = MaybeUninit<T>;
    fn as_slice(&self)-> &[Self::Item] {
        &self[..]
    }
    fn as_slice_mut(&mut self) -> &mut [Self::Item] {
        &mut self[..]
    }
}

impl<T> AsSlice for Box<[MaybeUninit<T>]> {
    type Item = MaybeUninit<T>;
    fn as_slice(&self)-> &[Self::Item] {
        &self[..]
    }
    fn as_slice_mut(&mut self) -> &mut [Self::Item] {
        &mut self[..]
    }
}