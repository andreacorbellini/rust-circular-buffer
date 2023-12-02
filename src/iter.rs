use core::fmt;
use core::iter::FusedIterator;
use core::mem::MaybeUninit;
use core::ops::Bound;
use core::ops::RangeBounds;
use crate::backend::AsSlice;
use crate::backend::Backend;

/// An owning [iterator](std::iter::Iterator) over the elements of a [`CircularBuffer`] or [`HeapCircularBuffer`].
///
/// This yields the elements of a `CircularBuffer` from fron to back.
///
/// This struct is created when iterating over a `CircularBuffer`. See the documentation for
/// [`IntoIterator`] for more details.
/// 
/// [`CircularBuffer`]: crate::CircularBuffer
/// [`HeapCircularBuffer`]: crate::heap::HeapCircularBuffer
pub(crate) struct IntoIter<T, B>
    where B: AsSlice<Item = MaybeUninit<T>>
{
    inner: Backend<T, B>,
}

impl<const N: usize, T> Clone for IntoIter<T, [MaybeUninit<T>; N]>
    where T: Clone,
{
    fn clone(&self) -> Self {
        use crate::CircularBuffer;
        let buf = CircularBuffer::from_iter(self.inner.iter().cloned());
        Self { inner: buf.into_backend() }
    }

    fn clone_from(&mut self, other: &Self) {
        self.inner.clear();
        self.inner.extend(other.inner.iter().cloned());
    }
}

impl<T> Clone for IntoIter<T, Box<[MaybeUninit<T>]>>
    where T: Clone,
{
    fn clone(&self) -> Self {
        use crate::heap::HeapCircularBuffer;
        let mut buf = HeapCircularBuffer::with_capacity(self.inner.capacity());
        buf.extend(self.inner.iter().cloned());
        Self { inner: buf.into_backend() }
    }

    fn clone_from(&mut self, other: &Self) {
        self.inner.clear();
        self.inner.extend(other.inner.iter().cloned());
    }
}

impl<T, B> IntoIter<T, B>
    where B: AsSlice<Item = MaybeUninit<T>>
{
    pub(crate) const fn new(inner: Backend<T, B>) -> Self {
        Self { inner }
    }
}

impl<T, B> Iterator for IntoIter<T, B>
    where B: AsSlice<Item = MaybeUninit<T>>
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.pop_front()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.inner.len();
        (len, Some(len))
    }
}

impl<T, B> ExactSizeIterator for IntoIter<T, B>
    where B: AsSlice<Item = MaybeUninit<T>>
{
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<T, B> FusedIterator for IntoIter<T, B>
    where B: AsSlice<Item = MaybeUninit<T>>
{}

impl<T, B> DoubleEndedIterator for IntoIter<T, B>
    where B: AsSlice<Item = MaybeUninit<T>>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.pop_back()
    }
}

impl<T, B> fmt::Debug for IntoIter<T, B>
    where
        T: fmt::Debug,
        B: AsSlice<Item = MaybeUninit<T>>

{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

/// An owning [iterator](std::iter::Iterator) over the elements of a
/// [`CircularBuffer`]
///
/// This yields the elements of a `CircularBuffer` from fron to back.
///
/// This struct is created when iterating over a `CircularBuffer`. See the
/// documentation for [`IntoIterator`] for more details.
/// 
/// [`CircularBuffer`]: crate::CircularBuffer
#[derive(Clone)]
pub struct StaticIntoIter<const N: usize, T>(pub(crate) IntoIter<T, [MaybeUninit<T>; N]>);
super::impl_iter_traits!(<{const N: usize, T}> - StaticIntoIter<N, T>);

/// An owning [iterator](std::iter::Iterator) over the elements of a
/// [`HeapCircularBuffer`].
///
/// This yields the elements of a `CircularBuffer` from fron to back.
///
/// This struct is created when iterating over a `CircularBuffer`. See the
/// documentation for [`IntoIterator`] for more details.
/// 
/// [`HeapCircularBuffer`]: crate::heap::HeapCircularBuffer
#[derive(Clone)]
pub struct HeapIntoIter<T>(pub(crate) IntoIter<T, Box<[MaybeUninit<T>]>>);
super::impl_iter_traits!(<{T}> - HeapIntoIter<T>);

pub(crate) fn translate_range_bounds<T, B, R>(buf: &Backend<T, B>, range: R) -> (usize, usize)
    where
        R: RangeBounds<usize>,
        B: AsSlice<Item = MaybeUninit<T>>
{
    let start = match range.start_bound() {
        Bound::Included(x) => *x,
        Bound::Excluded(x) => x.checked_add(1)
                               .expect("range start index exceeds maximum usize"),
        Bound::Unbounded   => 0,
    };

    let end = match range.end_bound() {
        Bound::Included(x) => x.checked_add(1)
                               .expect("range end index exceeds maximum usize"),
        Bound::Excluded(x) => *x,
        Bound::Unbounded   => buf.len(),
    };

    assert!(end <= buf.len(), "range end index {} out of range for buffer of length {}", end, buf.len());
    assert!(start <= end, "range starts at index {start} but ends at index {end}");

    (start, end)
}

#[inline(always)]
#[cfg(feature = "unstable")]
fn slice_take<'a, T, R: core::ops::OneSidedRange<usize>>(slice: &mut &'a [T], range: R) -> Option<&'a [T]> {
    slice.take(range)
}

#[cfg(not(feature = "unstable"))]
fn slice_take<'a, T, R: RangeBounds<usize>>(slice: &mut &'a [T], range: R) -> Option<&'a [T]> {
    match (range.start_bound(), range.end_bound()) {
        (Bound::Unbounded, Bound::Excluded(index)) => {
            if *index > slice.len() { return None; }
            let (left, right) = slice.split_at(*index);
            *slice = right;
            Some(left)
        },
        (Bound::Included(index), Bound::Unbounded) => {
            if *index > slice.len() { return None; }
            let (left, right) = slice.split_at(*index);
            *slice = left;
            Some(right)
        },
        _ => unimplemented!(),
    }
}

#[inline(always)]
#[cfg(feature = "unstable")]
fn slice_take_mut<'a, T, R: core::ops::OneSidedRange<usize>>(slice: &mut &'a mut [T], range: R) -> Option<&'a mut [T]> {
    slice.take_mut(range)
}

#[cfg(not(feature = "unstable"))]
fn slice_take_mut<'a, T, R: RangeBounds<usize>>(slice: &mut &'a mut [T], range: R) -> Option<&'a mut [T]> {
    match (range.start_bound(), range.end_bound()) {
        (Bound::Unbounded, Bound::Excluded(index)) => {
            if *index > slice.len() { return None; }
            let (left, right) = core::mem::take(slice).split_at_mut(*index);
            *slice = right;
            Some(left)
        },
        (Bound::Included(index), Bound::Unbounded) => {
            if *index > slice.len() { return None; }
            let (left, right) = core::mem::take(slice).split_at_mut(*index);
            *slice = left;
            Some(right)
        },
        _ => unimplemented!(),
    }
}

#[inline(always)]
#[cfg(feature = "unstable")]
fn slice_take_first<'a, T>(slice: &mut &'a [T]) -> Option<&'a T> {
    slice.take_first()
}

#[cfg(not(feature = "unstable"))]
fn slice_take_first<'a, T>(slice: &mut &'a [T]) -> Option<&'a T> {
    let (item, rest) = slice.split_first()?;
    *slice = rest;
    Some(item)
}

#[inline(always)]
#[cfg(feature = "unstable")]
fn slice_take_first_mut<'a, T>(slice: &mut &'a mut [T]) -> Option<&'a mut T> {
    slice.take_first_mut()
}

#[cfg(not(feature = "unstable"))]
fn slice_take_first_mut<'a, T>(slice: &mut &'a mut [T]) -> Option<&'a mut T> {
    let (item, rest) = core::mem::take(slice).split_first_mut()?;
    *slice = rest;
    Some(item)
}

#[inline(always)]
#[cfg(feature = "unstable")]
fn slice_take_last<'a, T>(slice: &mut &'a [T]) -> Option<&'a T> {
    slice.take_last()
}

#[cfg(not(feature = "unstable"))]
fn slice_take_last<'a, T>(slice: &mut &'a [T]) -> Option<&'a T> {
    let (item, rest) = slice.split_last()?;
    *slice = rest;
    Some(item)
}

#[inline(always)]
#[cfg(feature = "unstable")]
fn slice_take_last_mut<'a, T>(slice: &mut &'a mut [T]) -> Option<&'a mut T> {
    slice.take_last_mut()
}

#[cfg(not(feature = "unstable"))]
fn slice_take_last_mut<'a, T>(slice: &mut &'a mut [T]) -> Option<&'a mut T> {
    let (item, rest) = core::mem::take(slice).split_last_mut()?;
    *slice = rest;
    Some(item)
}

/// An [iterator](std::iter::Iterator) over the elements of a `CircularBuffer` or `HeapCircularBuffer`.
///
/// This struct is created by [`CircularBuffer::iter()`],
/// [`CircularBuffer::range()`], [`CircularBuffer::iter()`] and
/// [`CircularBuffer::range()`]. See their documentation for more details.
/// 
/// [`CircularBuffer::iter()`]: crate::CircularBuffer::iter
/// [`CircularBuffer::range()`]: crate::CircularBuffer::range
/// [`HeapCircularBuffer::iter()`]: crate::heap::HeapCircularBuffer::iter
/// [`HeapCircularBuffer::range()`]: crate::heap::HeapCircularBuffer::range
pub struct Iter<'a, T> {
    pub(crate) right: &'a [T],
    pub(crate) left: &'a [T],
}

impl<'a, T> Iter<'a, T> {
    pub(crate) const fn empty() -> Self {
        Self { right: &[], left: &[] }
    }

    pub(crate) fn new<B>(buf: &'a Backend<T, B>) -> Self
        where B: AsSlice<Item = MaybeUninit<T>>
    {
        let (right, left) = buf.as_slices();
        Self { right, left }
    }

    pub(crate) fn over_range<B, R>(buf: &'a Backend<T, B>, range: R) -> Self
        where
            R: RangeBounds<usize>,
            B: AsSlice<Item = MaybeUninit<T>>
    {
        let (start, end) = translate_range_bounds(buf, range);
        if start >= end {
            Self::empty()
        } else {
            let len = buf.len();
            let mut it = Self::new(buf);
            it.advance_front_by(start);
            it.advance_back_by(len - end);
            it
        }
    }

    fn advance_front_by(&mut self, count: usize) {
        if self.right.len() > count {
            slice_take(&mut self.right, ..count);
        } else {
            let take_left = count - self.right.len();
            debug_assert!(take_left <= self.left.len(),
                          "attempted to advance past the back of the buffer");
            slice_take(&mut self.left, ..take_left);
            self.right = &[];
        }
    }

    fn advance_back_by(&mut self, count: usize) {
        if self.left.len() > count {
            let take_left = self.left.len() - count;
            slice_take(&mut self.left, take_left..);
        } else {
            let take_right = self.right.len() - (count - self.left.len());
            debug_assert!(take_right <= self.right.len(),
                          "attempted to advance past the front of the buffer");
            slice_take(&mut self.right, take_right..);
            self.left = &[];
        }
    }
}

impl<'a, T> Default for Iter<'a, T> {
    #[inline]
    fn default() -> Self {
        Self::empty()
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(item) = slice_take_first(&mut self.right) {
            Some(item)
        } else if let Some(item) = slice_take_first(&mut self.left) {
            Some(item)
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {
    #[inline]
    fn len(&self) -> usize {
        self.right.len() + self.left.len()
    }
}

impl<'a, T> FusedIterator for Iter<'a, T> {}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(item) = slice_take_last(&mut self.left) {
            Some(item)
        } else if let Some(item) = slice_take_last(&mut self.right) {
            Some(item)
        } else {
            None
        }
    }
}

impl<'a, T> Clone for Iter<'a, T> {
    fn clone(&self) -> Self {
        Self { right: self.right, left: self.left }
    }
}

impl<'a, T> fmt::Debug for Iter<'a, T>
    where T: fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A mutable [iterator](std::iter::Iterator) over the elements of a `CircularBuffer` or `HeapCircularBuffer`.
///
/// This struct is created by [`CircularBuffer::iter_mut()`],
/// [`CircularBuffer::range_mut()`], [`HeapCircularBuffer::iter_mut()`] and
/// [`HeapCircularBuffer::range_mut()`]. See their documentation for more
/// details.
/// 
/// [`CircularBuffer::iter_mut()`]: crate::CircularBuffer::iter_mut
/// [`CircularBuffer::range_mut()`]: crate::CircularBuffer::range_mut
/// [`HeapCircularBuffer::iter_mut()`]: crate::heap::HeapCircularBuffer::iter_mut
/// [`HeapCircularBuffer::range_mut()`]: crate::heap::HeapCircularBuffer::range_mut
pub struct IterMut<'a, T> {
    right: &'a mut [T],
    left: &'a mut [T],
}

impl<'a, T> IterMut<'a, T> {
    pub(crate) fn empty() -> Self {
        Self { right: &mut [], left: &mut [] }
    }

    pub(crate) fn new<B>(buf: &'a mut Backend<T, B>) -> Self
        where B: AsSlice<Item = MaybeUninit<T>>
    {
        let (right, left) = buf.as_mut_slices();
        Self { right, left }
    }

    pub(crate) fn over_range<B, R>(buf: &'a mut Backend<T, B>, range: R) -> Self
        where
            R: RangeBounds<usize>,
            B: AsSlice<Item = MaybeUninit<T>>
    {
        let (start, end) = translate_range_bounds(buf, range);
        if start >= end {
            Self::empty()
        } else {
            let len = buf.len();
            let mut it = Self::new(buf);
            it.advance_front_by(start);
            it.advance_back_by(len - end);
            it
        }
    }

    fn advance_front_by(&mut self, count: usize) {
        if self.right.len() > count {
            slice_take_mut(&mut self.right, ..count);
        } else {
            let take_left = count - self.right.len();
            debug_assert!(take_left <= self.left.len(),
                          "attempted to advance past the back of the buffer");
            slice_take_mut(&mut self.left, ..take_left);
            self.right = &mut [];
        }
    }

    fn advance_back_by(&mut self, count: usize) {
        if self.left.len() > count {
            let take_left = self.left.len() - count;
            slice_take_mut(&mut self.left, take_left..);
        } else {
            let take_right = self.right.len() - (count - self.left.len());
            debug_assert!(take_right <= self.right.len(),
                          "attempted to advance past the front of the buffer");
            slice_take_mut(&mut self.right, take_right..);
            self.left = &mut [];
        }
    }
}

impl<'a, T> Default for IterMut<'a, T> {
    #[inline]
    fn default() -> Self {
        Self::empty()
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(item) = slice_take_first_mut(&mut self.right) {
            Some(item)
        } else if let Some(item) = slice_take_first_mut(&mut self.left) {
            Some(item)
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<'a, T> ExactSizeIterator for IterMut<'a, T> {
    #[inline]
    fn len(&self) -> usize {
        self.right.len() + self.left.len()
    }
}

impl<'a, T> FusedIterator for IterMut<'a, T> {}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(item) = slice_take_last_mut(&mut self.left) {
            Some(item)
        } else if let Some(item) = slice_take_last_mut(&mut self.right) {
            Some(item)
        } else {
            None
        }
    }
}

impl<'a, T> fmt::Debug for IterMut<'a, T>
    where T: fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let it = Iter { right: self.right, left: self.left };
        it.fmt(f)
    }
}
