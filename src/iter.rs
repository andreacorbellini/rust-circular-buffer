use core::fmt;
use core::iter::FusedIterator;
use core::ops::Bound;
use core::ops::RangeBounds;
use crate::CircularBuffer;
use crate::unstable_const_fn;

/// An owning [iterator](std::iter::Iterator) over the elements of a [`CircularBuffer`].
///
/// This yields the elements of a `CircularBuffer` from fron to back.
///
/// This struct is created when iterating over a `CircularBuffer`. See the documentation for
/// [`IntoIterator`] for more details.
#[derive(Clone)]
pub struct IntoIter<const N: usize, T> {
    inner: CircularBuffer<N, T>,
}

impl<const N: usize, T> IntoIter<N, T> {
    pub(crate) const fn new(inner: CircularBuffer<N, T>) -> Self {
        Self { inner }
    }
}

impl<const N: usize, T> Iterator for IntoIter<N, T> {
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

impl<const N: usize, T> ExactSizeIterator for IntoIter<N, T> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<const N: usize, T> FusedIterator for IntoIter<N, T> {}

impl<const N: usize, T> DoubleEndedIterator for IntoIter<N, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.pop_back()
    }
}

impl<const N: usize, T> fmt::Debug for IntoIter<N, T>
    where T: fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

fn translate_range_bounds<const N: usize, T, R>(buf: &CircularBuffer<N, T>, range: R) -> (usize, usize)
    where R: RangeBounds<usize>
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

/// An [iterator](std::iter::Iterator) over the elements of a `CircularBuffer`.
///
/// This struct is created by [`CircularBuffer::iter()`] and [`CircularBuffer::range()`]. See
/// their documentation for more details.
pub struct Iter<'a, T> {
    right: &'a [T],
    left: &'a [T],
}

impl<'a, T> Iter<'a, T> {
    pub(crate) const fn empty() -> Self {
        Self { right: &[], left: &[] }
    }

    unstable_const_fn! {
        pub(crate) const fn new<{const N: usize}>(buf: &'a CircularBuffer<N, T>) -> Self {
            let (right, left) = buf.as_slices();
            Self { right, left }
        }
    }

    pub(crate) fn over_range<const N: usize, R>(buf: &'a CircularBuffer<N, T>, range: R) -> Self
        where R: RangeBounds<usize>
    {
        let (start, end) = translate_range_bounds(buf, range);
        if start >= end {
            Self::empty()
        } else {
            let mut it = Self::new(buf);
            it.advance_front_by(start);
            it.advance_back_by(end - start);
            it
        }
    }

    fn advance_front_by(&mut self, count: usize) {
        if slice_take(&mut self.right, ..count).is_none() {
            let take_left = count - self.right.len();
            slice_take(&mut self.left, ..take_left)
                .expect("attempted to advance past the back of the buffer");
            self.right = &mut [];
        }
    }

    fn advance_back_by(&mut self, count: usize) {
        if slice_take(&mut self.left, count..).is_none() {
            let take_right = count - self.left.len();
            slice_take(&mut self.right, take_right..)
                .expect("attempted to advance past the front of the buffer");
            self.left = &mut [];
        }
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

/// A mutable [iterator](std::iter::Iterator) over the elements of a `CircularBuffer`.
///
/// This struct is created by [`CircularBuffer::iter_mut()`] and [`CircularBuffer::range_mut()`].
/// See their documentation for more details.
pub struct IterMut<'a, T> {
    right: &'a mut [T],
    left: &'a mut [T],
}

impl<'a, T> IterMut<'a, T> {
    unstable_const_fn! {
        pub(crate) const fn empty() -> Self {
            Self { right: &mut [], left: &mut [] }
        }
    }

    unstable_const_fn! {
        pub(crate) const fn new<{const N: usize}>(buf: &'a mut CircularBuffer<N, T>) -> Self {
            let (right, left) = buf.as_mut_slices();
            Self { right, left }
        }
    }

    pub(crate) fn over_range<const N: usize, R>(buf: &'a mut CircularBuffer<N, T>, range: R) -> Self
        where R: RangeBounds<usize>
    {
        let (start, end) = translate_range_bounds(buf, range);
        if start >= end {
            Self::empty()
        } else {
            let mut it = Self::new(buf);
            it.advance_front_by(start);
            it.advance_back_by(end - start);
            it
        }
    }

    fn advance_front_by(&mut self, count: usize) {
        if slice_take_mut(&mut self.right, ..count).is_none() {
            let take_left = count - self.right.len();
            slice_take_mut(&mut self.left, ..take_left)
                .expect("attempted to advance past the back of the buffer");
            self.right = &mut [];
        }
    }

    fn advance_back_by(&mut self, count: usize) {
        if slice_take_mut(&mut self.left, count..).is_none() {
            let take_right = count - self.left.len();
            slice_take_mut(&mut self.right, take_right..)
                .expect("attempted to advance past the front of the buffer");
            self.left = &mut [];
        }
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
