// Copyright © 2023-2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

//! Implementations of [`PartialEq`], [`Eq`], [`PartialOrd`], [`Ord`].

use crate::CircularBuffer;
use crate::FixedCircularBuffer;
use core::cmp::Ordering;
use core::convert::identity;
use core::ops::Deref;

#[cfg(feature = "alloc")]
use crate::HeapCircularBuffer;

impl<T> Eq for CircularBuffer<T> where T: Eq {}

impl<T, const N: usize> Eq for FixedCircularBuffer<T, N> where T: Eq {}

#[cfg(feature = "alloc")]
impl<T> Eq for HeapCircularBuffer<T> where T: Eq {}

impl<T, U> PartialEq<CircularBuffer<U>> for CircularBuffer<T>
where
    T: PartialEq<U>,
{
    fn eq(&self, other: &CircularBuffer<U>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        let (a_left, a_right) = self.as_slices();
        let (b_left, b_right) = other.as_slices();

        match a_left.len().cmp(&b_left.len()) {
            Ordering::Less => {
                let x = a_left.len();
                let y = b_left.len() - x;
                a_left[..] == b_left[..x]
                    && a_right[..y] == b_left[x..]
                    && a_right[y..] == b_right[..]
            }
            Ordering::Greater => {
                let x = b_left.len();
                let y = a_left.len() - x;
                a_left[..x] == b_left[..]
                    && a_left[x..] == b_right[..y]
                    && a_right[..] == b_right[y..]
            }
            Ordering::Equal => {
                debug_assert_eq!(a_left.len(), b_left.len());
                debug_assert_eq!(a_right.len(), b_right.len());
                a_left == b_left && a_right == b_right
            }
        }
    }
}

impl<T, U> PartialEq<[U]> for CircularBuffer<T>
where
    T: PartialEq<U>,
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

impl<T, U> PartialEq<CircularBuffer<U>> for [T]
where
    T: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &CircularBuffer<U>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        let (a_left, a_right) = other.as_slices();
        let (b_left, b_right) = self.split_at(a_left.len());

        debug_assert_eq!(a_left.len(), b_left.len());
        debug_assert_eq!(a_right.len(), b_right.len());
        b_left == a_left && b_right == a_right
    }
}

macro_rules! impl_partial_eq {
    ( [ $( $generics:tt )* ] $lhs:ty [ $l_transform:path ] , $rhs:ty [ $r_transform:path ] ) => {
        impl<T, U, $($generics)*> PartialEq<$rhs> for $lhs
        where
            T: PartialEq<U>,
        {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                $l_transform(self) == $r_transform(other)
            }
        }
    };
}

macro_rules! impl_partial_eq_with_refs {
    ( [ $( $generics:tt )* ] $lhs:ty [ $l_transform:path ] , $rhs:ty [ $r_transform:path ] ) => {
        impl_partial_eq!([$($generics)*] $lhs [$l_transform], $rhs [$r_transform]);
        impl_partial_eq!([$($generics)*] $lhs [$l_transform], &'_ $rhs [$r_transform]);
        impl_partial_eq!([$($generics)*] $lhs [$l_transform], &'_ mut $rhs [$r_transform]);
        impl_partial_eq!([$($generics)*] &'_ $lhs [$l_transform], $rhs [$r_transform]);
        impl_partial_eq!([$($generics)*] &'_ mut $lhs [$l_transform], $rhs [$r_transform]);
    };
}

// CircularBuffer <=> CircularBuffer
impl_partial_eq!([] CircularBuffer<T> [identity], &'_ CircularBuffer<U> [Deref::deref]);
impl_partial_eq!([] CircularBuffer<T> [identity], &'_ mut CircularBuffer<U> [Deref::deref]);
impl_partial_eq!([] &'_ CircularBuffer<T> [Deref::deref], CircularBuffer<U> [identity]);
impl_partial_eq!([] &'_ mut CircularBuffer<T> [Deref::deref], CircularBuffer<U> [identity]);

// CircularBuffer <=> slice
impl_partial_eq!([] CircularBuffer<T> [identity], &'_ [U] [Deref::deref]);
impl_partial_eq!([] CircularBuffer<T> [identity], &'_ mut [U] [Deref::deref]);
impl_partial_eq!([] &'_ CircularBuffer<T> [Deref::deref], [U] [identity]);
impl_partial_eq!([] &'_ mut CircularBuffer<T> [Deref::deref], [U] [identity]);

// CircularBuffer <=> array
impl_partial_eq_with_refs!([const M: usize] CircularBuffer<T> [identity], [U; M] [AsRef::as_ref]);

// CircularBuffer <=> FixedCircularBuffer
impl_partial_eq_with_refs!([const M: usize] CircularBuffer<T> [identity], FixedCircularBuffer<U, M> [Deref::deref]);
impl_partial_eq_with_refs!([const N: usize] FixedCircularBuffer<T, N> [Deref::deref], CircularBuffer<U> [identity]);

// CircularBuffer <=> HeapCircularBuffer
#[cfg(feature = "alloc")]
impl_partial_eq_with_refs!([] CircularBuffer<T> [identity], HeapCircularBuffer<U> [Deref::deref]);
#[cfg(feature = "alloc")]
impl_partial_eq_with_refs!([] HeapCircularBuffer<T> [Deref::deref], CircularBuffer<U> [identity]);

// FixedCircularBuffer <=> FixedCircularBuffer, slice, array
impl_partial_eq_with_refs!([const N: usize, const M: usize] FixedCircularBuffer<T, N> [Deref::deref], FixedCircularBuffer<U, M> [Deref::deref]);
impl_partial_eq_with_refs!([const N: usize] FixedCircularBuffer<T, N> [Deref::deref], [U] [identity]);
impl_partial_eq_with_refs!([const N: usize, const M: usize] FixedCircularBuffer<T, N> [Deref::deref], [U; M] [AsRef::as_ref]);

// HeapCircularBuffer <=> HeapCircularBuffer, slice, array
#[cfg(feature = "alloc")]
impl_partial_eq_with_refs!([] HeapCircularBuffer<T> [Deref::deref], HeapCircularBuffer<U> [Deref::deref]);
#[cfg(feature = "alloc")]
impl_partial_eq_with_refs!([] HeapCircularBuffer<T> [Deref::deref], [U] [identity]);
#[cfg(feature = "alloc")]
impl_partial_eq_with_refs!([const M: usize] HeapCircularBuffer<T> [Deref::deref], [U; M] [AsRef::as_ref]);

// Box<CircularBuffer> <=> slice, array
#[cfg(feature = "alloc")]
impl_partial_eq_with_refs!([] Box<CircularBuffer<T>> [Deref::deref], [U] [identity]);
#[cfg(feature = "alloc")]
impl_partial_eq_with_refs!([const M: usize] Box<CircularBuffer<T>> [Deref::deref], [U; M] [AsRef::as_ref]);

impl<T, U> PartialOrd<CircularBuffer<U>> for CircularBuffer<T>
where
    T: PartialOrd<U>,
{
    fn partial_cmp(&self, other: &CircularBuffer<U>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T> Ord for CircularBuffer<T>
where
    T: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T, const N: usize, U, const M: usize> PartialOrd<FixedCircularBuffer<U, M>>
    for FixedCircularBuffer<T, N>
where
    T: PartialOrd<U>,
{
    #[inline]
    fn partial_cmp(&self, other: &FixedCircularBuffer<U, M>) -> Option<Ordering> {
        self.deref().partial_cmp(other.deref())
    }
}

impl<T, const N: usize> Ord for FixedCircularBuffer<T, N>
where
    T: Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.deref().cmp(other.deref())
    }
}

impl<T, U> PartialOrd<HeapCircularBuffer<U>> for HeapCircularBuffer<T>
where
    T: PartialOrd<U>,
{
    #[inline]
    fn partial_cmp(&self, other: &HeapCircularBuffer<U>) -> Option<Ordering> {
        self.deref().partial_cmp(other.deref())
    }
}

impl<T> Ord for HeapCircularBuffer<T>
where
    T: Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.deref().cmp(other.deref())
    }
}
