// Copyright © 2023-2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

use circular_buffer::CircularBuffer;

/// Returns `true` if the elements of the given buffer are all contained in a contiguous slice.
#[must_use]
pub(crate) fn is_contiguous<T>(buf: &CircularBuffer<T>) -> bool {
    let slices = buf.as_slices();
    slices.1.is_empty()
}

/// Asserts that the specified buffer contains the specified elements.
macro_rules! assert_buf_eq {
    ( $buf:ident , [] $( as [ $( $arrtyp:tt )* ] )? ) => {
        let expected = [] $(as [ $($arrtyp)* ])?;
        assert!($buf.is_empty(), "{} is not empty", stringify!($buf));
        assert_eq!($buf, expected, "{} does not equal an empty array", stringify!($buf));
        assert_eq!($buf, &expected, "{} does not equal an empty array reference", stringify!($buf));
        assert_eq!($buf, &expected[..], "{} does not equal an empty slice", stringify!($buf));
        assert_eq!($buf.len(), 0, "{} length does not equal 0", stringify!($buf));
        assert_eq!($buf.iter().next(), None, "{} iterator is not empty", stringify!($buf));
    };
    ( $buf:ident , [ $( $elems:tt )* ] ) => {
        let expected = [ $($elems)* ];
        assert!(!$buf.is_empty(), "{} is empty", stringify!($buf));
        assert_eq!($buf, expected);
        assert_eq!($buf, &expected);
        assert_eq!($buf, &expected[..]);
        assert_eq!($buf.len(), expected.len(), "{} length does not equal {}", stringify!($buf), expected.len());

        let mut buf_iter = $buf.iter();
        let mut expected_iter = expected.iter();
        loop {
            match (buf_iter.next(), expected_iter.next()) {
                (Some(buf_item), Some(expected_item)) => assert_eq!(buf_item, expected_item),
                (Some(buf_item), None)                => panic!("{} iterator returned extra item: {:?}", stringify!(buf), buf_item),
                (None, Some(expected_item))           => panic!("{} iterator missing item: {:?}", stringify!(buf), expected_item),
                (None, None)                          => break,
            }
        }

        for i in 0..expected.len() {
            assert_eq!($buf[i], expected[i]);
            assert_eq!($buf.get(i).unwrap(), expected.get(i).unwrap());
            assert_eq!($buf.nth_front(i).unwrap(), expected.get(i).unwrap());
            assert_eq!($buf.nth_back(i).unwrap(), expected.get(expected.len() - i - 1).unwrap());
        }
    };
}

macro_rules! define_tests {
    ( $new_buffer:ident , $buffer_from:ident , $buffer_from_iter:ident $(,)? ) => {
        use core::ops::Bound;
        use drop_tracker::DropItem;
        use drop_tracker::DropTracker;
        use $crate::common::assert_buf_eq;
        use $crate::common::is_contiguous;

        #[test]
        fn attrs() {
            let mut buf = $new_buffer::<u32, 4>();
            assert_eq!(buf.len(), 0);
            assert!(buf.is_empty());
            assert!(!buf.is_full());

            buf.push_back(1);
            assert_eq!(buf.len(), 1);
            assert!(!buf.is_empty());
            assert!(!buf.is_full());

            buf.push_back(2);
            assert_eq!(buf.len(), 2);
            assert!(!buf.is_empty());
            assert!(!buf.is_full());

            buf.push_back(3);
            assert_eq!(buf.len(), 3);
            assert!(!buf.is_empty());
            assert!(!buf.is_full());

            buf.push_back(4);
            assert_eq!(buf.len(), 4);
            assert!(!buf.is_empty());
            assert!(buf.is_full());

            buf.push_back(5);
            assert_eq!(buf.len(), 4);
            assert!(!buf.is_empty());
            assert!(buf.is_full());

            buf.push_back(6);
            assert_eq!(buf.len(), 4);
            assert!(!buf.is_empty());
            assert!(buf.is_full());

            buf.clear();
            assert_eq!(buf.len(), 0);
            assert!(buf.is_empty());
            assert!(!buf.is_full());
        }

        #[test]
        fn push_back() {
            let mut tracker = DropTracker::new();
            let mut buf = $new_buffer::<DropItem<i32>, 4>();
            assert_buf_eq!(buf, [] as [i32; 0]);

            assert_eq!(buf.push_back(tracker.track(1)), None);
            assert_buf_eq!(buf, [1]);
            tracker.assert_all_alive([1]);
            tracker.assert_fully_alive();

            assert_eq!(buf.push_back(tracker.track(2)), None);
            assert_buf_eq!(buf, [1, 2]);
            tracker.assert_all_alive([1, 2]);
            tracker.assert_fully_alive();

            assert_eq!(buf.push_back(tracker.track(3)), None);
            assert_buf_eq!(buf, [1, 2, 3]);
            tracker.assert_all_alive([1, 2, 3]);
            tracker.assert_fully_alive();

            assert_eq!(buf.push_back(tracker.track(4)), None);
            assert_buf_eq!(buf, [1, 2, 3, 4]);
            tracker.assert_all_alive([1, 2, 3, 4]);
            tracker.assert_fully_alive();

            assert_eq!(buf.push_back(tracker.track(5)).unwrap(), 1);
            assert_buf_eq!(buf, [2, 3, 4, 5]);
            tracker.assert_all_alive([2, 3, 4, 5]);
            tracker.assert_all_dropped([1]);

            assert_eq!(buf.push_back(tracker.track(6)).unwrap(), 2);
            assert_buf_eq!(buf, [3, 4, 5, 6]);
            tracker.assert_all_alive([3, 4, 5, 6]);
            tracker.assert_all_dropped([1, 2]);

            assert_eq!(buf.push_back(tracker.track(7)).unwrap(), 3);
            assert_buf_eq!(buf, [4, 5, 6, 7]);
            tracker.assert_all_alive([4, 5, 6, 7]);
            tracker.assert_all_dropped([1, 2, 3]);

            assert_eq!(buf.push_back(tracker.track(8)).unwrap(), 4);
            assert_buf_eq!(buf, [5, 6, 7, 8]);
            tracker.assert_all_alive([5, 6, 7, 8]);
            tracker.assert_all_dropped([1, 2, 3, 4]);
        }

        #[test]
        fn push_front() {
            let mut tracker = DropTracker::new();
            let mut buf = $new_buffer::<DropItem<i32>, 4>();
            assert_buf_eq!(buf, [] as [i32; 0]);

            assert_eq!(buf.push_front(tracker.track(1)), None);
            assert_buf_eq!(buf, [1]);
            tracker.assert_all_alive([1]);
            tracker.assert_fully_alive();

            assert_eq!(buf.push_front(tracker.track(2)), None);
            assert_buf_eq!(buf, [2, 1]);
            tracker.assert_all_alive([1, 2]);
            tracker.assert_fully_alive();

            assert_eq!(buf.push_front(tracker.track(3)), None);
            assert_buf_eq!(buf, [3, 2, 1]);
            tracker.assert_all_alive([1, 2, 3]);
            tracker.assert_fully_alive();

            assert_eq!(buf.push_front(tracker.track(4)), None);
            assert_buf_eq!(buf, [4, 3, 2, 1]);
            tracker.assert_all_alive([1, 2, 3, 4]);
            tracker.assert_fully_alive();

            assert_eq!(buf.push_front(tracker.track(5)).unwrap(), 1);
            assert_buf_eq!(buf, [5, 4, 3, 2]);
            tracker.assert_all_alive([2, 3, 4, 5]);
            tracker.assert_all_dropped([1]);

            assert_eq!(buf.push_front(tracker.track(6)).unwrap(), 2);
            assert_buf_eq!(buf, [6, 5, 4, 3]);
            tracker.assert_all_alive([3, 4, 5, 6]);
            tracker.assert_all_dropped([1, 2]);

            assert_eq!(buf.push_front(tracker.track(7)).unwrap(), 3);
            assert_buf_eq!(buf, [7, 6, 5, 4]);
            tracker.assert_all_alive([4, 5, 6, 7]);
            tracker.assert_all_dropped([1, 2, 3]);

            assert_eq!(buf.push_front(tracker.track(8)).unwrap(), 4);
            assert_buf_eq!(buf, [8, 7, 6, 5]);
            tracker.assert_all_alive([5, 6, 7, 8]);
            tracker.assert_all_dropped([1, 2, 3, 4]);
        }

        #[test]
        fn pop_back() {
            let mut buf = $new_buffer::<u32, 4>();
            assert_buf_eq!(buf, [] as [u32; 0]);

            assert_eq!(buf.pop_back(), None);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.push_back(1);
            assert_buf_eq!(buf, [1]);
            assert_eq!(buf.pop_back(), Some(1));
            assert_buf_eq!(buf, [] as [u32; 0]);
            assert_eq!(buf.pop_back(), None);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.push_back(2);
            assert_buf_eq!(buf, [2]);
            buf.push_back(3);
            assert_buf_eq!(buf, [2, 3]);
            assert_eq!(buf.pop_back(), Some(3));
            assert_buf_eq!(buf, [2]);
            assert_eq!(buf.pop_back(), Some(2));
            assert_buf_eq!(buf, [] as [u32; 0]);
            assert_eq!(buf.pop_back(), None);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.push_back(4);
            assert_buf_eq!(buf, [4]);
            buf.push_back(5);
            assert_buf_eq!(buf, [4, 5]);
            buf.push_back(6);
            assert_buf_eq!(buf, [4, 5, 6]);
            buf.push_back(7);
            assert_buf_eq!(buf, [4, 5, 6, 7]);
            buf.push_back(8);
            assert_buf_eq!(buf, [5, 6, 7, 8]);
            assert_eq!(buf.pop_back(), Some(8));
            assert_buf_eq!(buf, [5, 6, 7]);
            assert_eq!(buf.pop_back(), Some(7));
            assert_buf_eq!(buf, [5, 6]);
            assert_eq!(buf.pop_back(), Some(6));
            assert_buf_eq!(buf, [5]);
            assert_eq!(buf.pop_back(), Some(5));
            assert_buf_eq!(buf, [] as [u32; 0]);
            assert_eq!(buf.pop_back(), None);
            assert_buf_eq!(buf, [] as [u32; 0]);
        }

        #[test]
        fn pop_front() {
            let mut buf = $new_buffer::<u32, 4>();
            assert_buf_eq!(buf, [] as [u32; 0]);

            assert_eq!(buf.pop_front(), None);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.push_front(1);
            assert_buf_eq!(buf, [1]);
            assert_eq!(buf.pop_front(), Some(1));
            assert_buf_eq!(buf, [] as [u32; 0]);
            assert_eq!(buf.pop_front(), None);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.push_front(2);
            assert_buf_eq!(buf, [2]);
            buf.push_front(3);
            assert_buf_eq!(buf, [3, 2]);
            assert_eq!(buf.pop_front(), Some(3));
            assert_buf_eq!(buf, [2]);
            assert_eq!(buf.pop_front(), Some(2));
            assert_buf_eq!(buf, [] as [u32; 0]);
            assert_eq!(buf.pop_front(), None);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.push_front(4);
            assert_buf_eq!(buf, [4]);
            buf.push_front(5);
            assert_buf_eq!(buf, [5, 4]);
            buf.push_front(6);
            assert_buf_eq!(buf, [6, 5, 4]);
            buf.push_front(7);
            assert_buf_eq!(buf, [7, 6, 5, 4]);
            buf.push_front(8);
            assert_buf_eq!(buf, [8, 7, 6, 5]);
            assert_eq!(buf.pop_front(), Some(8));
            assert_buf_eq!(buf, [7, 6, 5]);
            assert_eq!(buf.pop_front(), Some(7));
            assert_buf_eq!(buf, [6, 5]);
            assert_eq!(buf.pop_front(), Some(6));
            assert_buf_eq!(buf, [5]);
            assert_eq!(buf.pop_front(), Some(5));
            assert_buf_eq!(buf, [] as [u32; 0]);
            assert_eq!(buf.pop_front(), None);
            assert_buf_eq!(buf, [] as [u32; 0]);
        }

        #[test]
        fn remove() {
            let mut buf = $new_buffer::<u32, 4>();
            assert_buf_eq!(buf, [] as [u32; 0]);

            assert_eq!(buf.remove(0), None);
            assert_eq!(buf.remove(1), None);
            assert_eq!(buf.remove(2), None);
            assert_eq!(buf.remove(3), None);
            assert_eq!(buf.remove(4), None);
            assert_eq!(buf.remove(5), None);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.push_back(1);
            assert_buf_eq!(buf, [1]);
            assert_eq!(buf.remove(0), Some(1));
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.push_back(2);
            assert_buf_eq!(buf, [2]);
            buf.push_back(3);
            assert_buf_eq!(buf, [2, 3]);
            buf.push_back(4);
            assert_buf_eq!(buf, [2, 3, 4]);
            assert_eq!(buf.remove(1), Some(3));
            assert_buf_eq!(buf, [2, 4]);

            buf.push_back(5);
            assert_buf_eq!(buf, [2, 4, 5]);
            buf.push_back(6);
            assert_buf_eq!(buf, [2, 4, 5, 6]);
            buf.push_back(7);
            assert_buf_eq!(buf, [4, 5, 6, 7]);
            buf.push_back(8);
            assert_buf_eq!(buf, [5, 6, 7, 8]);
            assert_eq!(buf.remove(2), Some(7));
            assert_buf_eq!(buf, [5, 6, 8]);
            assert_eq!(buf.remove(2), Some(8));
            assert_buf_eq!(buf, [5, 6]);
            assert_eq!(buf.remove(1), Some(6));
            assert_buf_eq!(buf, [5]);
            assert_eq!(buf.remove(0), Some(5));
            assert_buf_eq!(buf, [] as [u32; 0]);
        }

        #[test]
        fn swap() {
            let mut buf = $buffer_from::<u32, 4, _>([1, 2, 3, 4]);

            buf.swap(0, 3);
            assert_buf_eq!(buf, [4, 2, 3, 1]);
            buf.swap(1, 2);
            assert_buf_eq!(buf, [4, 3, 2, 1]);
            buf.pop_front();
            assert_buf_eq!(buf, [3, 2, 1]);
            buf.push_back(4);
            assert_buf_eq!(buf, [3, 2, 1, 4]);
            assert!(!is_contiguous(&buf));
            buf.swap(0, 1);
            assert_buf_eq!(buf, [2, 3, 1, 4]);
            buf.swap(1, 2);
            assert_buf_eq!(buf, [2, 1, 3, 4]);
            buf.swap(2, 3);
            assert_buf_eq!(buf, [2, 1, 4, 3]);
            buf.swap(3, 0);
            assert_buf_eq!(buf, [3, 1, 4, 2]);
        }

        #[test]
        fn truncate_back() {
            let mut tracker = DropTracker::new();
            let mut buf = $new_buffer::<DropItem<i32>, 4>();
            assert_buf_eq!(buf, [] as [i32; 0]);

            buf.push_back(tracker.track(1));
            buf.push_back(tracker.track(2));
            buf.push_back(tracker.track(3));
            buf.push_back(tracker.track(4));
            assert_buf_eq!(buf, [1, 2, 3, 4]);
            tracker.assert_all_alive([1, 2, 3, 4]);
            tracker.assert_fully_alive();

            buf.truncate_back(2);
            assert_buf_eq!(buf, [1, 2]);
            tracker.assert_all_alive([1, 2]);
            tracker.assert_all_dropped([3, 4]);

            buf.truncate_back(0);
            assert_buf_eq!(buf, [] as [i32; 0]);
            tracker.assert_fully_dropped();
            tracker.assert_all_dropped([1, 2, 3, 4]);

            // Explicitly drop `buf` here to avoid an early implicit drop
            drop(buf);
        }

        #[test]
        fn truncate_front() {
            let mut tracker = DropTracker::new();
            let mut buf = $new_buffer::<DropItem<i32>, 4>();
            assert_buf_eq!(buf, [] as [i32; 0]);

            buf.push_back(tracker.track(1));
            buf.push_back(tracker.track(2));
            buf.push_back(tracker.track(3));
            buf.push_back(tracker.track(4));
            assert_buf_eq!(buf, [1, 2, 3, 4]);
            tracker.assert_all_alive([1, 2, 3, 4]);
            tracker.assert_fully_alive();

            buf.truncate_front(2);
            assert_buf_eq!(buf, [3, 4]);
            tracker.assert_all_alive([3, 4]);
            tracker.assert_all_dropped([1, 2]);

            buf.truncate_front(0);
            assert_buf_eq!(buf, [] as [i32; 0]);
            tracker.assert_fully_dropped();
            tracker.assert_all_dropped([1, 2, 3, 4]);

            // Explicitly drop `buf` here to avoid an early implicit drop
            drop(buf);
        }

        #[test]
        fn get() {
            let mut buf = $new_buffer::<u32, 4>();
            assert_buf_eq!(buf, [] as [u32; 0]);

            assert_eq!(buf.get(0), None);
            assert_eq!(buf.get(1), None);
            assert_eq!(buf.get(2), None);
            assert_eq!(buf.get(3), None);
            assert_eq!(buf.get(4), None);
            assert_eq!(buf.get(5), None);

            buf.push_back(1);
            assert_buf_eq!(buf, [1]);
            assert_eq!(buf.get(0), Some(&1));
            assert_eq!(buf.get(1), None);

            buf.push_back(2);
            assert_buf_eq!(buf, [1, 2]);
            assert_eq!(buf.get(0), Some(&1));
            assert_eq!(buf.get(1), Some(&2));
            assert_eq!(buf.get(2), None);

            buf.push_back(3);
            assert_buf_eq!(buf, [1, 2, 3]);
            assert_eq!(buf.get(0), Some(&1));
            assert_eq!(buf.get(1), Some(&2));
            assert_eq!(buf.get(2), Some(&3));
            assert_eq!(buf.get(3), None);

            buf.push_back(4);
            assert_buf_eq!(buf, [1, 2, 3, 4]);
            assert_eq!(buf.get(0), Some(&1));
            assert_eq!(buf.get(1), Some(&2));
            assert_eq!(buf.get(2), Some(&3));
            assert_eq!(buf.get(3), Some(&4));
            assert_eq!(buf.get(4), None);

            buf.push_back(5);
            assert_buf_eq!(buf, [2, 3, 4, 5]);
            assert_eq!(buf.get(0), Some(&2));
            assert_eq!(buf.get(1), Some(&3));
            assert_eq!(buf.get(2), Some(&4));
            assert_eq!(buf.get(3), Some(&5));
            assert_eq!(buf.get(4), None);

            buf.push_back(6);
            assert_buf_eq!(buf, [3, 4, 5, 6]);
            assert_eq!(buf.get(0), Some(&3));
            assert_eq!(buf.get(1), Some(&4));
            assert_eq!(buf.get(2), Some(&5));
            assert_eq!(buf.get(3), Some(&6));
            assert_eq!(buf.get(5), None);

            buf.push_back(7);
            assert_buf_eq!(buf, [4, 5, 6, 7]);
            assert_eq!(buf.get(0), Some(&4));
            assert_eq!(buf.get(1), Some(&5));
            assert_eq!(buf.get(2), Some(&6));
            assert_eq!(buf.get(3), Some(&7));
            assert_eq!(buf.get(4), None);

            buf.push_back(8);
            assert_buf_eq!(buf, [5, 6, 7, 8]);
            assert_eq!(buf.get(0), Some(&5));
            assert_eq!(buf.get(1), Some(&6));
            assert_eq!(buf.get(2), Some(&7));
            assert_eq!(buf.get(3), Some(&8));
            assert_eq!(buf.get(4), None);
        }

        #[test]
        fn nth_front() {
            let mut buf = $new_buffer::<u32, 4>();
            assert_buf_eq!(buf, [] as [u32; 0]);

            assert_eq!(buf.nth_front(0), None);
            assert_eq!(buf.nth_front(1), None);
            assert_eq!(buf.nth_front(2), None);
            assert_eq!(buf.nth_front(3), None);
            assert_eq!(buf.nth_front(4), None);
            assert_eq!(buf.nth_front(5), None);

            buf.push_back(1);
            assert_buf_eq!(buf, [1]);
            assert_eq!(buf.nth_front(0), Some(&1));
            assert_eq!(buf.nth_front(1), None);

            buf.push_back(2);
            assert_buf_eq!(buf, [1, 2]);
            assert_eq!(buf.nth_front(0), Some(&1));
            assert_eq!(buf.nth_front(1), Some(&2));
            assert_eq!(buf.nth_front(2), None);

            buf.push_back(3);
            assert_buf_eq!(buf, [1, 2, 3]);
            assert_eq!(buf.nth_front(0), Some(&1));
            assert_eq!(buf.nth_front(1), Some(&2));
            assert_eq!(buf.nth_front(2), Some(&3));
            assert_eq!(buf.nth_front(3), None);

            buf.push_back(4);
            assert_buf_eq!(buf, [1, 2, 3, 4]);
            assert_eq!(buf.nth_front(0), Some(&1));
            assert_eq!(buf.nth_front(1), Some(&2));
            assert_eq!(buf.nth_front(2), Some(&3));
            assert_eq!(buf.nth_front(3), Some(&4));
            assert_eq!(buf.nth_front(4), None);

            buf.push_back(5);
            assert_buf_eq!(buf, [2, 3, 4, 5]);
            assert_eq!(buf.nth_front(0), Some(&2));
            assert_eq!(buf.nth_front(1), Some(&3));
            assert_eq!(buf.nth_front(2), Some(&4));
            assert_eq!(buf.nth_front(3), Some(&5));
            assert_eq!(buf.nth_front(4), None);

            buf.push_back(6);
            assert_buf_eq!(buf, [3, 4, 5, 6]);
            assert_eq!(buf.nth_front(0), Some(&3));
            assert_eq!(buf.nth_front(1), Some(&4));
            assert_eq!(buf.nth_front(2), Some(&5));
            assert_eq!(buf.nth_front(3), Some(&6));
            assert_eq!(buf.nth_front(5), None);

            buf.push_back(7);
            assert_buf_eq!(buf, [4, 5, 6, 7]);
            assert_eq!(buf.nth_front(0), Some(&4));
            assert_eq!(buf.nth_front(1), Some(&5));
            assert_eq!(buf.nth_front(2), Some(&6));
            assert_eq!(buf.nth_front(3), Some(&7));
            assert_eq!(buf.nth_front(4), None);

            buf.push_back(8);
            assert_buf_eq!(buf, [5, 6, 7, 8]);
            assert_eq!(buf.nth_front(0), Some(&5));
            assert_eq!(buf.nth_front(1), Some(&6));
            assert_eq!(buf.nth_front(2), Some(&7));
            assert_eq!(buf.nth_front(3), Some(&8));
            assert_eq!(buf.nth_front(4), None);
        }

        #[test]
        fn nth_back() {
            let mut buf = $new_buffer::<u32, 4>();
            assert_buf_eq!(buf, [] as [u32; 0]);

            assert_eq!(buf.nth_back(0), None);
            assert_eq!(buf.nth_back(1), None);
            assert_eq!(buf.nth_back(2), None);
            assert_eq!(buf.nth_back(3), None);
            assert_eq!(buf.nth_back(4), None);
            assert_eq!(buf.nth_back(5), None);

            buf.push_front(1);
            assert_buf_eq!(buf, [1]);
            assert_eq!(buf.nth_back(0), Some(&1));
            assert_eq!(buf.nth_back(1), None);

            buf.push_front(2);
            assert_buf_eq!(buf, [2, 1]);
            assert_eq!(buf.nth_back(0), Some(&1));
            assert_eq!(buf.nth_back(1), Some(&2));
            assert_eq!(buf.nth_back(2), None);

            buf.push_front(3);
            assert_buf_eq!(buf, [3, 2, 1]);
            assert_eq!(buf.nth_back(0), Some(&1));
            assert_eq!(buf.nth_back(1), Some(&2));
            assert_eq!(buf.nth_back(2), Some(&3));
            assert_eq!(buf.nth_back(3), None);

            buf.push_front(4);
            assert_buf_eq!(buf, [4, 3, 2, 1]);
            assert_eq!(buf.nth_back(0), Some(&1));
            assert_eq!(buf.nth_back(1), Some(&2));
            assert_eq!(buf.nth_back(2), Some(&3));
            assert_eq!(buf.nth_back(3), Some(&4));
            assert_eq!(buf.nth_back(4), None);

            buf.push_front(5);
            assert_buf_eq!(buf, [5, 4, 3, 2]);
            assert_eq!(buf.nth_back(0), Some(&2));
            assert_eq!(buf.nth_back(1), Some(&3));
            assert_eq!(buf.nth_back(2), Some(&4));
            assert_eq!(buf.nth_back(3), Some(&5));
            assert_eq!(buf.nth_back(4), None);

            buf.push_front(6);
            assert_buf_eq!(buf, [6, 5, 4, 3]);
            assert_eq!(buf.nth_back(0), Some(&3));
            assert_eq!(buf.nth_back(1), Some(&4));
            assert_eq!(buf.nth_back(2), Some(&5));
            assert_eq!(buf.nth_back(3), Some(&6));
            assert_eq!(buf.nth_back(5), None);

            buf.push_front(7);
            assert_buf_eq!(buf, [7, 6, 5, 4]);
            assert_eq!(buf.nth_back(0), Some(&4));
            assert_eq!(buf.nth_back(1), Some(&5));
            assert_eq!(buf.nth_back(2), Some(&6));
            assert_eq!(buf.nth_back(3), Some(&7));
            assert_eq!(buf.nth_back(4), None);

            buf.push_front(8);
            assert_buf_eq!(buf, [8, 7, 6, 5]);
            assert_eq!(buf.nth_back(0), Some(&5));
            assert_eq!(buf.nth_back(1), Some(&6));
            assert_eq!(buf.nth_back(2), Some(&7));
            assert_eq!(buf.nth_back(3), Some(&8));
            assert_eq!(buf.nth_back(4), None);
        }

        #[test]
        fn index() {
            let mut buf = $new_buffer::<u32, 4>();
            assert_buf_eq!(buf, [] as [u32; 0]);

            assert!(std::panic::catch_unwind(|| buf[0]).is_err());
            assert!(std::panic::catch_unwind(|| buf[1]).is_err());
            assert!(std::panic::catch_unwind(|| buf[2]).is_err());
            assert!(std::panic::catch_unwind(|| buf[3]).is_err());
            assert!(std::panic::catch_unwind(|| buf[4]).is_err());
            assert!(std::panic::catch_unwind(|| buf[5]).is_err());

            buf.push_back(1);
            assert_buf_eq!(buf, [1]);
            assert_eq!(buf[0], 1);
            assert!(std::panic::catch_unwind(|| buf[1]).is_err());

            buf.push_back(2);
            assert_buf_eq!(buf, [1, 2]);
            assert_eq!(buf[0], 1);
            assert_eq!(buf[1], 2);
            assert!(std::panic::catch_unwind(|| buf[2]).is_err());

            buf.push_back(3);
            assert_buf_eq!(buf, [1, 2, 3]);
            assert_eq!(buf[0], 1);
            assert_eq!(buf[1], 2);
            assert_eq!(buf[2], 3);
            assert!(std::panic::catch_unwind(|| buf[3]).is_err());

            buf.push_back(4);
            assert_buf_eq!(buf, [1, 2, 3, 4]);
            assert_eq!(buf[0], 1);
            assert_eq!(buf[1], 2);
            assert_eq!(buf[2], 3);
            assert_eq!(buf[3], 4);
            assert!(std::panic::catch_unwind(|| buf[4]).is_err());

            buf.push_back(5);
            assert_buf_eq!(buf, [2, 3, 4, 5]);
            assert_eq!(buf[0], 2);
            assert_eq!(buf[1], 3);
            assert_eq!(buf[2], 4);
            assert_eq!(buf[3], 5);
            assert!(std::panic::catch_unwind(|| buf[4]).is_err());

            buf.push_back(6);
            assert_buf_eq!(buf, [3, 4, 5, 6]);
            assert_eq!(buf[0], 3);
            assert_eq!(buf[1], 4);
            assert_eq!(buf[2], 5);
            assert_eq!(buf[3], 6);
            assert!(std::panic::catch_unwind(|| buf[4]).is_err());

            buf.push_back(7);
            assert_buf_eq!(buf, [4, 5, 6, 7]);
            assert_eq!(buf[0], 4);
            assert_eq!(buf[1], 5);
            assert_eq!(buf[2], 6);
            assert_eq!(buf[3], 7);
            assert!(std::panic::catch_unwind(|| buf[4]).is_err());

            buf.push_back(8);
            assert_buf_eq!(buf, [5, 6, 7, 8]);
            assert_eq!(buf[0], 5);
            assert_eq!(buf[1], 6);
            assert_eq!(buf[2], 7);
            assert_eq!(buf[3], 8);
            assert!(std::panic::catch_unwind(|| buf[4]).is_err());
        }

        #[test]
        fn iter() {
            let buf = $new_buffer::<u32, 8>();
            let mut iter = buf.iter();
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from::<u32, 8, _>([1, 2, 3, 4]);
            let mut iter = buf.iter();
            assert_eq!(iter.next(), Some(&1));
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from::<u32, 8, _>([1, 2, 3, 4, 5, 6, 7, 8]);
            let mut iter = buf.iter();
            assert_eq!(iter.next(), Some(&1));
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&5));
            assert_eq!(iter.next(), Some(&6));
            assert_eq!(iter.next(), Some(&7));
            assert_eq!(iter.next(), Some(&8));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }

        #[test]
        fn iter_rev() {
            let buf = $new_buffer::<u32, 8>();
            let mut iter = buf.iter().rev();
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from::<u32, 8, _>([1, 2, 3, 4]);
            let mut iter = buf.iter().rev();
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&1));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from::<u32, 8, _>([1, 2, 3, 4, 5, 6, 7, 8]);
            let mut iter = buf.iter().rev();
            assert_eq!(iter.next(), Some(&8));
            assert_eq!(iter.next(), Some(&7));
            assert_eq!(iter.next(), Some(&6));
            assert_eq!(iter.next(), Some(&5));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&1));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }

        #[test]
        fn into_iter() {
            let buf = $new_buffer::<u32, 8>();
            let mut iter = buf.into_iter();
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from::<u32, 8, _>([1, 2, 3, 4]);
            let mut iter = buf.into_iter();
            assert_eq!(iter.next(), Some(1));
            assert_eq!(iter.next(), Some(2));
            assert_eq!(iter.next(), Some(3));
            assert_eq!(iter.next(), Some(4));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from::<u32, 8, _>([1, 2, 3, 4, 5, 6, 7, 8]);
            let mut iter = buf.into_iter();
            assert_eq!(iter.next(), Some(1));
            assert_eq!(iter.next(), Some(2));
            assert_eq!(iter.next(), Some(3));
            assert_eq!(iter.next(), Some(4));
            assert_eq!(iter.next(), Some(5));
            assert_eq!(iter.next(), Some(6));
            assert_eq!(iter.next(), Some(7));
            assert_eq!(iter.next(), Some(8));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }

        #[test]
        fn into_iter_rev() {
            let buf = $new_buffer::<u32, 8>();
            let mut iter = buf.into_iter().rev();
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from::<u32, 8, _>([1, 2, 3, 4]);
            let mut iter = buf.into_iter().rev();
            assert_eq!(iter.next(), Some(4));
            assert_eq!(iter.next(), Some(3));
            assert_eq!(iter.next(), Some(2));
            assert_eq!(iter.next(), Some(1));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from::<u32, 8, _>([1, 2, 3, 4, 5, 6, 7, 8]);
            let mut iter = buf.into_iter().rev();
            assert_eq!(iter.next(), Some(8));
            assert_eq!(iter.next(), Some(7));
            assert_eq!(iter.next(), Some(6));
            assert_eq!(iter.next(), Some(5));
            assert_eq!(iter.next(), Some(4));
            assert_eq!(iter.next(), Some(3));
            assert_eq!(iter.next(), Some(2));
            assert_eq!(iter.next(), Some(1));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }

        #[test]
        fn iter_mut() {
            let mut buf = $new_buffer::<u32, 8>();
            let mut iter = buf.iter_mut();
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let mut buf = $buffer_from::<u32, 8, _>([1, 2, 3, 4]);
            let mut iter = buf.iter_mut();
            assert_eq!(iter.next(), Some(&mut 1));
            assert_eq!(iter.next(), Some(&mut 2));
            assert_eq!(iter.next(), Some(&mut 3));
            assert_eq!(iter.next(), Some(&mut 4));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let mut buf = $buffer_from::<u32, 8, _>([1, 2, 3, 4, 5, 6, 7, 8]);
            let mut iter = buf.iter_mut();
            assert_eq!(iter.next(), Some(&mut 1));
            assert_eq!(iter.next(), Some(&mut 2));
            assert_eq!(iter.next(), Some(&mut 3));
            assert_eq!(iter.next(), Some(&mut 4));
            assert_eq!(iter.next(), Some(&mut 5));
            assert_eq!(iter.next(), Some(&mut 6));
            assert_eq!(iter.next(), Some(&mut 7));
            assert_eq!(iter.next(), Some(&mut 8));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }

        #[test]
        fn iter_mut_rev() {
            let mut buf = $new_buffer::<u32, 8>();
            let mut iter = buf.iter_mut().rev();
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let mut buf = $buffer_from::<u32, 8, _>([1, 2, 3, 4]);
            let mut iter = buf.iter_mut().rev();
            assert_eq!(iter.next(), Some(&mut 4));
            assert_eq!(iter.next(), Some(&mut 3));
            assert_eq!(iter.next(), Some(&mut 2));
            assert_eq!(iter.next(), Some(&mut 1));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let mut buf = $buffer_from::<u32, 8, _>([1, 2, 3, 4, 5, 6, 7, 8]);
            let mut iter = buf.iter_mut().rev();
            assert_eq!(iter.next(), Some(&mut 8));
            assert_eq!(iter.next(), Some(&mut 7));
            assert_eq!(iter.next(), Some(&mut 6));
            assert_eq!(iter.next(), Some(&mut 5));
            assert_eq!(iter.next(), Some(&mut 4));
            assert_eq!(iter.next(), Some(&mut 3));
            assert_eq!(iter.next(), Some(&mut 2));
            assert_eq!(iter.next(), Some(&mut 1));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }

        #[test]
        fn range() {
            let buf = $new_buffer::<char, 8>();
            let mut iter = buf.range(..);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range(..);
            assert_eq!(iter.next(), Some(&'a'));
            assert_eq!(iter.next(), Some(&'b'));
            assert_eq!(iter.next(), Some(&'c'));
            assert_eq!(iter.next(), Some(&'d'));
            assert_eq!(iter.next(), Some(&'e'));
            assert_eq!(iter.next(), Some(&'f'));
            assert_eq!(iter.next(), Some(&'g'));
            assert_eq!(iter.next(), Some(&'h'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range(5..);
            assert_eq!(iter.next(), Some(&'f'));
            assert_eq!(iter.next(), Some(&'g'));
            assert_eq!(iter.next(), Some(&'h'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range(..3);
            assert_eq!(iter.next(), Some(&'a'));
            assert_eq!(iter.next(), Some(&'b'));
            assert_eq!(iter.next(), Some(&'c'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range(..=2);
            assert_eq!(iter.next(), Some(&'a'));
            assert_eq!(iter.next(), Some(&'b'));
            assert_eq!(iter.next(), Some(&'c'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range(3..6);
            assert_eq!(iter.next(), Some(&'d'));
            assert_eq!(iter.next(), Some(&'e'));
            assert_eq!(iter.next(), Some(&'f'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range(3..=5);
            assert_eq!(iter.next(), Some(&'d'));
            assert_eq!(iter.next(), Some(&'e'));
            assert_eq!(iter.next(), Some(&'f'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range(0..0);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range((Bound::Excluded(4), Bound::Unbounded));
            assert_eq!(iter.next(), Some(&'f'));
            assert_eq!(iter.next(), Some(&'g'));
            assert_eq!(iter.next(), Some(&'h'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range((Bound::Excluded(2), Bound::Excluded(6)));
            assert_eq!(iter.next(), Some(&'d'));
            assert_eq!(iter.next(), Some(&'e'));
            assert_eq!(iter.next(), Some(&'f'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range((Bound::Excluded(2), Bound::Included(5)));
            assert_eq!(iter.next(), Some(&'d'));
            assert_eq!(iter.next(), Some(&'e'));
            assert_eq!(iter.next(), Some(&'f'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range((Bound::Excluded(2), Bound::Excluded(3)));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range((Bound::Excluded(2), Bound::Included(2)));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let buf = $buffer_from_iter::<char, 8, _>("abcdefghijkl".chars());
            let mut iter = buf.range(2..6);
            assert_eq!(iter.next(), Some(&'g'));
            assert_eq!(iter.next(), Some(&'h'));
            assert_eq!(iter.next(), Some(&'i'));
            assert_eq!(iter.next(), Some(&'j'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }

        #[test]
        fn range_mut() {
            let mut buf = $new_buffer::<char, 8>();
            let mut iter = buf.range_mut(..);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let mut buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range_mut(..);
            assert_eq!(iter.next(), Some(&mut 'a'));
            assert_eq!(iter.next(), Some(&mut 'b'));
            assert_eq!(iter.next(), Some(&mut 'c'));
            assert_eq!(iter.next(), Some(&mut 'd'));
            assert_eq!(iter.next(), Some(&mut 'e'));
            assert_eq!(iter.next(), Some(&mut 'f'));
            assert_eq!(iter.next(), Some(&mut 'g'));
            assert_eq!(iter.next(), Some(&mut 'h'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let mut buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range_mut(5..);
            assert_eq!(iter.next(), Some(&mut 'f'));
            assert_eq!(iter.next(), Some(&mut 'g'));
            assert_eq!(iter.next(), Some(&mut 'h'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let mut buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range_mut(..3);
            assert_eq!(iter.next(), Some(&mut 'a'));
            assert_eq!(iter.next(), Some(&mut 'b'));
            assert_eq!(iter.next(), Some(&mut 'c'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let mut buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range_mut(..=2);
            assert_eq!(iter.next(), Some(&mut 'a'));
            assert_eq!(iter.next(), Some(&mut 'b'));
            assert_eq!(iter.next(), Some(&mut 'c'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let mut buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range_mut(3..6);
            assert_eq!(iter.next(), Some(&mut 'd'));
            assert_eq!(iter.next(), Some(&mut 'e'));
            assert_eq!(iter.next(), Some(&mut 'f'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let mut buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range_mut(3..=5);
            assert_eq!(iter.next(), Some(&mut 'd'));
            assert_eq!(iter.next(), Some(&mut 'e'));
            assert_eq!(iter.next(), Some(&mut 'f'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let mut buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range_mut(0..0);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let mut buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range_mut((Bound::Excluded(4), Bound::Unbounded));
            assert_eq!(iter.next(), Some(&mut 'f'));
            assert_eq!(iter.next(), Some(&mut 'g'));
            assert_eq!(iter.next(), Some(&mut 'h'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let mut buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range_mut((Bound::Excluded(2), Bound::Excluded(6)));
            assert_eq!(iter.next(), Some(&mut 'd'));
            assert_eq!(iter.next(), Some(&mut 'e'));
            assert_eq!(iter.next(), Some(&mut 'f'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let mut buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range_mut((Bound::Excluded(2), Bound::Included(5)));
            assert_eq!(iter.next(), Some(&mut 'd'));
            assert_eq!(iter.next(), Some(&mut 'e'));
            assert_eq!(iter.next(), Some(&mut 'f'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let mut buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range_mut((Bound::Excluded(2), Bound::Excluded(3)));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let mut buf = $buffer_from_iter::<char, 8, _>("abcdefgh".chars());
            let mut iter = buf.range_mut((Bound::Excluded(2), Bound::Included(2)));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            let mut buf = $buffer_from_iter::<char, 8, _>("abcdefghijkl".chars());
            let mut iter = buf.range_mut(2..6);
            assert_eq!(iter.next(), Some(&mut 'g'));
            assert_eq!(iter.next(), Some(&mut 'h'));
            assert_eq!(iter.next(), Some(&mut 'i'));
            assert_eq!(iter.next(), Some(&mut 'j'));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }

        #[test]
        fn zero_capacity() {
            let mut buf = $new_buffer::<u32, 0>();
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.push_back(1);
            assert_buf_eq!(buf, [] as [u32; 0]);

            assert_eq!(buf.pop_back(), None);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.push_front(1);
            assert_buf_eq!(buf, [] as [u32; 0]);

            assert_eq!(buf.pop_front(), None);
            assert_buf_eq!(buf, [] as [u32; 0]);

            assert_eq!(buf.remove(0), None);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.extend(&[1, 2, 3]);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.extend_from_slice(&[1, 2, 3]);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.truncate_back(10);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.truncate_back(0);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.truncate_front(10);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.truncate_front(0);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.clear();
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.drain(..);
            assert_buf_eq!(buf, [] as [u32; 0]);
        }

        #[test]
        fn remove_on_empty() {
            let mut buf = $new_buffer::<u32, 10>();
            assert_buf_eq!(buf, [] as [u32; 0]);

            assert_eq!(buf.pop_back(), None);
            assert_buf_eq!(buf, [] as [u32; 0]);

            assert_eq!(buf.pop_front(), None);
            assert_buf_eq!(buf, [] as [u32; 0]);

            assert_eq!(buf.remove(0), None);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.truncate_back(10);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.truncate_back(0);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.truncate_front(10);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.truncate_front(0);
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.clear();
            assert_buf_eq!(buf, [] as [u32; 0]);
        }

        #[test]
        fn drop_contiguous() {
            let mut tracker = DropTracker::new();
            let mut buf = $new_buffer::<DropItem<i32>, 4>();
            assert_buf_eq!(buf, [] as [i32; 0]);

            buf.push_back(tracker.track(1));
            buf.push_back(tracker.track(2));
            assert_buf_eq!(buf, [1, 2]);
            assert!(is_contiguous(&buf));
            tracker.assert_all_alive([1, 2]);
            tracker.assert_fully_alive();

            drop(buf);

            tracker.assert_fully_dropped();
            tracker.assert_all_dropped([1, 2]);
        }

        #[test]
        fn drop_full_contiguous() {
            let mut tracker = DropTracker::new();
            let mut buf = $new_buffer::<DropItem<i32>, 4>();
            assert_buf_eq!(buf, [] as [i32; 0]);

            buf.push_back(tracker.track(1));
            buf.push_back(tracker.track(2));
            buf.push_back(tracker.track(3));
            buf.push_back(tracker.track(4));
            assert_buf_eq!(buf, [1, 2, 3, 4]);
            assert!(is_contiguous(&buf));
            tracker.assert_all_alive([1, 2, 3, 4]);
            tracker.assert_fully_alive();

            drop(buf);

            tracker.assert_fully_dropped();
            tracker.assert_all_dropped([1, 2, 3, 4]);
        }

        #[test]
        fn drop_full_disjoint() {
            let mut tracker = DropTracker::new();
            let mut buf = $new_buffer::<DropItem<i32>, 4>();
            assert_buf_eq!(buf, [] as [i32; 0]);

            buf.push_back(tracker.track(1));
            buf.push_back(tracker.track(2));
            buf.push_back(tracker.track(3));
            buf.push_back(tracker.track(4));
            buf.push_back(tracker.track(5));
            buf.push_back(tracker.track(6));
            assert_buf_eq!(buf, [3, 4, 5, 6]);
            assert!(!is_contiguous(&buf));
            tracker.assert_all_alive([3, 4, 5, 6]);
            tracker.assert_all_dropped([1, 2]);

            drop(buf);

            tracker.assert_fully_dropped();
            tracker.assert_all_dropped([1, 2, 3, 4, 5, 6]);
        }

        #[test]
        fn drop_disjoint() {
            let mut tracker = DropTracker::new();
            let mut buf = $new_buffer::<DropItem<i32>, 4>();
            assert_buf_eq!(buf, [] as [i32; 0]);

            buf.push_back(tracker.track(1));
            buf.push_back(tracker.track(2));
            buf.push_back(tracker.track(3));
            buf.push_back(tracker.track(4));
            buf.push_back(tracker.track(5));
            buf.push_back(tracker.track(6));
            buf.pop_back();
            assert_buf_eq!(buf, [3, 4, 5]);
            assert!(!is_contiguous(&buf));
            tracker.assert_all_alive([3, 4, 5]);
            tracker.assert_all_dropped([1, 2, 6]);

            drop(buf);

            tracker.assert_fully_dropped();
            tracker.assert_all_dropped([1, 2, 3, 4, 5, 6]);
        }

        #[test]
        fn drain_front() {
            // Fully consume the drain
            let mut tracker = DropTracker::new();
            let mut buf = $buffer_from_iter::<_, 10, _>(tracker.track_many([1, 2, 3, 4, 5, 6, 7]));
            let mut drain = buf.drain(..4);
            assert_eq!(drain.next().unwrap(), 1);
            assert_eq!(drain.next().unwrap(), 2);
            assert_eq!(drain.next().unwrap(), 3);
            assert_eq!(drain.next().unwrap(), 4);
            assert_eq!(drain.next(), None);
            assert_eq!(drain.next(), None);
            assert_eq!(drain.next(), None);
            drop(drain);
            assert_buf_eq!(buf, [5, 6, 7]);
            tracker.assert_all_alive([5, 6, 7]);
            tracker.assert_all_dropped([1, 2, 3, 4]);

            // Partially consume the drain
            let mut tracker = DropTracker::new();
            let mut buf = $buffer_from_iter::<_, 10, _>(tracker.track_many([1, 2, 3, 4, 5, 6, 7]));
            let mut drain = buf.drain(..4);
            assert_eq!(drain.next().unwrap(), 1);
            assert_eq!(drain.next().unwrap(), 2);
            drop(drain);
            assert_buf_eq!(buf, [5, 6, 7]);
            tracker.assert_all_alive([5, 6, 7]);
            tracker.assert_all_dropped([1, 2, 3, 4]);

            // Do not consume the drain
            let mut tracker = DropTracker::new();
            let mut buf = $buffer_from_iter::<_, 10, _>(tracker.track_many([1, 2, 3, 4, 5, 6, 7]));
            let _ = buf.drain(..4);
            assert_buf_eq!(buf, [5, 6, 7]);
            tracker.assert_all_alive([5, 6, 7]);
            tracker.assert_all_dropped([1, 2, 3, 4]);
        }

        #[test]
        fn drain_back() {
            // Fully consume the drain
            let mut tracker = DropTracker::new();
            let mut buf = $buffer_from_iter::<_, 10, _>(tracker.track_many([1, 2, 3, 4, 5, 6, 7]));
            let mut drain = buf.drain(3..);
            assert_eq!(drain.next().unwrap(), 4);
            assert_eq!(drain.next().unwrap(), 5);
            assert_eq!(drain.next().unwrap(), 6);
            assert_eq!(drain.next().unwrap(), 7);
            assert_eq!(drain.next(), None);
            assert_eq!(drain.next(), None);
            assert_eq!(drain.next(), None);
            drop(drain);
            assert_buf_eq!(buf, [1, 2, 3]);
            tracker.assert_all_alive([1, 2, 3]);
            tracker.assert_all_dropped([4, 5, 6, 7]);

            // Partially consume the drain
            let mut tracker = DropTracker::new();
            let mut buf = $buffer_from_iter::<_, 10, _>(tracker.track_many([1, 2, 3, 4, 5, 6, 7]));
            let mut drain = buf.drain(3..);
            assert_eq!(drain.next().unwrap(), 4);
            assert_eq!(drain.next().unwrap(), 5);
            drop(drain);
            assert_buf_eq!(buf, [1, 2, 3]);
            tracker.assert_all_alive([1, 2, 3]);
            tracker.assert_all_dropped([4, 5, 6, 7]);

            // Do not consume the drain
            let mut tracker = DropTracker::new();
            let mut buf = $buffer_from_iter::<_, 10, _>(tracker.track_many([1, 2, 3, 4, 5, 6, 7]));
            let _ = buf.drain(3..);
            assert_buf_eq!(buf, [1, 2, 3]);
            tracker.assert_all_alive([1, 2, 3]);
            tracker.assert_all_dropped([4, 5, 6, 7]);
        }

        #[test]
        fn drain_middle_contiguous() {
            // Fully consume the drain
            let mut tracker = DropTracker::new();
            let mut buf = $buffer_from_iter::<_, 10, _>(tracker.track_many([1, 2, 3, 4, 5, 6, 7]));
            assert!(is_contiguous(&buf));
            let mut drain = buf.drain(2..5);
            assert_eq!(drain.next().unwrap(), 3);
            assert_eq!(drain.next().unwrap(), 4);
            assert_eq!(drain.next().unwrap(), 5);
            assert_eq!(drain.next(), None);
            assert_eq!(drain.next(), None);
            assert_eq!(drain.next(), None);
            drop(drain);
            assert_buf_eq!(buf, [1, 2, 6, 7]);
            tracker.assert_all_alive([1, 2, 6, 7]);
            tracker.assert_all_dropped([3, 4, 5]);

            // Partially consume the drain
            let mut tracker = DropTracker::new();
            let mut buf = $buffer_from_iter::<_, 10, _>(tracker.track_many([1, 2, 3, 4, 5, 6, 7]));
            assert!(is_contiguous(&buf));
            let mut drain = buf.drain(2..5);
            assert_eq!(drain.next().unwrap(), 3);
            assert_eq!(drain.next().unwrap(), 4);
            drop(drain);
            assert_buf_eq!(buf, [1, 2, 6, 7]);
            tracker.assert_all_alive([1, 2, 6, 7]);
            tracker.assert_all_dropped([3, 4, 5]);

            // Do not consume the drain
            let mut tracker = DropTracker::new();
            let mut buf = $buffer_from_iter::<_, 10, _>(tracker.track_many([1, 2, 3, 4, 5, 6, 7]));
            assert!(is_contiguous(&buf));
            let _ = buf.drain(2..5);
            assert_buf_eq!(buf, [1, 2, 6, 7]);
            tracker.assert_all_alive([1, 2, 6, 7]);
            tracker.assert_all_dropped([3, 4, 5]);
        }

        #[test]
        fn drain_middle_disjoint() {
            // Fully consume the drain
            let mut tracker = DropTracker::new();
            let mut buf = $buffer_from_iter::<_, 10, _>(
                tracker.track_many([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
            );
            assert!(!is_contiguous(&buf));
            let mut drain = buf.drain(3..7);
            assert_eq!(drain.next().unwrap(), 9);
            assert_eq!(drain.next().unwrap(), 10);
            assert_eq!(drain.next().unwrap(), 11);
            assert_eq!(drain.next().unwrap(), 12);
            assert_eq!(drain.next(), None);
            assert_eq!(drain.next(), None);
            assert_eq!(drain.next(), None);
            drop(drain);
            assert_buf_eq!(buf, [6, 7, 8, 13, 14, 15]);
            tracker.assert_all_alive([6, 7, 8, 13, 14, 15]);
            tracker.assert_all_dropped([9, 10, 11, 12]);

            // Partially consume the drain
            let mut tracker = DropTracker::new();
            let mut buf = $buffer_from_iter::<_, 10, _>(
                tracker.track_many([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
            );
            assert!(!is_contiguous(&buf));
            let mut drain = buf.drain(3..7);
            assert_eq!(drain.next().unwrap(), 9);
            assert_eq!(drain.next().unwrap(), 10);
            drop(drain);
            assert_buf_eq!(buf, [6, 7, 8, 13, 14, 15]);
            tracker.assert_all_alive([6, 7, 8, 13, 14, 15]);
            tracker.assert_all_dropped([9, 10, 11, 12]);

            // Do not consume the drain
            let mut tracker = DropTracker::new();
            let mut buf = $buffer_from_iter::<_, 10, _>(
                tracker.track_many([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
            );
            assert!(!is_contiguous(&buf));
            let _ = buf.drain(3..7);
            assert_buf_eq!(buf, [6, 7, 8, 13, 14, 15]);
            tracker.assert_all_alive([6, 7, 8, 13, 14, 15]);
            tracker.assert_all_dropped([9, 10, 11, 12]);
        }

        #[test]
        fn drain_full() {
            // Fully consume the drain
            let mut tracker = DropTracker::new();
            let mut buf = $buffer_from_iter::<_, 10, _>(tracker.track_many([1, 2, 3, 4]));
            let mut drain = buf.drain(..);
            assert_eq!(drain.next().unwrap(), 1);
            assert_eq!(drain.next().unwrap(), 2);
            assert_eq!(drain.next().unwrap(), 3);
            assert_eq!(drain.next().unwrap(), 4);
            assert_eq!(drain.next(), None);
            assert_eq!(drain.next(), None);
            assert_eq!(drain.next(), None);
            drop(drain);
            assert_buf_eq!(buf, [] as [i32; 0]);
            tracker.assert_fully_dropped();

            // Partially consume the drain
            let mut tracker = DropTracker::new();
            let mut buf = $buffer_from_iter::<_, 10, _>(tracker.track_many([1, 2, 3, 4]));
            let mut drain = buf.drain(..);
            assert_eq!(drain.next().unwrap(), 1);
            assert_eq!(drain.next().unwrap(), 2);
            drop(drain);
            assert_buf_eq!(buf, [] as [i32; 0]);
            tracker.assert_fully_dropped();

            // Do not consume the drain
            let mut tracker = DropTracker::new();
            let mut buf = $buffer_from_iter::<_, 10, _>(tracker.track_many([1, 2, 3, 4]));
            let _ = buf.drain(..);
            assert_buf_eq!(buf, [] as [i32; 0]);
            tracker.assert_fully_dropped();
        }

        #[test]
        fn drain_full_no_items() {
            // Fully consume the drain
            let mut buf = $new_buffer::<i32, 10>();
            let mut drain = buf.drain(..);
            assert_eq!(drain.next(), None);
            assert_eq!(drain.next(), None);
            assert_eq!(drain.next(), None);
            drop(drain);
            assert_buf_eq!(buf, [] as [i32; 0]);

            // Do not consume the drain
            let mut buf = $new_buffer::<i32, 10>();
            let _ = buf.drain(..);
            assert_buf_eq!(buf, [] as [i32; 0]);
        }

        #[test]
        fn drain_empty() {
            let mut tracker = DropTracker::new();
            let mut buf = $buffer_from_iter::<_, 10, _>(tracker.track_many([1, 2, 3, 4]));
            let mut drain = buf.drain(0..0);
            assert_eq!(drain.next(), None);
            assert_eq!(drain.next(), None);
            assert_eq!(drain.next(), None);
            drop(drain);
            assert_buf_eq!(buf, [1, 2, 3, 4]);
            tracker.assert_fully_alive();
        }
    };
}

pub(crate) use assert_buf_eq;
pub(crate) use define_tests;
