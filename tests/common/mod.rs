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

/// Asserts that the items in the specified buffer are spread over two slices with the specified
/// elements.
macro_rules! assert_buf_slices_eq {
    ( $buf:ident , [ $( $front_elems:tt )* ] , [ $( $back_elems:tt )* ] ) => {
        let mut expected_front = [ $($front_elems)* ];
        let mut expected_back = [ $($back_elems)* ];
        assert_eq!($buf.as_slices(), (&expected_front[..], &expected_back[..]));
        assert_eq!($buf.as_mut_slices(), (&mut expected_front[..], &mut expected_back[..]));
    }
}

macro_rules! define_tests {
    ( $new_buffer:ident , $buffer_from:ident , $buffer_from_iter:ident $(,)? ) => {
        use core::cell::RefCell;
        use core::ops::Bound;
        use drop_tracker::DropItem;
        use drop_tracker::DropTracker;
        use $crate::common::assert_buf_eq;
        use $crate::common::assert_buf_slices_eq;
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

        #[test]
        fn eq_contiguous() {
            let mut buf1 = $buffer_from_iter::<_, 5, _>([1, 2, 3]);
            let mut buf2 = $buffer_from_iter::<_, 5, _>([1, 2, 3]);
            assert!(is_contiguous(&buf1));
            assert!(is_contiguous(&buf2));
            assert_eq!(buf1, buf2);

            buf1.push_back(4);
            assert!(is_contiguous(&buf1));
            assert!(is_contiguous(&buf2));
            assert_ne!(buf1, buf2);

            buf2.push_back(4);
            assert!(is_contiguous(&buf1));
            assert!(is_contiguous(&buf2));
            assert_eq!(buf1, buf2);
        }

        #[test]
        fn eq_disjoint() {
            let mut buf1 = $buffer_from_iter::<_, 5, _>([1, 2, 3, 4, 5]);
            let mut buf2 = $buffer_from_iter::<_, 5, _>([0, 1, 2, 3, 4]);

            buf1.push_back(6);
            buf2.push_back(5);
            assert!(!is_contiguous(&buf1));
            assert!(!is_contiguous(&buf2));
            assert_ne!(buf1, buf2);

            buf2.push_back(6);
            assert!(!is_contiguous(&buf1));
            assert!(!is_contiguous(&buf2));
            assert_eq!(buf1, buf2);

            buf1.push_back(7);
            buf2.push_back(7);
            assert!(!is_contiguous(&buf1));
            assert!(!is_contiguous(&buf2));
            assert_eq!(buf1, buf2);

            buf1.push_back(8);
            buf2.push_back(8);
            assert!(!is_contiguous(&buf1));
            assert!(!is_contiguous(&buf2));
            assert_eq!(buf1, buf2);

            buf1.push_back(9);
            buf2.push_back(9);
            assert!(!is_contiguous(&buf1));
            assert!(is_contiguous(&buf2));
            assert_eq!(buf1, buf2);

            buf1.push_back(10);
            buf2.push_back(10);
            assert!(is_contiguous(&buf1));
            assert!(!is_contiguous(&buf2));
            assert_eq!(buf1, buf2);
        }

        #[test]
        fn eq_mixed_types() {
            let mut buf = $buffer_from_iter::<u32, 5, _>([1, 2, 3]);
            let mut other_buf = $buffer_from_iter::<u32, 20, _>([1, 2, 3]);
            let mut other_arr = [1, 2, 3];

            assert_eq!(buf, buf);
            assert_eq!(buf, other_buf);
            assert_eq!(buf, other_buf.as_circular_buffer());
            assert_eq!(buf, other_buf.as_mut_circular_buffer());
            assert_eq!(buf, other_arr);
            assert_eq!(buf, other_arr.as_slice());
            assert_eq!(buf, other_arr.as_mut_slice());

            assert_eq!(buf.as_circular_buffer(), buf);
            assert_eq!(buf.as_circular_buffer(), other_buf);
            assert_eq!(buf.as_circular_buffer(), other_buf.as_circular_buffer());
            assert_eq!(buf.as_circular_buffer(), other_buf.as_mut_circular_buffer());
            assert_eq!(buf.as_circular_buffer(), other_arr);
            assert_eq!(buf.as_circular_buffer(), other_arr.as_slice());
            assert_eq!(buf.as_circular_buffer(), other_arr.as_mut_slice());

            assert_eq!(buf.as_mut_circular_buffer(), other_buf);
            assert_eq!(buf.as_mut_circular_buffer(), other_buf.as_circular_buffer());
            assert_eq!(
                buf.as_mut_circular_buffer(),
                other_buf.as_mut_circular_buffer()
            );
            assert_eq!(buf.as_mut_circular_buffer(), other_arr);
            assert_eq!(buf.as_mut_circular_buffer(), other_arr.as_slice());
            assert_eq!(buf.as_mut_circular_buffer(), other_arr.as_mut_slice());
        }

        #[test]
        fn extend() {
            let mut buf = $new_buffer::<u32, 4>();
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.extend([] as [u32; 0]);
            assert_buf_eq!(buf, [] as [u32; 0]);
            buf.extend([1]);
            assert_buf_eq!(buf, [1]);
            buf.extend([2, 3]);
            assert_buf_eq!(buf, [1, 2, 3]);
            buf.extend([4, 5, 6]);
            assert_buf_eq!(buf, [3, 4, 5, 6]);
            buf.extend([7, 8, 9, 10]);
            assert_buf_eq!(buf, [7, 8, 9, 10]);
            buf.extend([11, 12, 13, 14, 15]);
            assert_buf_eq!(buf, [12, 13, 14, 15]);
        }

        #[test]
        fn extend_ref() {
            let mut buf = $new_buffer::<u32, 4>();
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.extend([].iter());
            assert_buf_eq!(buf, [] as [u32; 0]);
            buf.extend([1].iter());
            assert_buf_eq!(buf, [1]);
            buf.extend([2, 3].iter());
            assert_buf_eq!(buf, [1, 2, 3]);
            buf.extend([4, 5, 6].iter());
            assert_buf_eq!(buf, [3, 4, 5, 6]);
            buf.extend([7, 8, 9, 10].iter());
            assert_buf_eq!(buf, [7, 8, 9, 10]);
            buf.extend([11, 12, 13, 14, 15].iter());
            assert_buf_eq!(buf, [12, 13, 14, 15]);
        }

        #[test]
        fn extend_from_slice() {
            let mut buf = $new_buffer::<u32, 4>();
            assert_buf_eq!(buf, [] as [u32; 0]);

            buf.extend_from_slice(&[][..]);
            assert_buf_eq!(buf, [] as [u32; 0]);
            buf.extend_from_slice(&[1][..]);
            assert_buf_eq!(buf, [1]);
            buf.extend_from_slice(&[2, 3][..]);
            assert_buf_eq!(buf, [1, 2, 3]);
            buf.extend_from_slice(&[4, 5, 6][..]);
            assert_buf_eq!(buf, [3, 4, 5, 6]);
            buf.extend_from_slice(&[7, 8, 9, 10][..]);
            assert_buf_eq!(buf, [7, 8, 9, 10]);
            buf.extend_from_slice(&[11, 12, 13, 14, 15][..]);
            assert_buf_eq!(buf, [12, 13, 14, 15]);
        }

        #[test]
        fn extend_from_slice_unwind_safety() {
            thread_local! {
                static TRACKER: RefCell<DropTracker<String>> = RefCell::new(DropTracker::new());
            }

            #[derive(Debug)]
            struct FaultyClonable {
                drop_item: DropItem<String>,
                panic_on_clone: bool,
            }

            impl Clone for FaultyClonable {
                fn clone(&self) -> Self {
                    if self.panic_on_clone {
                        panic!("clone failed :(");
                    } else {
                        Self {
                            drop_item: TRACKER.with_borrow_mut(|tracker| {
                                tracker.track(format!("clone of {}", self.drop_item))
                            }),
                            panic_on_clone: false,
                        }
                    }
                }
            }

            let array = TRACKER.with_borrow_mut(|tracker| {
                [
                    FaultyClonable {
                        drop_item: tracker.track("a".to_string()),
                        panic_on_clone: false,
                    },
                    FaultyClonable {
                        drop_item: tracker.track("b".to_string()),
                        panic_on_clone: false,
                    },
                    FaultyClonable {
                        drop_item: tracker.track("c".to_string()),
                        panic_on_clone: true,
                    },
                    FaultyClonable {
                        drop_item: tracker.track("d".to_string()),
                        panic_on_clone: false,
                    },
                ]
            });

            let mut buf = $new_buffer::<FaultyClonable, 4>();

            let res = std::panic::catch_unwind(move || buf.extend_from_slice(&array));
            assert!(res.is_err());

            TRACKER.with_borrow(|tracker| {
                tracker.assert_dropped("clone of a");
                tracker.assert_dropped("clone of b");
                assert!(!tracker.is_tracked("clone of c"));
                assert!(!tracker.is_tracked("clone of d"));
            });
        }

        #[test]
        fn fill_efficiency() {
            #[derive(Default, Debug)]
            struct Cloneable {
                num_clones: RefCell<usize>,
                is_clone: bool,
            }

            impl Clone for Cloneable {
                fn clone(&self) -> Self {
                    if self.is_clone {
                        panic!("cannot create clone of another clone");
                    }
                    *self.num_clones.borrow_mut() += 1;
                    Self {
                        num_clones: RefCell::default(),
                        is_clone: true,
                    }
                }
            }

            let mut buf = $new_buffer::<Cloneable, 6>();

            buf.fill(Cloneable::default());
            assert_eq!(buf.len(), buf.capacity());

            // The last element should be the original `value` that we passed. As such, the number of
            // clones created should be `len - 1`
            assert_eq!(*buf.back().unwrap().num_clones.borrow(), buf.len() - 1);

            // Only the last element should have been cloned; the other elements should have not been
            // cloned
            for elem in buf.iter().take(buf.len() - 1) {
                assert_eq!(*elem.num_clones.borrow(), 0);
            }
        }

        #[test]
        fn fill_unwind_safety() {
            thread_local! {
                static TRACKER: RefCell<DropTracker<String>> = RefCell::new(DropTracker::new());
            }

            #[derive(Debug)]
            struct FaultyClonable {
                drop_item: DropItem<String>,
                num_clones: RefCell<usize>,
                panic_at: usize,
            }

            impl Clone for FaultyClonable {
                fn clone(&self) -> Self {
                    *self.num_clones.borrow_mut() += 1;
                    let num_clones = *self.num_clones.borrow();
                    if num_clones >= self.panic_at {
                        panic!("clone failed :(");
                    }
                    Self {
                        drop_item: TRACKER.with_borrow_mut(|tracker| {
                            tracker.track(format!("clone #{} of {}", num_clones, self.drop_item))
                        }),
                        num_clones: RefCell::default(),
                        panic_at: self.panic_at,
                    }
                }
            }

            let mut buf = $new_buffer::<FaultyClonable, 6>();

            let value = FaultyClonable {
                drop_item: TRACKER.with_borrow_mut(|tracker| tracker.track("value".to_string())),
                num_clones: RefCell::default(),
                panic_at: 4,
            };
            let res = std::panic::catch_unwind(move || buf.fill(value));
            assert!(res.is_err());

            TRACKER.with_borrow(|tracker| {
                tracker.assert_dropped("value");
                tracker.assert_dropped("clone #1 of value");
                tracker.assert_dropped("clone #2 of value");
                tracker.assert_dropped("clone #3 of value");
                assert!(!tracker.is_tracked("clone #4 of value"));
                assert!(!tracker.is_tracked("clone #5 of value"));
            });
        }

        #[test]
        fn fill_with_unwind_safety() {
            thread_local! {
                static TRACKER: RefCell<DropTracker<u32>> = RefCell::new(DropTracker::new());
            }

            let mut buf = $new_buffer::<DropItem<u32>, 6>();

            let res = std::panic::catch_unwind(move || {
                let mut counter = 0u32;
                buf.fill_with(|| {
                    counter += 1;
                    if counter > 4 {
                        panic!("closure failed :(");
                    }
                    TRACKER.with_borrow_mut(|tracker| tracker.track(counter))
                })
            });
            assert!(res.is_err());

            TRACKER.with_borrow(|tracker| {
                tracker.assert_dropped(&1);
                tracker.assert_dropped(&2);
                tracker.assert_dropped(&3);
                tracker.assert_dropped(&4);
                assert!(!tracker.is_tracked(&5));
                assert!(!tracker.is_tracked(&6));
            });
        }

        #[test]
        fn make_contiguous_not_full() {
            let mut buf = $buffer_from::<u32, 4, _>([1, 2]);
            assert_buf_slices_eq!(buf, [1, 2], []);

            assert_eq!(buf.make_contiguous(), &mut [1, 2]);
            assert_buf_slices_eq!(buf, [1, 2], []);
            assert_buf_eq!(buf, [1, 2]);

            buf.extend([3, 4, 5]);
            buf.truncate_front(2);
            assert_buf_slices_eq!(buf, [4], [5]);
            assert_eq!(buf.make_contiguous(), &mut [4, 5]);
            assert_buf_slices_eq!(buf, [4, 5], []);
            assert_buf_eq!(buf, [4, 5]);
        }

        #[test]
        fn make_contiguous_full() {
            let mut buf = $buffer_from::<u32, 4, _>([1, 2, 3, 4]);
            assert_buf_slices_eq!(buf, [1, 2, 3, 4], []);

            assert_eq!(buf.make_contiguous(), &mut [1, 2, 3, 4]);
            assert_buf_slices_eq!(buf, [1, 2, 3, 4], []);
            assert_buf_eq!(buf, [1, 2, 3, 4]);

            buf.push_back(5);
            assert_buf_slices_eq!(buf, [2, 3, 4], [5]);
            assert_eq!(buf.make_contiguous(), &mut [2, 3, 4, 5]);
            assert_buf_slices_eq!(buf, [2, 3, 4, 5], []);
            assert_buf_eq!(buf, [2, 3, 4, 5]);

            buf.extend([6, 7]);
            assert_buf_slices_eq!(buf, [4, 5], [6, 7]);
            assert_eq!(buf.make_contiguous(), &mut [4, 5, 6, 7]);
            assert_buf_slices_eq!(buf, [4, 5, 6, 7], []);
            assert_buf_eq!(buf, [4, 5, 6, 7]);

            buf.extend([8, 9, 10]);
            assert_buf_slices_eq!(buf, [7], [8, 9, 10]);
            assert_eq!(buf.make_contiguous(), &mut [7, 8, 9, 10]);
            assert_buf_slices_eq!(buf, [7, 8, 9, 10], []);
            assert_buf_eq!(buf, [7, 8, 9, 10]);
        }

        #[test]
        fn clone() {
            let mut buf = $new_buffer::<u32, 4>();
            assert_eq!(buf, buf.clone());

            buf.extend_from_slice(&[][..]);
            assert_eq!(buf, buf.clone());
            buf.extend_from_slice(&[1][..]);
            assert_eq!(buf, buf.clone());
            buf.extend_from_slice(&[2, 3][..]);
            assert_eq!(buf, buf.clone());
            buf.extend_from_slice(&[4, 5, 6][..]);
            assert_eq!(buf, buf.clone());
            buf.extend_from_slice(&[7, 8, 9, 10][..]);
            assert_eq!(buf, buf.clone());
            buf.extend_from_slice(&[11, 12, 13, 14, 15][..]);
            assert_eq!(buf, buf.clone());
        }

        #[test]
        #[cfg(feature = "std")]
        fn hash() {
            use circular_buffer::CircularBuffer;
            use core::hash::Hash;
            use core::hash::Hasher;
            use std::collections::hash_map::DefaultHasher;

            fn hash<T: Hash>(buf: &CircularBuffer<T>) -> u64 {
                let mut hasher = DefaultHasher::new();
                buf.hash(&mut hasher);
                hasher.finish()
            }

            let hash_empty = hash(&$new_buffer::<u32, 0>());
            assert_eq!(hash_empty, hash(&$new_buffer::<u32, 0>()));
            assert_eq!(hash_empty, hash(&$new_buffer::<u32, 2>()));
            assert_eq!(hash_empty, hash(&$new_buffer::<u32, 4>()));
            assert_eq!(hash_empty, hash(&$new_buffer::<u32, 8>()));

            let hash_1 = hash(&$buffer_from::<u32, 1, _>([1]));
            assert_ne!(hash_1, hash_empty);
            assert_eq!(hash_1, hash(&$buffer_from::<u32, 2, _>([1])));
            assert_eq!(hash_1, hash(&$buffer_from::<u32, 4, _>([1])));
            assert_eq!(hash_1, hash(&$buffer_from::<u32, 8, _>([1])));

            let hash_2 = hash(&$buffer_from::<u32, 2, _>([1, 2]));
            assert_ne!(hash_2, hash_empty);
            assert_ne!(hash_2, hash_1);
            assert_eq!(hash_2, hash(&$buffer_from::<u32, 4, _>([1, 2])));
            assert_eq!(hash_2, hash(&$buffer_from::<u32, 8, _>([1, 2])));

            let hash_4 = hash(&$buffer_from::<u32, 4, _>([1, 2, 3, 4]));
            assert_ne!(hash_4, hash_empty);
            assert_ne!(hash_4, hash_1);
            assert_ne!(hash_4, hash_2);
            assert_eq!(hash_4, hash(&$buffer_from::<u32, 4, _>([1, 2, 3, 4])));
            assert_eq!(hash_4, hash(&$buffer_from::<u32, 8, _>([1, 2, 3, 4])));
        }

        #[test]
        fn debug() {
            let mut buf = $new_buffer::<u32, 4>();
            assert_buf_eq!(buf, [] as [u32; 0]);
            assert_eq!(format!("{:?}", buf), "[_, _, _, _]");
            assert_eq!(format!("{:x?}", buf), "[_, _, _, _]");
            assert_eq!(format!("{:X?}", buf), "[_, _, _, _]");

            buf.push_back(10);
            assert_buf_eq!(buf, [10]);
            assert_eq!(format!("{:?}", buf), "[10, _, _, _]");
            assert_eq!(format!("{:x?}", buf), "[a, _, _, _]");
            assert_eq!(format!("{:X?}", buf), "[A, _, _, _]");

            buf.push_back(20);
            assert_buf_eq!(buf, [10, 20]);
            assert_eq!(format!("{:?}", buf), "[10, 20, _, _]");
            assert_eq!(format!("{:x?}", buf), "[a, 14, _, _]");
            assert_eq!(format!("{:X?}", buf), "[A, 14, _, _]");

            buf.push_back(30);
            assert_buf_eq!(buf, [10, 20, 30]);
            assert_eq!(format!("{:?}", buf), "[10, 20, 30, _]");
            assert_eq!(format!("{:x?}", buf), "[a, 14, 1e, _]");
            assert_eq!(format!("{:X?}", buf), "[A, 14, 1E, _]");

            buf.push_back(40);
            assert_buf_eq!(buf, [10, 20, 30, 40]);
            assert_eq!(format!("{:?}", buf), "[10, 20, 30, 40]");
            assert_eq!(format!("{:x?}", buf), "[a, 14, 1e, 28]");
            assert_eq!(format!("{:X?}", buf), "[A, 14, 1E, 28]");

            buf.push_back(50);
            assert_buf_eq!(buf, [20, 30, 40, 50]);
            assert_eq!(format!("{:?}", buf), "[20, 30, 40, 50]");
            assert_eq!(format!("{:x?}", buf), "[14, 1e, 28, 32]");
            assert_eq!(format!("{:X?}", buf), "[14, 1E, 28, 32]");

            buf.push_back(60);
            assert_buf_eq!(buf, [30, 40, 50, 60]);
            assert_eq!(format!("{:?}", buf), "[30, 40, 50, 60]");
            assert_eq!(format!("{:x?}", buf), "[1e, 28, 32, 3c]");
            assert_eq!(format!("{:X?}", buf), "[1E, 28, 32, 3C]");
        }

        #[cfg(feature = "std")]
        mod std_io {
            use super::$new_buffer;
            use std::io::BufRead;
            use std::io::Read;
            use std::io::Write;

            #[test]
            fn write() {
                let mut buf = $new_buffer::<u8, 4>();
                assert_eq!(buf, [] as [u8; 0]);

                assert!(write!(&mut buf, "hello").is_ok());
                assert_eq!(buf, [b'e', b'l', b'l', b'o']);
                assert!(write!(&mut buf, "world").is_ok());
                assert_eq!(buf, [b'o', b'r', b'l', b'd']);
            }

            #[test]
            fn read() {
                fn read_all<R: Read>(mut buf: R) -> Vec<u8> {
                    let mut vec = Vec::new();
                    buf.read_to_end(&mut vec).expect("read failed");
                    vec
                }

                let mut buf = $new_buffer::<u8, 4>();
                assert_eq!(buf, [] as [u8; 0]);
                assert_eq!(read_all(&mut buf), []);
                assert_eq!(buf, [] as [u8; 0]);

                buf.push_back(b'a');
                buf.push_back(b'b');
                assert_eq!(buf, [b'a', b'b']);
                assert_eq!(read_all(&mut buf), [b'a', b'b']);
                assert_eq!(buf, [] as [u8; 0]);

                buf.push_back(b'c');
                buf.push_back(b'd');
                buf.push_back(b'e');
                buf.push_back(b'f');
                assert_eq!(buf, [b'c', b'd', b'e', b'f']);
                assert_eq!(read_all(&mut buf), [b'c', b'd', b'e', b'f']);
                assert_eq!(buf, [] as [u8; 0]);
            }

            #[test]
            fn read_buf() {
                let mut buf = $new_buffer::<u8, 4>();
                assert_eq!(buf, [] as [u8; 0]);
                assert_eq!(buf.fill_buf().unwrap(), b"");

                buf.push_back(b'a');
                buf.push_back(b'b');
                assert_eq!(buf, [b'a', b'b']);
                assert_eq!(buf.fill_buf().unwrap(), b"ab");

                buf.push_back(b'c');
                buf.push_back(b'd');
                buf.push_back(b'e');
                buf.push_back(b'f');
                assert_eq!(buf, [b'c', b'd', b'e', b'f']);
                assert_eq!(buf.fill_buf().unwrap(), b"cd");

                buf.consume(2);
                assert_eq!(buf.fill_buf().unwrap(), b"ef");

                buf.consume(2);
                assert_eq!(buf.fill_buf().unwrap(), b"");

                buf.consume(2);
                assert_eq!(buf.fill_buf().unwrap(), b"");
            }
        }

        #[cfg(feature = "embedded-io")]
        mod embedded_io {
            use super::$new_buffer;
            use embedded_io::BufRead;
            use embedded_io::Read;
            use embedded_io::Write;

            #[test]
            fn write() {
                let mut buf = $new_buffer::<u8, 4>();
                assert_eq!(buf, [] as [u8; 0]);

                assert!(write!(&mut buf, "hello").is_ok());
                assert_eq!(buf, [b'e', b'l', b'l', b'o']);
                assert!(write!(&mut buf, "world").is_ok());
                assert_eq!(buf, [b'o', b'r', b'l', b'd']);
            }

            #[test]
            fn read() {
                fn read_all<R: Read>(mut buf: R) -> Vec<u8> {
                    let mut vec = Vec::new();
                    loop {
                        let mut tmp = [0u8; 4];
                        let size = buf.read(&mut tmp[..]).expect("read failed");
                        if size == 0 {
                            break;
                        }
                        vec.extend_from_slice(&tmp[..size]);
                    }
                    vec
                }

                let mut buf = $new_buffer::<u8, 4>();
                assert_eq!(buf, [] as [u8; 0]);
                assert_eq!(read_all(&mut buf), []);
                assert_eq!(buf, [] as [u8; 0]);

                buf.push_back(b'a');
                buf.push_back(b'b');
                assert_eq!(buf, [b'a', b'b']);
                assert_eq!(read_all(&mut buf), [b'a', b'b']);
                assert_eq!(buf, [] as [u8; 0]);

                buf.push_back(b'c');
                buf.push_back(b'd');
                buf.push_back(b'e');
                buf.push_back(b'f');
                assert_eq!(buf, [b'c', b'd', b'e', b'f']);
                assert_eq!(read_all(&mut buf), [b'c', b'd', b'e', b'f']);
                assert_eq!(buf, [] as [u8; 0]);
            }

            #[test]
            fn read_buf() {
                let mut buf = $new_buffer::<u8, 4>();
                assert_eq!(buf, [] as [u8; 0]);
                assert_eq!(buf.fill_buf().unwrap(), b"");

                buf.push_back(b'a');
                buf.push_back(b'b');
                assert_eq!(buf, [b'a', b'b']);
                assert_eq!(buf.fill_buf().unwrap(), b"ab");

                buf.push_back(b'c');
                buf.push_back(b'd');
                buf.push_back(b'e');
                buf.push_back(b'f');
                assert_eq!(buf, [b'c', b'd', b'e', b'f']);
                assert_eq!(buf.fill_buf().unwrap(), b"cd");

                buf.consume(2);
                assert_eq!(buf.fill_buf().unwrap(), b"ef");

                buf.consume(2);
                assert_eq!(buf.fill_buf().unwrap(), b"");

                buf.consume(2);
                assert_eq!(buf.fill_buf().unwrap(), b"");
            }
        }

        #[cfg(feature = "embedded-io-async")]
        mod embedded_io_async {
            use super::$new_buffer;
            use embedded_io_async::BufRead;
            use embedded_io_async::Read;
            use embedded_io_async::Write;

            #[test]
            fn write() {
                futures_lite::future::block_on(async {
                    let mut buf = $new_buffer::<u8, 4>();
                    assert_eq!(buf, [] as [u8; 0]);

                    assert!(buf.write_all(b"hello").await.is_ok());
                    assert_eq!(buf, [b'e', b'l', b'l', b'o']);
                    assert!(buf.write_all(b"world").await.is_ok());
                    assert_eq!(buf, [b'o', b'r', b'l', b'd']);
                });
            }

            #[test]
            fn read() {
                futures_lite::future::block_on(async {
                    async fn read_all<R: Read>(mut buf: R) -> Vec<u8> {
                        let mut vec = Vec::new();
                        loop {
                            let mut tmp = [0u8; 4];
                            let size = buf.read(&mut tmp[..]).await.expect("read failed");
                            if size == 0 {
                                break;
                            }
                            vec.extend_from_slice(&tmp[..size]);
                        }
                        vec
                    }

                    let mut buf = $new_buffer::<u8, 4>();
                    assert_eq!(buf, [] as [u8; 0]);
                    assert_eq!(read_all(&mut buf).await, []);
                    assert_eq!(buf, [] as [u8; 0]);

                    buf.push_back(b'a');
                    buf.push_back(b'b');
                    assert_eq!(buf, [b'a', b'b']);
                    assert_eq!(read_all(&mut buf).await, [b'a', b'b']);
                    assert_eq!(buf, [] as [u8; 0]);

                    buf.push_back(b'c');
                    buf.push_back(b'd');
                    buf.push_back(b'e');
                    buf.push_back(b'f');
                    assert_eq!(buf, [b'c', b'd', b'e', b'f']);
                    assert_eq!(read_all(&mut buf).await, [b'c', b'd', b'e', b'f']);
                    assert_eq!(buf, [] as [u8; 0]);
                });
            }

            #[test]
            fn read_buf() {
                futures_lite::future::block_on(async {
                    let mut buf = $new_buffer::<u8, 4>();
                    assert_eq!(buf, [] as [u8; 0]);
                    assert_eq!(buf.fill_buf().await.unwrap(), b"");

                    buf.push_back(b'a');
                    buf.push_back(b'b');
                    assert_eq!(buf, [b'a', b'b']);
                    assert_eq!(buf.fill_buf().await.unwrap(), b"ab");

                    buf.push_back(b'c');
                    buf.push_back(b'd');
                    buf.push_back(b'e');
                    buf.push_back(b'f');
                    assert_eq!(buf, [b'c', b'd', b'e', b'f']);
                    assert_eq!(buf.fill_buf().await.unwrap(), b"cd");

                    buf.consume(2);
                    assert_eq!(buf.fill_buf().await.unwrap(), b"ef");

                    buf.consume(2);
                    assert_eq!(buf.fill_buf().await.unwrap(), b"");

                    buf.consume(2);
                    assert_eq!(buf.fill_buf().await.unwrap(), b"");
                });
            }
        }
    };
}

pub(crate) use assert_buf_eq;
pub(crate) use assert_buf_slices_eq;
pub(crate) use define_tests;
