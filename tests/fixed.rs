// Copyright © 2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

mod common;

use circular_buffer::FixedCircularBuffer;

#[must_use]
fn fixed_circular_buffer<T, const N: usize>() -> FixedCircularBuffer<T, N> {
    FixedCircularBuffer::<T, N>::new()
}

#[must_use]
fn fixed_circular_buffer_from<T, const N: usize, I>(input: I) -> FixedCircularBuffer<T, N>
where
    FixedCircularBuffer<T, N>: From<I>,
{
    FixedCircularBuffer::<T, N>::from(input)
}

#[must_use]
fn fixed_circular_buffer_from_iter<T, const N: usize, I>(input: I) -> FixedCircularBuffer<T, N>
where
    I: IntoIterator<Item = T>,
{
    FixedCircularBuffer::<T, N>::from_iter(input)
}

#[must_use]
#[cfg(feature = "std")]
fn fixed_circular_buffer_boxed<T, const N: usize>() -> Box<FixedCircularBuffer<T, N>> {
    FixedCircularBuffer::<T, N>::boxed()
}

#[cfg(not(feature = "std"))]
#[allow(dead_code)]
#[allow(clippy::extra_unused_type_parameters)]
fn fixed_circular_buffer_boxed<T, const N: usize>() -> ! {
    unimplemented!()
}

common::define_tests!(
    fixed_circular_buffer,
    fixed_circular_buffer_from,
    fixed_circular_buffer_from_iter,
    fixed_circular_buffer_boxed,
);

#[test]
fn from_array() {
    let arr = [];
    let buf = FixedCircularBuffer::<i32, 4>::from(arr);
    assert_buf_eq!(buf, [] as [i32; 0]);

    let mut tracker = DropTracker::new();
    let arr = [tracker.track(1), tracker.track(2)];
    let buf = FixedCircularBuffer::<DropItem<i32>, 4>::from(arr);
    assert_buf_eq!(buf, [1, 2]);
    tracker.assert_all_alive([1, 2]);
    tracker.assert_fully_alive();

    let mut tracker = DropTracker::new();
    let arr = [
        tracker.track(1),
        tracker.track(2),
        tracker.track(3),
        tracker.track(4),
    ];
    let buf = FixedCircularBuffer::<DropItem<i32>, 4>::from(arr);
    assert_buf_eq!(buf, [1, 2, 3, 4]);
    tracker.assert_all_alive([1, 2, 3, 4]);
    tracker.assert_fully_alive();

    let mut tracker = DropTracker::new();
    let arr = [
        tracker.track(1),
        tracker.track(2),
        tracker.track(3),
        tracker.track(4),
        tracker.track(5),
        tracker.track(6),
    ];
    let buf = FixedCircularBuffer::<DropItem<i32>, 4>::from(arr);
    assert_buf_eq!(buf, [3, 4, 5, 6]);
    tracker.assert_all_alive([3, 4, 5, 6]);
    tracker.assert_all_dropped([1, 2]);

    let mut tracker = DropTracker::new();
    let arr = [
        tracker.track(1),
        tracker.track(2),
        tracker.track(3),
        tracker.track(4),
        tracker.track(5),
        tracker.track(6),
        tracker.track(7),
        tracker.track(8),
    ];
    let buf = FixedCircularBuffer::<DropItem<i32>, 4>::from(arr);
    assert_buf_eq!(buf, [5, 6, 7, 8]);
    tracker.assert_all_alive([5, 6, 7, 8]);
    tracker.assert_all_dropped([1, 2, 3, 4]);
}

#[test]
fn from_iter() {
    let vec = vec![];
    let buf = FixedCircularBuffer::<i32, 4>::from_iter(vec);
    assert_buf_eq!(buf, [] as [i32; 0]);

    let mut tracker = DropTracker::new();
    let vec = vec![tracker.track(1), tracker.track(2)];
    let buf = FixedCircularBuffer::<DropItem<i32>, 4>::from_iter(vec);
    assert_buf_eq!(buf, [1, 2]);
    tracker.assert_all_alive([1, 2]);
    tracker.assert_fully_alive();

    let mut tracker = DropTracker::new();
    let vec = vec![
        tracker.track(1),
        tracker.track(2),
        tracker.track(3),
        tracker.track(4),
    ];
    let buf = FixedCircularBuffer::<DropItem<i32>, 4>::from_iter(vec);
    assert_buf_eq!(buf, [1, 2, 3, 4]);
    tracker.assert_all_alive([1, 2, 3, 4]);
    tracker.assert_fully_alive();

    let mut tracker = DropTracker::new();
    let vec = vec![
        tracker.track(1),
        tracker.track(2),
        tracker.track(3),
        tracker.track(4),
        tracker.track(5),
        tracker.track(6),
    ];
    let buf = FixedCircularBuffer::<DropItem<i32>, 4>::from_iter(vec);
    assert_buf_eq!(buf, [3, 4, 5, 6]);
    tracker.assert_all_alive([3, 4, 5, 6]);
    tracker.assert_all_dropped([1, 2]);

    let mut tracker = DropTracker::new();
    let vec = vec![
        tracker.track(1),
        tracker.track(2),
        tracker.track(3),
        tracker.track(4),
        tracker.track(5),
        tracker.track(6),
        tracker.track(7),
        tracker.track(8),
    ];
    let buf = FixedCircularBuffer::<DropItem<i32>, 4>::from_iter(vec);
    assert_buf_eq!(buf, [5, 6, 7, 8]);
    tracker.assert_all_alive([5, 6, 7, 8]);
    tracker.assert_all_dropped([1, 2, 3, 4]);
}

#[test]
fn const_construction() {
    let buf = const {
        let mut buf = FixedCircularBuffer::<u32, 8>::new();
        let buf_ref = buf.as_mut_circular_buffer();
        buf_ref.push_back(3);
        buf_ref.push_back(4);
        buf_ref.push_back(5);
        buf_ref.push_front(2);
        buf_ref.push_front(1);
        buf_ref.push_front(0);
        buf_ref.pop_back();
        buf_ref.pop_front();
        buf
    };

    assert_buf_eq!(buf, [1, 2, 3, 4]);
}
