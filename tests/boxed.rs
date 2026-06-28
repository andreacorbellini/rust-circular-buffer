// Copyright © 2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

#![cfg(feature = "alloc")]

extern crate alloc;

use circular_buffer::HeapCircularBuffer;
use drop_tracker::DropItem;
use drop_tracker::DropTracker;

#[test]
fn test() {
    let mut tracker = DropTracker::new();
    let mut buf =
        HeapCircularBuffer::<DropItem<u32>>::with_capacity(10).into_boxed_circular_buffer();

    buf.push_back(tracker.track(1));
    buf.push_back(tracker.track(2));
    buf.push_back(tracker.track(3));

    tracker.assert_fully_alive();

    drop(buf);

    tracker.assert_fully_dropped();
}
