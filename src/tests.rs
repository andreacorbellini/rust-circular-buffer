// Copyright © 2023-2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

#![cfg(feature = "std")]

use crate::CircularBuffer;
use crate::FixedCircularBuffer;
use drop_tracker::DropItem;
use drop_tracker::DropTracker;
use std::cell::RefCell;
use std::collections::hash_map::DefaultHasher;
use std::hash::Hash;
use std::hash::Hasher;

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
fn extend() {
    let mut buf = FixedCircularBuffer::<u32, 4>::new();
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
    let mut buf = FixedCircularBuffer::<u32, 4>::new();
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
    let mut buf = FixedCircularBuffer::<u32, 4>::new();
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

    let mut buf = FixedCircularBuffer::<FaultyClonable, 4>::new();

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

    let mut buf = FixedCircularBuffer::<Cloneable, 6>::new();

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

    let mut buf = FixedCircularBuffer::<FaultyClonable, 6>::new();

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

    let mut buf = FixedCircularBuffer::<DropItem<u32>, 6>::new();

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
fn make_contiguous_full() {
    let mut buf: FixedCircularBuffer<u32, 4> = [1, 2, 3, 4].into_iter().collect();
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
fn make_contiguous_not_full() {
    let mut buf: FixedCircularBuffer<u32, 4> = [1, 2].into_iter().collect();
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
fn clone() {
    let mut buf = FixedCircularBuffer::<u32, 4>::new();
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
fn hash() {
    fn hash<T: Hash>(buf: &CircularBuffer<T>) -> u64 {
        let mut hasher = DefaultHasher::new();
        buf.hash(&mut hasher);
        hasher.finish()
    }

    let hash_empty = hash(&FixedCircularBuffer::<u32, 0>::new());
    assert_eq!(hash_empty, hash(&FixedCircularBuffer::<u32, 0>::new()));
    assert_eq!(hash_empty, hash(&FixedCircularBuffer::<u32, 2>::new()));
    assert_eq!(hash_empty, hash(&FixedCircularBuffer::<u32, 4>::new()));
    assert_eq!(hash_empty, hash(&FixedCircularBuffer::<u32, 8>::new()));

    let hash_1 = hash(&FixedCircularBuffer::<u32, 1>::from([1]));
    assert_ne!(hash_1, hash_empty);
    assert_eq!(hash_1, hash(&FixedCircularBuffer::<u32, 2>::from([1])));
    assert_eq!(hash_1, hash(&FixedCircularBuffer::<u32, 4>::from([1])));
    assert_eq!(hash_1, hash(&FixedCircularBuffer::<u32, 8>::from([1])));

    let hash_2 = hash(&FixedCircularBuffer::<u32, 2>::from([1, 2]));
    assert_ne!(hash_2, hash_empty);
    assert_ne!(hash_2, hash_1);
    assert_eq!(hash_2, hash(&FixedCircularBuffer::<u32, 4>::from([1, 2])));
    assert_eq!(hash_2, hash(&FixedCircularBuffer::<u32, 8>::from([1, 2])));

    let hash_4 = hash(&FixedCircularBuffer::<u32, 4>::from([1, 2, 3, 4]));
    assert_ne!(hash_4, hash_empty);
    assert_ne!(hash_4, hash_1);
    assert_ne!(hash_4, hash_2);
    assert_eq!(
        hash_4,
        hash(&FixedCircularBuffer::<u32, 4>::from([1, 2, 3, 4]))
    );
    assert_eq!(
        hash_4,
        hash(&FixedCircularBuffer::<u32, 8>::from([1, 2, 3, 4]))
    );
}

#[test]
fn debug() {
    let mut buf = FixedCircularBuffer::<u32, 4>::new();
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

macro_rules! assert_add_mod_eq {
    ( $expected:expr , crate :: add_mod ( $x:expr , $y:expr , $m:expr ) ) => {
        let x = $x;
        let y = $y;
        let m = $m;
        let expected = $expected;
        let result = crate::add_mod(x, y, m);
        assert_eq!(
            result, expected,
            "add_mod({x}, {y}, {m}) returned {result}; expected: {expected}"
        );
    };
}

#[test]
fn add_mod() {
    assert_eq!(0, crate::add_mod(0, 0, 1));
    assert_eq!(0, crate::add_mod(0, 1, 1));
    assert_eq!(0, crate::add_mod(1, 0, 1));
    assert_eq!(0, crate::add_mod(1, 1, 1));

    assert_eq!(0, crate::add_mod(0, 0, 2));
    assert_eq!(1, crate::add_mod(0, 1, 2));
    assert_eq!(0, crate::add_mod(0, 2, 2));
    assert_eq!(1, crate::add_mod(1, 0, 2));
    assert_eq!(0, crate::add_mod(1, 1, 2));
    assert_eq!(1, crate::add_mod(1, 2, 2));
    assert_eq!(0, crate::add_mod(2, 0, 2));
    assert_eq!(1, crate::add_mod(2, 1, 2));
    assert_eq!(0, crate::add_mod(2, 2, 2));

    for m in [
        3,
        4,
        5,
        6,
        7,
        8,
        usize::MAX >> 1,
        (usize::MAX >> 1) + 1,
        usize::MAX - 2,
        usize::MAX - 1,
        usize::MAX,
    ] {
        assert_add_mod_eq!(0, crate::add_mod(0, 0, m));
        assert_add_mod_eq!(0, crate::add_mod(0, m, m));
        assert_add_mod_eq!(0, crate::add_mod(m, 0, m));
        assert_add_mod_eq!(0, crate::add_mod(m, m, m));

        assert_add_mod_eq!(1, crate::add_mod(1, m, m));
        assert_add_mod_eq!(2, crate::add_mod(2, m, m));
        assert_add_mod_eq!(m - 2, crate::add_mod(m - 2, m, m));
        assert_add_mod_eq!(m - 1, crate::add_mod(m - 1, m, m));
    }
}
