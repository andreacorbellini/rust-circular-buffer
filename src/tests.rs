// Copyright © 2023-2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

#![cfg(feature = "std")]

use crate::CircularBuffer;
use crate::FixedCircularBuffer;
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
