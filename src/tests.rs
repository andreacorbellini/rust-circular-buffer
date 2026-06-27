// Copyright © 2023-2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

#![cfg(feature = "std")]

use crate::FixedCircularBuffer;

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
