// Copyright © 2023-2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

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
