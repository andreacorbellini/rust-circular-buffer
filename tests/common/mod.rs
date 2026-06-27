// Copyright © 2023-2026 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

macro_rules! define_tests {
    ( $new_buffer:ident ) => {
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
    };
}

pub(crate) use define_tests;
