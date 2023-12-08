#![cfg(not(miri))]
/// Compare the correctness of `CircularBuffer` against a reference implementation (that is assumed
/// to be fully correct).
///
/// This module applies random actions (like `push_back`, `pop_front`, ...) to a `CircularBuffer`
/// and to a reference implementation at the same time, and compares their result after each
/// action. The reference implementation currently is based on top of `VecDeque`.

use circular_buffer::CircularBuffer;
use circular_buffer::heap::HeapCircularBuffer;
use drop_tracker::DropItem;
use drop_tracker::DropTracker;
use rand::Rng;
use rand::distributions::Distribution;
use rand::distributions::Standard;
use rand::distributions::Uniform;
use std::collections::VecDeque;
use std::fmt;
use std::mem;
use std::ops::Deref;
use std::ops::DerefMut;
use std::ops::RangeInclusive;
use std::rc::Rc;

#[derive(Clone, Debug)]
enum Action<T> {
    BackMut(T),
    FrontMut(T),
    GetMut(usize, T),
    PushBack(T),
    PushFront(T),
    PopBack,
    PopFront,
    Remove(usize),
    Swap(usize, usize),
    SwapRemoveBack(usize),
    SwapRemoveFront(usize),
    TruncateBack(usize),
    TruncateFront(usize),
    Clear,
    Extend(Vec<T>),
    ExtendFromSlice(Vec<T>),
    RangeMut(RangeInclusive<usize>, Vec<T>),
    Drain(RangeInclusive<usize>),
    MakeContiguous,
}

impl<T> Distribution<Action<T>> for Standard
    where Standard: Distribution<T>
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Action<T> {
        fn random_vec<T, R: Rng + ?Sized>(rng: &mut R) -> Vec<T>
            where Standard: Distribution<T>
        {
            let size = rng.gen_range(0..128);
            let mut vec = Vec::with_capacity(size);
            for _ in 0..size {
                vec.push(rng.gen());
            }
            vec
        }

        let action_num: u8 = rng.gen_range(0..=6);

        match action_num {
            0 => Action::PushBack(rng.gen()),
            1 => Action::PushFront(rng.gen()),
            2 => Action::PopBack,
            3 => Action::PopFront,
            4 => Action::Clear,
            5 => Action::Extend(random_vec(rng)),
            6 => Action::ExtendFromSlice(random_vec(rng)),
            _ => unreachable!(),
        }
    }
}

impl<T> Distribution<Action<T>> for Uniform<usize>
    where Standard: Distribution<T>
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Action<T> {
        fn random_vec<T, R: Rng + ?Sized>(rng: &mut R) -> Vec<T>
            where Standard: Distribution<T>
        {
            let size = rng.gen_range(0..128);
            let mut vec = Vec::with_capacity(size);
            for _ in 0..size {
                vec.push(rng.gen());
            }
            vec
        }

        fn random_range<D: Distribution<usize>, R: Rng + ?Sized>(dist: &D, rng: &mut R) -> RangeInclusive<usize> {
            let low = dist.sample(rng);
            let high = dist.sample(rng).max(low);
            low..=high
        }

        let action_num: u8 = rng.gen_range(0..=18);

        match action_num {
            0  => Action::BackMut(rng.gen()),
            1  => Action::FrontMut(rng.gen()),
            2  => Action::GetMut(self.sample(rng), rng.gen()),
            3  => Action::PushBack(rng.gen()),
            4  => Action::PushFront(rng.gen()),
            5  => Action::PopBack,
            6  => Action::PopFront,
            7  => Action::Remove(self.sample(rng)),
            8  => Action::Swap(self.sample(rng), self.sample(rng)),
            9  => Action::SwapRemoveBack(self.sample(rng)),
            10 => Action::SwapRemoveFront(self.sample(rng)),
            11 => Action::TruncateBack(self.sample(rng)),
            12 => Action::TruncateFront(self.sample(rng)),
            13 => Action::Clear,
            14 => Action::Extend(random_vec(rng)),
            15 => Action::ExtendFromSlice(random_vec(rng)),
            16 => Action::RangeMut(random_range(self, rng), random_vec(rng)),
            17 => Action::Drain(random_range(self, rng)),
            18 => Action::MakeContiguous,
            _ => unreachable!(),
        }
    }
}

#[derive(Copy, Clone, Debug)]
enum Direction {
    Back,
    Front,
}

#[derive(Debug)]
struct Reference<T> {
    inner: VecDeque<T>,
    max_len: usize,
}

impl<T> Reference<T> {
    fn new(max_len: usize) -> Self {
        Self {
            inner: VecDeque::new(),
            max_len,
        }
    }

    fn trim(&mut self, direction: Direction) {
        match direction {
            Direction::Back  => self.trim_back(),
            Direction::Front => self.trim_front(),
        }
    }

    fn trim_back(&mut self) {
        while self.len() > self.max_len {
            self.pop_back().unwrap();
        }
    }

    fn trim_front(&mut self) {
        while self.len() > self.max_len {
            self.pop_front().unwrap();
        }
    }
}

impl<T> Deref for Reference<T> {
    type Target = VecDeque<T>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T> DerefMut for Reference<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
enum Result<T> {
    None,
    Val(T),
    Vec(Vec<T>),
}

impl<T> From<Option<T>> for Result<T> {
    fn from(opt: Option<T>) -> Self {
        match opt {
            Some(val) => Self::Val(val),
            None      => Self::None,
        }
    }
}

impl<T> FromIterator<T> for Result<T> {
    fn from_iter<I>(iter: I) -> Self
       where I: IntoIterator<Item = T>
    {
        let vec = Vec::from_iter(iter);
        Self::Vec(vec)
    }
}

trait Perform<T> {
    fn perform(&mut self, action: Action<T>) -> Result<T>;
}

impl<const N: usize, T> Perform<T> for CircularBuffer<N, T>
    where T: Clone
{
    fn perform(&mut self, action: Action<T>) -> Result<T> {
        match action {
            Action::BackMut(elem)          => { *self.back_mut().unwrap() = elem; Result::None },
            Action::FrontMut(elem)         => { *self.front_mut().unwrap() = elem; Result::None },
            Action::GetMut(index, elem)    => { *self.get_mut(index).unwrap() = elem; Result::None },
            Action::PushBack(elem)         => { self.push_back(elem); Result::None },
            Action::PushFront(elem)        => { self.push_front(elem); Result::None },
            Action::PopBack                => self.pop_back().into(),
            Action::PopFront               => self.pop_front().into(),
            Action::Remove(index)          => self.remove(index).into(),
            Action::Swap(x, y)             => { self.swap(x, y); Result::None },
            Action::SwapRemoveBack(index)  => { self.swap_remove_back(index); Result::None },
            Action::SwapRemoveFront(index) => { self.swap_remove_front(index); Result::None },
            Action::TruncateBack(index)    => { self.truncate_back(index); Result::None },
            Action::TruncateFront(index)   => { self.truncate_front(index); Result::None },
            Action::Clear                  => { self.clear(); Result::None },
            Action::Extend(elems)          => { self.extend(elems); Result::None },
            Action::ExtendFromSlice(elems) => { self.extend_from_slice(&elems[..]); Result::None },
            Action::RangeMut(range, elems) => {
                self.range_mut(range)
                    .zip(elems)
                    .map(|(elem, replacement)| *elem = replacement)
                    .count();
                Result::None
            },
            Action::Drain(range)           => { self.drain(range).collect() },
            Action::MakeContiguous         => { self.make_contiguous().iter().cloned().collect() },
        }
    }
}

impl<T> Perform<T> for HeapCircularBuffer<T>
where
    T: Clone,
{
    fn perform(&mut self, action: Action<T>) -> Result<T> {
        match action {
            Action::BackMut(elem)          => { *self.back_mut().unwrap() = elem; Result::None },
            Action::FrontMut(elem)         => { *self.front_mut().unwrap() = elem; Result::None },
            Action::GetMut(index, elem)    => { *self.get_mut(index).unwrap() = elem; Result::None },
            Action::PushBack(elem)         => { self.push_back(elem); Result::None },
            Action::PushFront(elem)        => { self.push_front(elem); Result::None },
            Action::PopBack                => self.pop_back().into(),
            Action::PopFront               => self.pop_front().into(),
            Action::Remove(index)          => self.remove(index).into(),
            Action::Swap(x, y)             => { self.swap(x, y); Result::None },
            Action::SwapRemoveBack(index)  => { self.swap_remove_back(index); Result::None },
            Action::SwapRemoveFront(index) => { self.swap_remove_front(index); Result::None },
            Action::TruncateBack(index)    => { self.truncate_back(index); Result::None },
            Action::TruncateFront(index)   => { self.truncate_front(index); Result::None },
            Action::Clear                  => { self.clear(); Result::None },
            Action::Extend(elems)          => { self.extend(elems); Result::None },
            Action::ExtendFromSlice(elems) => { self.extend_from_slice(&elems[..]); Result::None },
            Action::RangeMut(range, elems) => {
                self.range_mut(range)
                    .zip(elems)
                    .map(|(elem, replacement)| *elem = replacement)
                    .count();
                Result::None
            },
            Action::Drain(range)           => { self.drain(range).collect() },
            Action::MakeContiguous         => { self.make_contiguous().iter().cloned().collect() },
        }
    }
}

impl<T> Perform<T> for VecDeque<T>
    where T: Clone
{
    fn perform(&mut self, action: Action<T>) -> Result<T> {
        match action {
            Action::BackMut(elem)          => { *self.back_mut().unwrap() = elem; Result::None },
            Action::FrontMut(elem)         => { *self.front_mut().unwrap() = elem; Result::None },
            Action::GetMut(index, elem)    => { *self.get_mut(index).unwrap() = elem; Result::None },
            Action::PushBack(elem)         => { self.push_back(elem); Result::None },
            Action::PushFront(elem)        => { self.push_front(elem); Result::None },
            Action::PopBack                => self.pop_back().into(),
            Action::PopFront               => self.pop_front().into(),
            Action::Remove(index)          => self.remove(index).into(),
            Action::Swap(x, y)             => { self.swap(x, y); Result::None },
            Action::SwapRemoveBack(index)  => { self.swap_remove_back(index); Result::None },
            Action::SwapRemoveFront(index) => { self.swap_remove_front(index); Result::None },
            Action::TruncateBack(size)     => {
                while self.len() > size { let _ = self.pop_back(); };
                Result::None
            },
            Action::TruncateFront(size)    => {
                while self.len() > size { let _ = self.pop_front(); };
                Result::None
            },
            Action::Clear                  => { self.clear(); Result::None },
            Action::Extend(elems)          => { self.extend(elems); Result::None },
            Action::ExtendFromSlice(elems) => { self.extend(elems); Result::None },
            Action::RangeMut(range, elems) => {
                self.range_mut(range)
                    .zip(elems)
                    .map(|(elem, replacement)| *elem = replacement)
                    .count();
                Result::None
            },
            Action::Drain(range)           => { self.drain(range).collect() },
            Action::MakeContiguous         => { self.make_contiguous().iter().cloned().collect() },
        }
    }
}

impl<T> Perform<T> for Reference<T>
    where T: Clone
{
    fn perform(&mut self, action: Action<T>) -> Result<T> {
        let trim_direction = match action {
            Action::PushBack(_)        => Some(Direction::Front),
            Action::PushFront(_)       => Some(Direction::Back),
            Action::Extend(_)          => Some(Direction::Front),
            Action::ExtendFromSlice(_) => Some(Direction::Front),
            _                          => None,
        };

        let result = self.inner.perform(action);

        if let Some(direction) = trim_direction {
            self.trim(direction);
        }

        result
    }
}

mod fixed {
    use super::*;

    fn test<const N: usize, T>()
        where T: Clone + PartialEq + fmt::Debug,
              Standard: Distribution<T>
    {
        let mut reference = Reference::<T>::new(N);
        let mut buffer = CircularBuffer::<N, T>::boxed();
        let mut rng = rand::thread_rng();
    
        for _ in 0..200_000 {
            // Generate a random action
            let action: Action<T> = if reference.is_empty() {
                <Standard as Distribution<Action<T>>>::sample(&Standard, &mut rng)
            } else {
                Uniform::from(0..reference.len()).sample(&mut rng)
            };
    
            println!("{action:?}");
    
            // Perform the action on both the reference implementation and the CircularBuffer
            let expected = reference.perform(action.clone());
            let actual = buffer.perform(action);
    
            // Compare the return value of both implementations
            assert_eq!(expected, actual);
    
            // Compare the state of both implementations
            let expected_items = reference.iter()
                                          .cloned()
                                          .collect::<Vec<T>>();
            #[allow(clippy::eq_op)]
            { assert_eq!(buffer, buffer); }
            assert_eq!(*buffer, &expected_items[..]);
            assert_eq!(buffer.to_vec(), expected_items);
    
            assert_eq!(reference.len(), buffer.len());
            assert_eq!(reference.is_empty(), buffer.is_empty());
    
            assert_eq!(reference.iter().collect::<Vec<&T>>(),
                       buffer.iter().collect::<Vec<&T>>());
            assert_eq!(reference.iter_mut().collect::<Vec<&mut T>>(),
                       buffer.iter_mut().collect::<Vec<&mut T>>());
    
            assert_eq!(reference.iter().rev().collect::<Vec<&T>>(),
                       buffer.iter().rev().collect::<Vec<&T>>());
            assert_eq!(reference.iter_mut().rev().collect::<Vec<&mut T>>(),
                       buffer.iter_mut().rev().collect::<Vec<&mut T>>());
        }
    }
    
    #[test]
    fn zero() {
        test::<0, u64>();
    }
    
    #[test]
    fn small() {
        test::<10, u64>();
    }
    
    #[test]
    fn medium() {
        test::<1_000, u64>();
    }
    
    #[test]
    fn large() {
        test::<1_000_000, u64>();
    }
    
    #[test]
    fn largest_with_zero_sized_struct() {
        type Zst = ();
        assert_eq!(mem::size_of::<Zst>(), 0);
        test::<{ usize::MAX }, Zst>();
    }
    
    #[test]
    fn drop() {
        static mut TRACKER: Option<DropTracker<u64>> = None;
    
        // SAFETY: the assumption is that this test function will be called only once
        unsafe { TRACKER.replace(DropTracker::new()); }
    
        fn tracker() -> &'static DropTracker<u64> {
            unsafe { TRACKER.as_ref().unwrap() }
        }
    
        fn tracker_mut() -> &'static mut DropTracker<u64> {
            unsafe { TRACKER.as_mut().unwrap() }
        }
    
        #[derive(Clone, PartialEq, Eq, Debug)]
        struct Item(Rc<DropItem<u64>>);
    
        impl Distribution<Item> for Standard {
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Item {
                let n = rng.gen();
                Item(Rc::new(tracker_mut().track(n)))
            }
        }
    
        test::<100, Item>();
    
        tracker().assert_fully_dropped();
    }
}

mod heap {
    use super::*;

    fn test<const N: usize, T>()
        where T: Clone + PartialEq + fmt::Debug,
              Standard: Distribution<T>
    {
        let mut reference = Reference::<T>::new(N);
        let mut buffer = HeapCircularBuffer::<T>::with_capacity(N);
        let mut rng = rand::thread_rng();
    
        for _ in 0..200_000 {
            // Generate a random action
            let action: Action<T> = if reference.is_empty() {
                <Standard as Distribution<Action<T>>>::sample(&Standard, &mut rng)
            } else {
                Uniform::from(0..reference.len()).sample(&mut rng)
            };
    
            println!("{action:?}");
    
            // Perform the action on both the reference implementation and the CircularBuffer
            let expected = reference.perform(action.clone());
            let actual = buffer.perform(action);
    
            // Compare the return value of both implementations
            assert_eq!(expected, actual);
    
            // Compare the state of both implementations
            let expected_items = reference.iter()
                                          .cloned()
                                          .collect::<Vec<T>>();
            #[allow(clippy::eq_op)]
            { assert_eq!(buffer, buffer); }
            assert_eq!(buffer, &expected_items[..]);
            assert_eq!(buffer.to_vec(), expected_items);
    
            assert_eq!(reference.len(), buffer.len());
            assert_eq!(reference.is_empty(), buffer.is_empty());
    
            assert_eq!(reference.iter().collect::<Vec<&T>>(),
                       buffer.iter().collect::<Vec<&T>>());
            assert_eq!(reference.iter_mut().collect::<Vec<&mut T>>(),
                       buffer.iter_mut().collect::<Vec<&mut T>>());
    
            assert_eq!(reference.iter().rev().collect::<Vec<&T>>(),
                       buffer.iter().rev().collect::<Vec<&T>>());
            assert_eq!(reference.iter_mut().rev().collect::<Vec<&mut T>>(),
                       buffer.iter_mut().rev().collect::<Vec<&mut T>>());
        }
    }
    
    #[test]
    fn zero() {
        test::<0, u64>();
    }
    
    #[test]
    fn small() {
        test::<10, u64>();
    }
    
    #[test]
    fn medium() {
        test::<1_000, u64>();
    }
    
    #[test]
    fn large() {
        test::<1_000_000, u64>();
    }
    
    #[test]
    fn largest_with_zero_sized_struct() {
        type Zst = ();
        assert_eq!(mem::size_of::<Zst>(), 0);
        test::<{ usize::MAX }, Zst>();
    }
    
    #[test]
    fn drop() {
        static mut TRACKER: Option<DropTracker<u64>> = None;
    
        // SAFETY: the assumption is that this test function will be called only once
        unsafe { TRACKER.replace(DropTracker::new()); }
    
        fn tracker() -> &'static DropTracker<u64> {
            unsafe { TRACKER.as_ref().unwrap() }
        }
    
        fn tracker_mut() -> &'static mut DropTracker<u64> {
            unsafe { TRACKER.as_mut().unwrap() }
        }
    
        #[derive(Clone, PartialEq, Eq, Debug)]
        struct Item(Rc<DropItem<u64>>);
    
        impl Distribution<Item> for Standard {
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Item {
                let n = rng.gen();
                Item(Rc::new(tracker_mut().track(n)))
            }
        }
    
        test::<100, Item>();
    
        tracker().assert_fully_dropped();
    }
}