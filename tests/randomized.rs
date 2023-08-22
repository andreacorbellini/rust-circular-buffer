/// Compare the correctness of `CircularBuffer` against a reference implementation (that is assumed
/// to be fully correct).
///
/// This module applies random actions (like `push_back`, `pop_front`, ...) to a `CircularBuffer`
/// and to a reference implementation at the same time, and compares their result after each
/// action. The reference implementation currently is based on top of `VecDeque`.

use circular_buffer::CircularBuffer;
use drop_tracker::DropItem;
use drop_tracker::DropTracker;
use rand::Rng;
use rand::distributions::Distribution;
use rand::distributions::Standard;
use rand::distributions::Uniform;
use std::collections::VecDeque;
use std::fmt;
use std::ops::Deref;
use std::ops::DerefMut;
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

        let action_num: u8 = rng.gen_range(0..=15);

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

    fn trim(&mut self, direction: Direction) -> Vec<T> {
        match direction {
            Direction::Back  => self.trim_back(),
            Direction::Front => self.trim_front(),
        }
    }

    fn trim_back(&mut self) -> Vec<T> {
        let mut trimmed = Vec::new();
        while self.len() > self.max_len {
            let item = self.pop_back().unwrap();
            trimmed.push(item);
        }
        trimmed
    }

    fn trim_front(&mut self) -> Vec<T> {
        let mut trimmed = Vec::new();
        while self.len() > self.max_len {
            let item = self.pop_front().unwrap();
            trimmed.push(item);
        }
        trimmed
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

trait Perform<T> {
    fn perform(&mut self, action: Action<T>) -> Option<T>;
}

impl<const N: usize, T> Perform<T> for CircularBuffer<N, T>
    where T: Clone
{
    fn perform(&mut self, action: Action<T>) -> Option<T> {
        match action {
            Action::BackMut(elem)          => { *self.back_mut().unwrap() = elem; None },
            Action::FrontMut(elem)         => { *self.front_mut().unwrap() = elem; None },
            Action::GetMut(index, elem)    => { *self.get_mut(index).unwrap() = elem; None },
            Action::PushBack(elem)         => { self.push_back(elem) },
            Action::PushFront(elem)        => { self.push_front(elem) },
            Action::PopBack                => self.pop_back(),
            Action::PopFront               => self.pop_front(),
            Action::Remove(index)          => self.remove(index),
            Action::Swap(x, y)             => { self.swap(x, y); None },
            Action::SwapRemoveBack(index)  => { self.swap_remove_back(index); None },
            Action::SwapRemoveFront(index) => { self.swap_remove_front(index); None },
            Action::TruncateBack(index)    => { self.truncate_back(index); None },
            Action::TruncateFront(index)   => { self.truncate_front(index); None },
            Action::Clear                  => { self.clear(); None },
            Action::Extend(elems)          => { self.extend(elems); None },
            Action::ExtendFromSlice(elems) => { self.extend_from_slice(&elems[..]); None },
        }
    }
}

impl<T> Perform<T> for VecDeque<T> {
    fn perform(&mut self, action: Action<T>) -> Option<T> {
        match action {
            Action::BackMut(elem)          => { *self.back_mut().unwrap() = elem; None },
            Action::FrontMut(elem)         => { *self.front_mut().unwrap() = elem; None },
            Action::GetMut(index, elem)    => { *self.get_mut(index).unwrap() = elem; None },
            Action::PushBack(elem)         => { self.push_back(elem); None },
            Action::PushFront(elem)        => { self.push_front(elem); None },
            Action::PopBack                => self.pop_back(),
            Action::PopFront               => self.pop_front(),
            Action::Remove(index)          => self.remove(index),
            Action::Swap(x, y)             => { self.swap(x, y); None },
            Action::SwapRemoveBack(index)  => { self.swap_remove_back(index); None },
            Action::SwapRemoveFront(index) => { self.swap_remove_front(index); None },
            Action::TruncateBack(size)     => { while self.len() > size { let _ = self.pop_back(); }; None },
            Action::TruncateFront(size)    => { while self.len() > size { let _ = self.pop_front(); }; None },
            Action::Clear                  => { self.clear(); None },
            Action::Extend(elems)          => { self.extend(elems); None },
            Action::ExtendFromSlice(elems) => { self.extend(elems); None },
        }
    }
}

impl<T> Perform<T> for Reference<T> {
    fn perform(&mut self, action: Action<T>) -> Option<T> {
        let (trim_direction, return_trimmed) = match action {
            Action::PushBack(_)        => (Some(Direction::Front), true),
            Action::PushFront(_)       => (Some(Direction::Back), true),
            Action::Extend(_)          => (Some(Direction::Front), false),
            Action::ExtendFromSlice(_) => (Some(Direction::Front), false),
            _                          => (None, false),
        };

        let result = self.inner.perform(action);

        if let Some(direction) = trim_direction {
            let mut trimmed = self.trim(direction);
            if return_trimmed {
                assert!(result.is_none());
                assert!(trimmed.len() <= 1);
                return trimmed.pop();
            }
        }

        result
    }
}

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

        assert_eq!(reference.len(), buffer.len());
        assert_eq!(reference.is_empty(), buffer.is_empty());
        assert_eq!(reference.iter().collect::<Vec<&T>>(),
                   buffer.iter().collect::<Vec<&T>>());
        assert_eq!(reference.iter_mut().collect::<Vec<&mut T>>(),
                   buffer.iter_mut().collect::<Vec<&mut T>>());
        assert_eq!(buffer.to_vec(), expected_items);
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
