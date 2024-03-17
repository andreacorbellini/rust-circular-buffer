// Copyright © 2023, 2024 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

use circular_buffer::CircularBuffer;
use criterion::BenchmarkGroup;
use criterion::Criterion;
use criterion::Throughput;
use criterion::criterion_group;
use criterion::criterion_main;
use criterion::measurement::Measurement;

fn fill<const N: usize, T: Default>(buf: &mut CircularBuffer<N, T>) {
    while buf.len() < N {
        buf.push_front(T::default())
    }
}

fn bench_push(c: &mut Criterion) {
    let mut group = c.benchmark_group("push");

    fn do_bench<M: Measurement, const N: usize>(
        group: &mut BenchmarkGroup<'_, M>,
        buf: &mut CircularBuffer<N, u32>,
    ) {
        group.throughput(Throughput::Elements(N as u64));
        group.bench_function("push_back", |b| b.iter(|| {
            buf.push_back(1);
        }));
        group.bench_function("push_front", |b| b.iter(|| {
            buf.push_front(1);
        }));
    }

    do_bench(&mut group, &mut CircularBuffer::<10, u32>::new());
    do_bench(&mut group, &mut CircularBuffer::<100, u32>::new());
    do_bench(&mut group, &mut CircularBuffer::<1000, u32>::boxed());

    group.finish();
}

fn bench_pop(c: &mut Criterion) {
    let mut group = c.benchmark_group("pop");

    fn do_bench<M: Measurement, const N: usize>(
        group: &mut BenchmarkGroup<'_, M>,
        buf: &mut CircularBuffer<N, u32>,
    ) {
        fill(buf);
        group.throughput(Throughput::Elements(N as u64));
        group.bench_function("pop_back", |b| b.iter(|| {
            let mut buf = buf.clone();
            for _ in 0..buf.capacity() {
                buf.pop_back();
            }
        }));
        group.bench_function("pop_front", |b| b.iter(|| {
            let mut buf = buf.clone();
            for _ in 0..buf.capacity() {
                buf.pop_front();
            }
        }));
    }

    do_bench(&mut group, &mut CircularBuffer::<10, u32>::new());
    do_bench(&mut group, &mut CircularBuffer::<100, u32>::new());
    do_bench(&mut group, &mut CircularBuffer::<1000, u32>::boxed());

    group.finish();
}

criterion_group!(benches, bench_push, bench_pop);
criterion_main!(benches);
