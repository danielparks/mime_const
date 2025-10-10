//! Benchmark ways to check if bytes in a string are valid

#![allow(
    clippy::incompatible_msrv,
    clippy::missing_docs_in_private_items,
    missing_docs
)]

use criterion::{
    criterion_group, criterion_main, BenchmarkId, Criterion, Throughput,
};
use mime_const::bitfilter::BitFilter;
use mime_const::bytefilter::ByteFilter;
use std::hint::black_box;
use std::time::Duration;

macro_rules! byte_map {
    ($($flag:expr,)*) => ([
        $($flag != 0,)*
    ])
}

const TOKEN_MAP: [bool; 256] = byte_map![
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1,
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
];

#[inline]
const fn check_map(c: u8) -> bool {
    TOKEN_MAP[c as usize]
}

#[inline]
const fn match_byte(c: u8) -> bool {
    matches!(
        c,
        b'!' | b'#' | b'$' | b'%' | b'&' | b'\'' | b'+' | b'-' | b'.' | b'^' |
        b'_' | b'`' | b'|' | b'~' | b'0'..=b'9' | b'a'..=b'z' | b'A'..=b'Z',
    )
}

const BIT_FILTER: BitFilter = BitFilter::from_str("-!#$%&'+.^_`|~0-9a-zA-Z");
const BYTE_FILTER: ByteFilter = ByteFilter::from_str("-!#$%&'+.^_`|~0-9a-zA-Z");

fn benchmarks(c: &mut Criterion) {
    for b in 0u8..=255 {
        assert_eq!(
            match_byte(b),
            BIT_FILTER.match_byte(b),
            "byte {:?} does not match",
            b as char
        );
        assert_eq!(
            match_byte(b),
            check_map(b),
            "byte {:?} does not match",
            b as char
        );
        assert_eq!(
            match_byte(b),
            BYTE_FILTER.match_byte(b),
            "byte {:?} does not match",
            b as char
        );
    }

    let mut group = c.benchmark_group("filter_bytes");
    group
        .noise_threshold(0.10)
        .significance_level(0.01)
        .confidence_level(0.99)
        .sample_size(300)
        .warm_up_time(Duration::from_millis(10))
        .measurement_time(Duration::from_millis(100));

    for input in [b'a'..=b'z', b' '..=(b' ' + b'z' - b'a')] {
        group.throughput(Throughput::Bytes(input.len().try_into().unwrap()));
        group.bench_with_input(
            BenchmarkId::new("byte map", format!("{input:?}")),
            &input,
            |b, input| {
                b.iter(|| {
                    for b in input.clone() {
                        black_box(check_map(b));
                    }
                })
            },
        );
        group.bench_with_input(
            BenchmarkId::new("match", format!("{input:?}")),
            &input,
            |b, input| {
                b.iter(|| {
                    for b in input.clone() {
                        black_box(match_byte(b));
                    }
                })
            },
        );
        group.bench_with_input(
            BenchmarkId::new("BitFilter", format!("{input:?}")),
            &input,
            |b, input| {
                b.iter(|| {
                    for b in input.clone() {
                        black_box(BIT_FILTER.match_byte(b));
                    }
                })
            },
        );
        group.bench_with_input(
            BenchmarkId::new("ByteFilter", format!("{input:?}")),
            &input,
            |b, input| {
                b.iter(|| {
                    for b in input.clone() {
                        black_box(BYTE_FILTER.match_byte(b));
                    }
                })
            },
        );
    }

    group.finish();
}

criterion_group!(general_group, benchmarks);
criterion_main!(general_group);
