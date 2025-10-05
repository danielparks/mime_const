//! Determine relative performance of various ways of constructing a media type.

#![allow(
    clippy::incompatible_msrv,
    clippy::missing_docs_in_private_items,
    missing_docs
)]

use criterion::{
    criterion_group, criterion_main, BenchmarkId, Criterion, Throughput,
};
use mime_const::{index, index_u16, index_u8, index_usize, owned, slice};
use std::time::Duration;

fn benchmarks(c: &mut Criterion) {
    // Test `rough_parse()`:
    assert_eq!(
        (
            "image",
            "svg+xml",
            Some("xml"),
            Some(("charset", "utf-8")),
            None
        ),
        rough_parse("image/svg+xml; charset=utf-8")
    );

    let mut group = c.benchmark_group("mime_parse");
    group
        .noise_threshold(0.10)
        .significance_level(0.01)
        .confidence_level(0.99)
        .sample_size(300)
        .warm_up_time(Duration::from_millis(10))
        .measurement_time(Duration::from_millis(100));

    for input in ["text/plain", "text/plain; charset=utf-8", "image/svg+xml"] {
        group.throughput(Throughput::Bytes(input.len().try_into().unwrap()));
        group.bench_with_input(
            BenchmarkId::new("rough_parse", input),
            input,
            |b, input| b.iter(|| rough_parse(input)),
        );

        group.bench_with_input(
            BenchmarkId::new("slice::Mime literal", input),
            input,
            |b, input| {
                let (typ, sub, suffix, param_1, param_2) = rough_parse(input);
                b.iter(|| {
                    slice::Mime::constant(typ, sub, suffix, param_1, param_2)
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("owned::Mime conversion", input),
            input,
            |b, input| {
                let (typ, sub, suffix, param_1, param_2) = rough_parse(input);
                b.iter(|| {
                    owned::Mime::from(slice::Mime::constant(
                        typ, sub, suffix, param_1, param_2,
                    ))
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("index::Mime parse", input),
            input,
            |b, input| b.iter(|| index::Mime::constant(input)),
        );

        group.bench_with_input(
            BenchmarkId::new("index_u8::Mime parse", input),
            input,
            |b, input| b.iter(|| index_u8::Mime::constant(input)),
        );

        group.bench_with_input(
            BenchmarkId::new("index_u16::Mime parse", input),
            input,
            |b, input| b.iter(|| index_u16::Mime::constant(input)),
        );

        group.bench_with_input(
            BenchmarkId::new("index_usize::Mime parse", input),
            input,
            |b, input| b.iter(|| index_usize::Mime::constant(input)),
        );
    }

    group.finish();
}

/// Quick and dirty mime type parsing.
///
/// Quick and dirty test in `benchmarks()`.
#[allow(clippy::type_complexity)]
fn rough_parse(
    input: &str,
) -> (
    &str,
    &str,
    Option<&str>,
    Option<(&str, &str)>,
    Option<(&str, &str)>,
) {
    fn parameter_to_tuple(key_value: &str) -> (&str, &str) {
        let mut iter = key_value.splitn(2, '=');
        (iter.next().unwrap(), iter.next().unwrap())
    }

    let (type_, rest) = input.split_once('/').unwrap();
    let mut iter = rest.splitn(4, "; ");
    let subtype = iter.next().unwrap();
    let suffix = subtype.split_once('+').map(|(_, suffix)| suffix);

    let parameter_1 = iter.next().map(parameter_to_tuple);
    let parameter_2 = iter.next().map(parameter_to_tuple);
    assert!(iter.next().is_none(), "too many parameters");

    (type_, subtype, suffix, parameter_1, parameter_2)
}

criterion_group!(general_group, benchmarks);
criterion_main!(general_group);
