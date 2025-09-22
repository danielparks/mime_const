//! Benchmark quoted-string implementations

#![allow(
    clippy::incompatible_msrv,
    clippy::missing_docs_in_private_items,
    missing_docs
)]

use criterion::{
    criterion_group, criterion_main, BenchmarkId, Criterion, Throughput,
};
use mime_const::rfc7231::unquote_string;
use quoted_string::test_utils::TestSpec;
use quoted_string::to_content;
use std::time::Duration;

fn benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("quoted-string");
    group
        .noise_threshold(0.10)
        .significance_level(0.01)
        .confidence_level(0.99)
        .sample_size(300)
        .warm_up_time(Duration::from_millis(10))
        .measurement_time(Duration::from_millis(100));

    for input in [
        r#""""#,
        r#""abc""#,
        r#""--==_mimepart_68cbf43c8202e_6c15b8103531""#,
        r#""My file named \"My file\".txt""#,
        r#""\\\\\"a\\""#,
        r#""\\\\\"a\\bcd\\\\\"a\\bcd\\\\\"a\\bcd\\\\\"a\\bcd""#,
    ] {
        group.throughput(Throughput::Bytes(input.len().try_into().unwrap()));
        group.bench_with_input(
            BenchmarkId::new("crate", input),
            input,
            |b, input| b.iter(|| to_content::<TestSpec>(input).unwrap()),
        );
        group.bench_with_input(
            BenchmarkId::new("unquote_string", input),
            &input[1..input.len() - 1], // Strip quotes
            |b, input| b.iter(|| unquote_string(input)),
        );
    }

    group.finish();
}

criterion_group!(general_group, benchmarks);
criterion_main!(general_group);
