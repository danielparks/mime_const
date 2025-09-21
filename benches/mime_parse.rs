//! Determine relative performance of various ways of constructing a media type.

#![allow(
    clippy::incompatible_msrv,
    clippy::missing_docs_in_private_items,
    missing_docs
)]

use criterion::{criterion_group, criterion_main, Criterion};
use mime_const::Parser;
use std::time::Duration;

#[allow(dead_code)]
struct StrMime {
    source: &'static str,
    type_: &'static str,
    subtype: &'static str,
    suffix: Option<&'static str>,
}

fn benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("mime_parse");
    group
        .noise_threshold(0.10)
        .significance_level(0.01)
        .confidence_level(0.99)
        .sample_size(300)
        .warm_up_time(Duration::from_millis(100))
        .measurement_time(Duration::from_secs(1));

    group.bench_function("StrMime literal (text/plain)", |b| {
        b.iter(|| StrMime {
            source: "text/plain",
            type_: "text",
            subtype: "plain",
            suffix: None,
        })
    });

    group.bench_function("StrMime literal (image/svg+xml)", |b| {
        b.iter(|| StrMime {
            source: "image/svg+xml",
            type_: "image",
            subtype: "svg+xml",
            suffix: Some("xml"),
        })
    });

    group.bench_function("parse text/plain", |b| {
        b.iter(|| Parser::type_parser().parse_const("text/plain").unwrap())
    });

    group.bench_function("parse image/svg+xml", |b| {
        b.iter(|| Parser::type_parser().parse_const("image/svg+xml").unwrap())
    });

    group.finish();
}

criterion_group!(general_group, benchmarks);
criterion_main!(general_group);
