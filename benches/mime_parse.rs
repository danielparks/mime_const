//! Determine relative performance of various ways of constructing a media type.

#![allow(
    clippy::incompatible_msrv,
    clippy::missing_docs_in_private_items,
    missing_docs
)]

use criterion::{criterion_group, criterion_main, Criterion};
use mime_const::index::Mime as IndexMime;
use mime_const::slice::Mime as StrMime;
use mime_const::slice::Parameter as StrParameter;
use std::time::Duration;

fn benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("mime_parse");
    group
        .noise_threshold(0.10)
        .significance_level(0.01)
        .confidence_level(0.99)
        .sample_size(300)
        .warm_up_time(Duration::from_millis(10))
        .measurement_time(Duration::from_millis(100));

    group.bench_function("StrMime literal (text/plain)", |b| {
        b.iter(|| StrMime::new("text", "plain", None, None, None))
    });

    group.bench_function("StrMime literal (text/plain; charset=utf-8)", |b| {
        b.iter(|| {
            StrMime::new(
                "text",
                "plain",
                None,
                Some(StrParameter::new("charset", "utf-8").unwrap()),
                None,
            )
        })
    });

    group.bench_function("StrMime literal (image/svg+xml)", |b| {
        b.iter(|| StrMime::new("image", "svg+xml", Some("xml"), None, None))
    });

    group.bench_function("parse text/plain", |b| {
        b.iter(|| IndexMime::constant("text/plain"))
    });

    group.bench_function("parse text/plain; charset=utf-8", |b| {
        b.iter(|| IndexMime::constant("text/plain; charset=utf-8"))
    });

    group.bench_function("parse image/svg+xml", |b| {
        b.iter(|| IndexMime::constant("image/svg+xml"))
    });

    group.finish();
}

criterion_group!(general_group, benchmarks);
criterion_main!(general_group);
