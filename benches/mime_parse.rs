//! Determine relative performance of various ways of constructing a media type.

#![allow(
    clippy::incompatible_msrv,
    clippy::missing_docs_in_private_items,
    missing_docs
)]

use criterion::{criterion_group, criterion_main, Criterion};
use mime_const::index;
use mime_const::slice;
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

    // No reason to benchmark the creation of `owned::Mime`; it’s created by
    // converting from a `slice::Mime` for convenience.

    group.bench_function("slice::Mime literal (text/plain)", |b| {
        b.iter(|| slice::Mime::new("text", "plain", None, None, None).unwrap());
    });

    group.bench_function(
        "slice::Mime literal (text/plain; charset=utf-8)",
        |b| {
            b.iter(|| {
                slice::Mime::new(
                    "text",
                    "plain",
                    None,
                    Some(slice::Parameter::new("charset", "utf-8").unwrap()),
                    None,
                )
                .unwrap()
            });
        },
    );

    group.bench_function("slice::Mime literal (image/svg+xml)", |b| {
        b.iter(|| {
            slice::Mime::new("image", "svg+xml", Some("xml"), None, None)
                .unwrap()
        });
    });

    group.bench_function("index::Mime parse text/plain", |b| {
        b.iter(|| index::Mime::constant("text/plain"));
    });

    group.bench_function("ndex::Mime parse text/plain; charset=utf-8", |b| {
        b.iter(|| index::Mime::constant("text/plain; charset=utf-8"));
    });

    group.bench_function("ndex::Mime parse image/svg+xml", |b| {
        b.iter(|| index::Mime::constant("image/svg+xml"));
    });

    group.finish();
}

criterion_group!(general_group, benchmarks);
criterion_main!(general_group);
