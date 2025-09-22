//! Determine relative performance of various ways of constructing a media type.

#![allow(
    clippy::incompatible_msrv,
    clippy::missing_docs_in_private_items,
    missing_docs
)]

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use std::hint::black_box;
use std::time::Duration;

struct IndexMime<T>
where
    T: Into<usize> + From<u8> + Copy,
{
    source: &'static str,
    slash: T,
    plus: Option<T>,
    end: T,
}

trait Mime {
    fn type_(&self) -> &'static str;
    fn subtype(&self) -> &'static str;
    fn suffix(&self) -> Option<&'static str>;
}

impl<T> Mime for IndexMime<T>
where
    T: Into<usize> + From<u8> + Copy,
{
    fn type_(&self) -> &'static str {
        &self.source[0..self.slash.into()]
    }

    fn subtype(&self) -> &'static str {
        &self.source[self.slash.into() + 1..self.end.into()]
    }

    fn suffix(&self) -> Option<&'static str> {
        self.plus
            .map(|plus| &self.source[plus.into() + 1..self.end.into()])
    }
}

struct StrMime {
    type_: &'static str,
    subtype: &'static str,
    suffix: Option<&'static str>,
}

impl Mime for StrMime {
    fn type_(&self) -> &'static str {
        self.type_
    }

    fn subtype(&self) -> &'static str {
        self.subtype
    }

    fn suffix(&self) -> Option<&'static str> {
        self.suffix
    }
}

const INDEX_MIME_TEXT_U8: IndexMime<u8> = IndexMime::<u8> {
    source: "text/plain; charset=utf-8",
    slash: 4,
    plus: None,
    end: 10,
};

const INDEX_MIME_TEXT_U16: IndexMime<u16> = IndexMime::<u16> {
    source: "text/plain; charset=utf-8",
    slash: 4,
    plus: None,
    end: 10,
};

const INDEX_MIME_TEXT_USIZE: IndexMime<usize> = IndexMime::<usize> {
    source: "text/plain; charset=utf-8",
    slash: 4,
    plus: None,
    end: 10,
};

const INDEX_MIME_SVG_U8: IndexMime<u8> = IndexMime::<u8> {
    source: "image/svg+xml",
    slash: 5,
    plus: Some(9),
    end: 13,
};

const INDEX_MIME_SVG_U16: IndexMime<u16> = IndexMime::<u16> {
    source: "image/svg+xml",
    slash: 5,
    plus: Some(9),
    end: 13,
};

const INDEX_MIME_SVG_USIZE: IndexMime<usize> = IndexMime::<usize> {
    source: "image/svg+xml",
    slash: 5,
    plus: Some(9),
    end: 13,
};

/// `text/plain`
const STR_MIME_TEXT: StrMime =
    StrMime { type_: "text", subtype: "plain", suffix: None };

/// `image/svg+xml`
const STR_MIME_SVG: StrMime =
    StrMime { type_: "image", subtype: "svg+xml", suffix: Some("xml") };

fn test_mime<M: Mime>(text: M, svg: M) {
    assert_eq!(black_box(text.type_()), "text");
    assert_eq!(black_box(text.subtype()), "plain");
    assert_eq!(black_box(text.suffix()), None);

    assert_eq!(black_box(svg.type_()), "image");
    assert_eq!(black_box(svg.subtype()), "svg+xml");
    assert_eq!(black_box(svg.suffix()), Some("xml"));
}

fn benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("mime_type");
    group
        .noise_threshold(0.10)
        .significance_level(0.01)
        .confidence_level(0.99)
        .sample_size(300)
        .warm_up_time(Duration::from_millis(10))
        .measurement_time(Duration::from_millis(100));

    group.bench_function(
        BenchmarkId::new("u8", size_of_val(&INDEX_MIME_TEXT_U8)),
        |b| b.iter(|| test_mime(INDEX_MIME_TEXT_U8, INDEX_MIME_SVG_U8)),
    );
    group.bench_function(
        BenchmarkId::new("u16", size_of_val(&INDEX_MIME_TEXT_U16)),
        |b| b.iter(|| test_mime(INDEX_MIME_TEXT_U16, INDEX_MIME_SVG_U16)),
    );
    group.bench_function(
        BenchmarkId::new("usize", size_of_val(&INDEX_MIME_TEXT_USIZE)),
        |b| b.iter(|| test_mime(INDEX_MIME_TEXT_USIZE, INDEX_MIME_SVG_USIZE)),
    );
    group.bench_function(
        BenchmarkId::new("str", size_of_val(&STR_MIME_TEXT)),
        |b| b.iter(|| test_mime(STR_MIME_TEXT, STR_MIME_SVG)),
    );
    // Verify that benchmarks are working — this should take roughly twice as
    // long as the others.
    group.bench_function(BenchmarkId::new("control", 0), |b| {
        b.iter(|| {
            test_mime(STR_MIME_TEXT, STR_MIME_SVG);
            test_mime(INDEX_MIME_TEXT_USIZE, INDEX_MIME_SVG_USIZE);
        })
    });

    group.finish();
}

criterion_group!(general_group, benchmarks);
criterion_main!(general_group);
