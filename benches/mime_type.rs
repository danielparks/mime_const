//! Determine relative performance of various ways of constructing a media type.

#![allow(
    clippy::incompatible_msrv,
    clippy::missing_docs_in_private_items,
    missing_docs
)]

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use mime_const::{index, index_u16, index_u8, index_usize, owned, slice};
use std::hint::black_box;
use std::time::Duration;

trait Mime<'a> {
    fn type_(&'a self) -> &'a str;
    fn subtype(&'a self) -> &'a str;
    fn suffix(&'a self) -> Option<&'a str>;
}

impl<'a> Mime<'a> for index::Mime<'a> {
    fn type_(&'a self) -> &'a str {
        self.type_()
    }

    fn subtype(&'a self) -> &'a str {
        self.subtype()
    }

    fn suffix(&'a self) -> Option<&'a str> {
        self.suffix()
    }
}

impl<'a> Mime<'a> for index_u8::Mime<'a> {
    fn type_(&'a self) -> &'a str {
        self.type_()
    }

    fn subtype(&'a self) -> &'a str {
        self.subtype()
    }

    fn suffix(&'a self) -> Option<&'a str> {
        self.suffix()
    }
}

impl<'a> Mime<'a> for index_u16::Mime<'a> {
    fn type_(&'a self) -> &'a str {
        self.type_()
    }

    fn subtype(&'a self) -> &'a str {
        self.subtype()
    }

    fn suffix(&'a self) -> Option<&'a str> {
        self.suffix()
    }
}

impl<'a> Mime<'a> for index_usize::Mime<'a> {
    fn type_(&'a self) -> &'a str {
        self.type_()
    }

    fn subtype(&'a self) -> &'a str {
        self.subtype()
    }

    fn suffix(&'a self) -> Option<&'a str> {
        self.suffix()
    }
}

impl<'a> Mime<'a> for slice::Mime<'a> {
    fn type_(&'a self) -> &'a str {
        self.type_()
    }

    fn subtype(&'a self) -> &'a str {
        self.subtype()
    }

    fn suffix(&'a self) -> Option<&'a str> {
        self.suffix()
    }
}

impl<'a> Mime<'a> for owned::Mime {
    fn type_(&'a self) -> &'a str {
        self.type_()
    }

    fn subtype(&'a self) -> &'a str {
        self.subtype()
    }

    fn suffix(&'a self) -> Option<&'a str> {
        self.suffix()
    }
}

struct IndexMime<T>
where
    T: Into<usize> + From<u8> + Copy,
{
    source: &'static str,
    slash: T,
    plus: Option<T>,
    end: T,
}

impl<T> Mime<'static> for IndexMime<T>
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

impl Mime<'static> for StrMime {
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

const CRATE_INDEX_MIME_TEXT: index::Mime =
    index::Mime::constant("text/plain; charset=utf-8");
const CRATE_INDEX_MIME_SVG: index::Mime =
    index::Mime::constant("image/svg+xml");

const CRATE_INDEX_U8_MIME_TEXT: index_u8::Mime =
    index_u8::Mime::constant("text/plain; charset=utf-8");
const CRATE_INDEX_U8_MIME_SVG: index_u8::Mime =
    index_u8::Mime::constant("image/svg+xml");

const CRATE_INDEX_U16_MIME_TEXT: index_u16::Mime =
    index_u16::Mime::constant("text/plain; charset=utf-16");
const CRATE_INDEX_U16_MIME_SVG: index_u16::Mime =
    index_u16::Mime::constant("image/svg+xml");

const CRATE_INDEX_USIZE_MIME_TEXT: index_usize::Mime =
    index_usize::Mime::constant("text/plain; charset=utf-size");
const CRATE_INDEX_USIZE_MIME_SVG: index_usize::Mime =
    index_usize::Mime::constant("image/svg+xml");

const CRATE_SLICE_MIME_TEXT: slice::Mime = slice::Mime::constant(
    "text",
    "plain",
    None,
    Some(("charset", "utf-8")),
    None,
);
const CRATE_SLICE_MIME_SVG: slice::Mime =
    slice::Mime::constant("image", "svg+xml", Some("xml"), None, None);

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

fn test_mime<'a, M: Mime<'a>>(text: &'a M, svg: &'a M) {
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
        |b| b.iter(|| test_mime(&INDEX_MIME_TEXT_U8, &INDEX_MIME_SVG_U8)),
    );
    group.bench_function(
        BenchmarkId::new("u16", size_of_val(&INDEX_MIME_TEXT_U16)),
        |b| b.iter(|| test_mime(&INDEX_MIME_TEXT_U16, &INDEX_MIME_SVG_U16)),
    );
    group.bench_function(
        BenchmarkId::new("usize", size_of_val(&INDEX_MIME_TEXT_USIZE)),
        |b| b.iter(|| test_mime(&INDEX_MIME_TEXT_USIZE, &INDEX_MIME_SVG_USIZE)),
    );
    group.bench_function(
        BenchmarkId::new("str", size_of_val(&STR_MIME_TEXT)),
        |b| b.iter(|| test_mime(&STR_MIME_TEXT, &STR_MIME_SVG)),
    );
    group.bench_function(
        BenchmarkId::new("index::Mime", size_of_val(&CRATE_INDEX_MIME_TEXT)),
        |b| b.iter(|| test_mime(&CRATE_INDEX_MIME_TEXT, &CRATE_INDEX_MIME_SVG)),
    );
    group.bench_function(
        BenchmarkId::new(
            "index_u8::Mime",
            size_of_val(&CRATE_INDEX_U8_MIME_TEXT),
        ),
        |b| {
            b.iter(|| {
                test_mime(&CRATE_INDEX_U8_MIME_TEXT, &CRATE_INDEX_U8_MIME_SVG)
            })
        },
    );
    group.bench_function(
        BenchmarkId::new(
            "index_u16::Mime",
            size_of_val(&CRATE_INDEX_U16_MIME_TEXT),
        ),
        |b| {
            b.iter(|| {
                test_mime(&CRATE_INDEX_U16_MIME_TEXT, &CRATE_INDEX_U16_MIME_SVG)
            })
        },
    );
    group.bench_function(
        BenchmarkId::new(
            "index_usize::Mime",
            size_of_val(&CRATE_INDEX_USIZE_MIME_TEXT),
        ),
        |b| {
            b.iter(|| {
                test_mime(
                    &CRATE_INDEX_USIZE_MIME_TEXT,
                    &CRATE_INDEX_USIZE_MIME_SVG,
                )
            })
        },
    );
    group.bench_function(
        BenchmarkId::new("slice::Mime", size_of_val(&CRATE_SLICE_MIME_TEXT)),
        |b| b.iter(|| test_mime(&CRATE_SLICE_MIME_TEXT, &CRATE_SLICE_MIME_SVG)),
    );
    let owned_mime_text: owned::Mime = CRATE_SLICE_MIME_TEXT.into();
    let owned_mime_svg: owned::Mime = CRATE_SLICE_MIME_SVG.into();
    group.bench_function(
        BenchmarkId::new("owned::Mime", size_of_val(&owned_mime_text)),
        |b| b.iter(|| test_mime(&owned_mime_text, &owned_mime_svg)),
    );
    // Verify that benchmarks are working — this should take roughly twice as
    // long as the others.
    group.bench_function(BenchmarkId::new("control", 0), |b| {
        b.iter(|| {
            test_mime(&STR_MIME_TEXT, &STR_MIME_SVG);
            test_mime(&INDEX_MIME_TEXT_USIZE, &INDEX_MIME_SVG_USIZE);
        });
    });

    group.finish();
}

criterion_group!(general_group, benchmarks);
criterion_main!(general_group);
