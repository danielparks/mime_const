//! Determine relative performance of various ways of constructing a media type.

#![allow(
    clippy::incompatible_msrv,
    clippy::missing_docs_in_private_items,
    missing_docs
)]

mod helpers;
use helpers::{rough_parse, rough_parse_cow, test_rough_parse, BigTupleCow};

use criterion::{
    criterion_group, criterion_main, BenchmarkId, Criterion, Throughput,
};
use mime_const::{index, index_u16, index_u8, index_usize, owned, slice};
use std::time::Duration;

trait Mime<'a> {
    fn parse(input: &'a str) -> Self;

    fn big_tuple(&'a self) -> BigTupleCow<'a>;
}

macro_rules! impl_mime {
    ($lt:lifetime, $ty:ty) => {
        impl<$lt> Mime<$lt> for $ty {
            fn parse(input: &$lt str) -> Self {
                Self::constant(input)
            }

            fn big_tuple(&$lt self) -> BigTupleCow<$lt> {
                let mut parameters = self.parameters();
                (self.type_(), self.subtype(), self.suffix(), parameters.next(), parameters.next())
            }
        }
    }
}

impl_mime!('a, index::Mime<'a>);
impl_mime!('a, index_u8::Mime<'a>);
impl_mime!('a, index_u16::Mime<'a>);
impl_mime!('a, index_usize::Mime<'a>);

impl<'a> Mime<'a> for slice::Mime<'a> {
    fn parse(input: &'a str) -> Self {
        let (typ, sub, suffix, param_1, param2) = rough_parse(input);
        slice::Mime::constant(typ, sub, suffix, param_1, param2)
    }

    fn big_tuple(&'a self) -> BigTupleCow<'a> {
        let mut parameters = self.parameters();
        (
            self.type_(),
            self.subtype(),
            self.suffix(),
            parameters.next(),
            parameters.next(),
        )
    }
}

impl<'a> Mime<'a> for owned::Mime {
    fn parse(input: &'a str) -> Self {
        <slice::Mime as Mime>::parse(input).into()
    }

    fn big_tuple(&'a self) -> BigTupleCow<'a> {
        let mut parameters = self.parameters();
        (
            self.type_(),
            self.subtype(),
            self.suffix(),
            parameters.next(),
            parameters.next(),
        )
    }
}

macro_rules! bench {
    ($group:expr, $input:expr, $ty:ty) => {
        let input = $input;
        $group.bench_with_input(
            BenchmarkId::new(
                format!("{} ({}B)", stringify!($ty), size_of::<$ty>()),
                input,
            ),
            &input,
            |b, input| {
                let expected = rough_parse_cow(input);
                let mime: $ty = <$ty as Mime>::parse(input);
                b.iter(|| {
                    let parts = mime.big_tuple();
                    assert_eq!(parts, expected);
                    parts
                })
            },
        );
    };
}

fn benchmarks(c: &mut Criterion) {
    test_rough_parse();

    let mut group = c.benchmark_group("mime_type");
    group
        .noise_threshold(0.10)
        .significance_level(0.01)
        .confidence_level(0.99)
        .sample_size(300)
        .warm_up_time(Duration::from_millis(10))
        .measurement_time(Duration::from_millis(100));

    for input in ["text/plain", "text/plain; charset=utf-8", "image/svg+xml"] {
        group.throughput(Throughput::Bytes(input.len().try_into().unwrap()));
        bench!(&mut group, input, index::Mime);
        bench!(&mut group, input, index_u8::Mime);
        bench!(&mut group, input, index_u16::Mime);
        bench!(&mut group, input, index_usize::Mime);
        bench!(&mut group, input, slice::Mime);
        bench!(&mut group, input, owned::Mime);
    }

    group.finish();
}

criterion_group!(general_group, benchmarks);
criterion_main!(general_group);
