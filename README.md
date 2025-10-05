# mime_const

![Rust version 1.57+](https://img.shields.io/badge/Rust%20version-1.57%2B-success)

```rust
const MARKDOWN: MimeType = MimeType::constant("text/markdown; charset=utf-8");
```

This is an experiment in parsing MIME/media types in `const` context. It
requires a minimum Rust version of 1.57 so we can `panic!` in`const` context.

See [my comment on hyperium/mime issue #154][comment] for my thoughts on how
this can be applied to the [mime] crate.

## Benchmarking

There are hard-to-read benchmark results for various implementation strategies
at [`target/criterion/reports/index.html`].

The gist of the results:

* Storing the parts of a MIME/media type as `&str` or `String` allows for the
  fastest access to the components, e.g. the subtype. Storing the parts as
  indices is roughly 30% slower.
* Parsing to indices is about 30% slower than just passing the components as
  individual `&str`s and then validating them.
* Storing the indices as `u8` or `u16` gives marginally better parse and access
  times than using `usize`.

## Other interesting crates

  * [mime_typed](https://crates.io/crates/mime_typed) extends [mime].
  * [mediatype](https://crates.io/crates/mediatype/) has a different approach to
    `const` context.

## License

Unless otherwise noted, this project is dual-licensed under the Apache 2 and MIT
licenses. You may choose to use either.

  * [Apache License, Version 2.0](LICENSE-APACHE)
  * [MIT license](LICENSE-MIT)

### Contributions

Unless you explicitly state otherwise, any contribution you submit as defined
in the Apache 2.0 license shall be dual licensed as above, without any
additional terms or conditions.

[comment]: https://github.com/hyperium/mime/issues/154#issuecomment-3285927661
[mime]: https://crates.io/crates/mime
