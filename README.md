# mime_const

![Rust version 1.46+](https://img.shields.io/badge/Rust%20version-1.46%2B-success)

```rust
const MARKDOWN: MimeType = MimeType::constant("text/markdown; charset=utf-8");
```

This is an experiment in parsing MIME/media types in `const` context. Presently
this requires a minimum Rust version of 1.46 so we can use `if` and `match` in
`const` context.

See [my comment on hyperium/mime issue #154][comment] for my thoughts on how
this can be applied to the [mime] crate.

### Panic kludge

This uses a horrible kludge to trigger a compile-time panic, since `panic!()` in
`const` requires Rust 1.46.

```rust
#[allow(unconditional_panic, clippy::out_of_bounds_indexing)]
let _: usize = [/*Error parsing MimeType*/][0];
```

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
