# mime_const

![Rust version 1.57+](https://img.shields.io/badge/Rust%20version-1.57%2B-success)

This is an experiment in parsing MIME/media types in `const` context. Presently
this requires a minimum Rust version of 1.57 so that we can `panic!()` in a
`const fn`, but that could be moved back if we hid the function that panics on
error behind a feature.

Most of the time people will want a compile-time panic in code like:

```rust
const MARKDOWN: MimeType = MimeType::constant("text/markdown; charset=utf-8");
```

## License

This project dual-licensed under the Apache 2 and MIT licenses. You may choose
to use either.

  * [Apache License, Version 2.0](LICENSE-APACHE)
  * [MIT license](LICENSE-MIT)

### Contributions

Unless you explicitly state otherwise, any contribution you submit as defined
in the Apache 2.0 license shall be dual licensed as above, without any
additional terms or conditions.

[docs.rs]: https://docs.rs/mime_const/latest/mime_test/
[crates.io]: https://crates.io/crates/mime_const
[issues]: https://github.com/danielparks/mime_const/issues
