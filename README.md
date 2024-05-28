# unicode-linebreak

Modified version of [`unicode-linebreak`] with support for analyzing text
split across multiple non-contiguous chunks.

This is quite an advanced use case: **You probably want to use [`unicode-linebreak`] instead.**

[![Documentation](https://docs.rs/unicode-linebreak-chunked/badge.svg)](https://docs.rs/unicode-linebreak-chunked)

Given an input text, locates "line break opportunities", or positions appropriate for wrapping
lines when displaying text.

## Example

```rust
use unicode_linebreak_chunked::{Linebreaks, BreakOpportunity::{Mandatory, Allowed}};

let mut l = Linebreaks::default();
assert!(l.chunk("a ").eq([]));
assert!(l.chunk("b ").eq([(0, Allowed)]));     // May break after first space
assert!(l.chunk("\nc").eq([(1, Mandatory)]));  // Must break after line feed
assert!(l.chunk("d e").eq([(2, Allowed)]));    // May break after space, no break between chunks
assert_eq!(l.eot(), Some(Mandatory));          // Must break at end of text, so that there always is at least one LB
```

## Development

After cloning the repository or modifying `LineBreak.txt` the tables
have to be (re-)generated:

```sh
# Generate src/tables.rs
(cd gen-tables && cargo run)
# Run tests to make sure it was successful
cargo test
```

[UAX14]: https://www.unicode.org/reports/tr14/
[`unicode-linebreak`]: https://github.com/axelf4/unicode-linebreak
