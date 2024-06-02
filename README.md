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
assert_eq!(l.chunk("a ", 0), None);

// May break after first space
assert_eq!(l.chunk("b ", 0), Some((0, 1, Allowed)));
assert_eq!(l.chunk("b ", 1), None);

// Must break after line feed
assert_eq!(l.chunk("\nc", 0), Some((1, 2, Mandatory)));
assert_eq!(l.chunk("\nc", 2), None);

// May break after space, no break between chunks
assert_eq!(l.chunk("d e", 0), Some((2, 3, Allowed)));
assert_eq!(l.chunk("d e", 3), None);

// Must break at end of text, so that there always is at least one LB
assert_eq!(l.eot(), Some(Mandatory));
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
