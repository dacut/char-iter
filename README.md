# char-iter
Lazily iterate over Unicode characters from a u8 slice in Rust.

This crate provides a `.chars()` method for `Vec<u8>` and `&[u8]` types, allowing you to iterate over the characters
in a byte vector or slice without decoding each character preemptively.

In typical usage, you `use` the `CharIterExt` trait (implemented for `Vec<u8>` and `&[u8]`) and call the `.chars()`
method on those types:

```rust
use char_iter::CharIterExt;
let bread_str: &str = "brød";
let bread_bytes: &[u8] = bread_str.as_bytes();
let mut char_iter = bread_bytes.chars();
assert_eq!(char_iter.next(), Some(Ok('b')));
```

