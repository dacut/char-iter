//! This crate provides a `.chars()` method for `Vec<u8>` and `&[u8]` types, allowing you to iterate over the characters
//! in a byte vector or slice without decoding each character preemptively.
//!
//! In typical usage, you `use` the `CharIterExt` trait (implemented for `Vec<u8>` and `&[u8]`) and call the `.chars()`
//! method on those types:
//!
//! ```
//! use char_iter::CharIterExt;
//!
//! let bread_str: &str = "brød";
//! let bread_bytes: &[u8] = bread_str.as_bytes();
//! let mut char_iter = bread_bytes.chars();
//! assert_eq!(char_iter.next(), Some(Ok('b')));
//! ```
#![warn(clippy::all)]

use std::{
    error::Error,
    fmt::{Display, Formatter, Result as FmtResult},
    iter::{DoubleEndedIterator, FusedIterator, Iterator},
};

/// Iterate over the characters in a given type.
pub trait CharIterExt {
    type Iter;

    /// Returns an iterator over the `char`s of the given type.
    ///
    /// Since the underlying type is not guaranteed to be valid UTF-8, the iterator will return
    /// `Option<Result<char, Utf8Error>>` instead of just `char`
    ///
    /// It's important to remember that char represents a Unicode Scalar Value, and might not match your idea of what a
    /// ‘character’ is. Iteration over grapheme clusters may be what you actually want. This functionality is not
    /// provided here; check (crates.io)[<https://crates.io>] instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use char_iter::CharIterExt;
    ///
    /// let bread_str: &str = "brød";
    /// let bread_bytes: &[u8] = bread_str.as_bytes();
    /// assert!(bread_bytes.len() == 5); // ø is \xc3\xb8
    ///
    /// let mut char_iter = bread_bytes.chars();
    /// assert_eq!(char_iter.next(), Some(Ok('b')));
    /// assert_eq!(char_iter.next(), Some(Ok('r')));
    /// assert_eq!(char_iter.next(), Some(Ok('ø')));
    /// assert_eq!(char_iter.next(), Some(Ok('d')));
    /// assert_eq!(char_iter.next(), None);
    /// ```
    ///
    /// Invalid UTF-8 results in an error when the invalid character is hit:
    ///
    /// ```
    /// use char_iter::{CharIterExt, Utf8Error};
    ///
    /// let invalid = vec![b'b', b'r', b'\xc3', b'\xc3', b'd'];
    /// let invalid_bytes: &[u8] = invalid.as_slice();
    ///
    /// let mut char_iter = invalid_bytes.chars();
    /// assert_eq!(char_iter.next(), Some(Ok('b')));
    /// assert_eq!(char_iter.next(), Some(Ok('r')));
    /// assert_eq!(char_iter.next(), Some(Err(Utf8Error::InvalidEncoding(vec![0xc3, 0xc3]))));
    /// ```
    fn chars(&self) -> Self::Iter;
}

/// The resulting iterator returned when `.chars()` is called on a `&[u8]`.
#[derive(Clone, Debug)]
pub struct CharSliceIter<'a> {
    slice_iter: ::std::slice::Iter<'a, u8>,
}

impl<'a> CharSliceIter<'a> {
    /// Returns the undecoded remainder of the slice.
    ///
    /// This has the same lifetime as the original slice, so the iterator can continue to be used while this exists.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use char_iter::CharIterExt;
    ///
    /// let bread_str: &str = "brød";
    /// let bread_bytes: &[u8] = bread_str.as_bytes();
    ///
    /// // Iterate over the characters.
    /// let mut char_iter = bread_bytes.chars();
    ///
    /// // If we print the remaining characters, we have "[98, 114, 195, 184, 100]" (the UTF-8 bytes for "brød").
    /// assert_eq!(format!("{:?}", char_iter.remaining()), "[98, 114, 195, 184, 100]");
    ///
    /// // Move to the fourth character of the slice.
    /// char_iter.next();
    /// char_iter.next();
    /// char_iter.next();
    ///
    /// // Now the remaining character is "[100]".
    /// assert_eq!(format!("{:?}", char_iter.remaining()), "[100]");
    /// ```
    pub fn remaining(&self) -> &'a [u8] {
        self.slice_iter.as_slice()
    }
}

impl<'a> AsRef<[u8]> for CharSliceIter<'a> {
    #[inline]
    fn as_ref(&self) -> &'a [u8] {
        self.slice_iter.as_slice()
    }
}

impl<'a> Iterator for CharSliceIter<'a> {
    type Item = Result<char, Utf8Error>;

    fn next(&mut self) -> Option<Self::Item> {
        let b1 = *(self.slice_iter.next()?);

        let c = if b1 & 0x80 == 0 {
            // Single byte character.
            b1 as u32
        } else if b1 & 0b1110_0000 == 0b1100_0000 {
            // Two byte character.
            let b2 = match self.slice_iter.next() {
                Some(b) => *b,
                None => return Some(Err(Utf8Error::Truncated(vec![b1]))),
            };

            if b2 & 0b1100_0000 != 0b1000_0000 {
                return Some(Err(Utf8Error::InvalidEncoding(vec![b1, b2])));
            }

            let result = ((b1 & 0b0001_1111) as u32) << 6 | (b2 & 0b0011_1111) as u32;
            if result < 0x80 {
                return Some(Err(Utf8Error::OverlongEncoding(vec![b1, b2])));
            }

            result
        } else if b1 & 0b1111_0000 == 0b1110_0000 {
            // Three byte character.
            let b2 = match self.slice_iter.next() {
                Some(b) => *b,
                None => return Some(Err(Utf8Error::Truncated(vec![b1]))),
            };

            if b2 & 0b1100_0000 != 0b1000_0000 {
                return Some(Err(Utf8Error::InvalidEncoding(vec![b1, b2])));
            }

            let b3 = match self.slice_iter.next() {
                Some(b) => *b,
                None => return Some(Err(Utf8Error::Truncated(vec![b1, b2]))),
            };

            if b3 & 0b1100_0000 != 0b1000_0000 {
                return Some(Err(Utf8Error::InvalidEncoding(vec![b1, b2, b3])));
            }

            let result =
                ((b1 & 0b0000_1111) as u32) << 12 | ((b2 & 0b0011_1111) as u32) << 6 | (b3 & 0b0011_1111) as u32;
            if result < 0x800 {
                return Some(Err(Utf8Error::OverlongEncoding(vec![b1, b2, b3])));
            }

            result
        } else if b1 & 0b1111_1000 == 0b1111_0000 {
            // Four byte character.
            let b2 = match self.slice_iter.next() {
                Some(b) => *b,
                None => return Some(Err(Utf8Error::Truncated(vec![b1]))),
            };

            if b2 & 0b1100_0000 != 0b1000_0000 {
                return Some(Err(Utf8Error::InvalidEncoding(vec![b1, b2])));
            }

            let b3 = match self.slice_iter.next() {
                Some(b) => *b,
                None => return Some(Err(Utf8Error::Truncated(vec![b1, b2]))),
            };

            if b3 & 0b1100_0000 != 0b1000_0000 {
                return Some(Err(Utf8Error::InvalidEncoding(vec![b1, b2, b3])));
            }

            let b4 = match self.slice_iter.next() {
                Some(b) => *b,
                None => return Some(Err(Utf8Error::Truncated(vec![b1, b2, b3]))),
            };

            if b4 & 0b1100_0000 != 0b1000_0000 {
                return Some(Err(Utf8Error::InvalidEncoding(vec![b1, b2, b3, b4])));
            }

            let result = ((b1 & 0b0000_0111) as u32) << 18
                | ((b2 & 0b0011_1111) as u32) << 12
                | ((b3 & 0b0011_1111) as u32) << 6
                | (b4 & 0b0011_1111) as u32;
            if result < 0x10000 {
                return Some(Err(Utf8Error::OverlongEncoding(vec![b1, b2, b3, b4])));
            }

            result
        } else {
            // Invalid lead byte.
            return Some(Err(Utf8Error::InvalidEncoding(vec![b1])));
        };

        match char::from_u32(c) {
            Some(c) => Some(Ok(c)),
            None => Some(Err(Utf8Error::InvalidCodepoint(c))),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // Lower bound is the number of bytes in the slice divided by 4 (the maximum number of bytes per character).
        // Upper bound is the number of bytes in the slice.
        let upper = self.slice_iter.len();
        let mut lower = upper / 4;
        if upper % 4 > 0 {
            lower += 1;
        }

        (lower, Some(upper))
    }
}

impl<'a> DoubleEndedIterator for CharSliceIter<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let b1 = *(self.slice_iter.next_back()?);

        let c = if b1 & 0b1100_0000 == 0b1000_0000 {
            // Continuation byte (2-4 byte encoding). Find the lead byte.
            let b2 = match self.slice_iter.next_back() {
                Some(b) => *b,
                None => return Some(Err(Utf8Error::Truncated(vec![b1]))),
            };

            if b2 & 0b1100_0000 == 0b1000_0000 {
                // Second continuation byte (3-4 byte encoding). Keep scanning to find the lead byte.
                let b3 = match self.slice_iter.next_back() {
                    Some(b) => *b,
                    None => return Some(Err(Utf8Error::Truncated(vec![b2, b1]))),
                };

                if b3 & 0b1100_0000 == 0b1000_0000 {
                    // Third continuation byte (4 byte encoding). Next byte *must* be the lead byte.
                    let b4 = match self.slice_iter.next_back() {
                        Some(b) => *b,
                        None => return Some(Err(Utf8Error::Truncated(vec![b3, b2, b1]))),
                    };

                    if b4 & 0b1111_1000 != 0b1111_0000 {
                        return Some(Err(Utf8Error::InvalidEncoding(vec![b4, b3, b2, b1])));
                    }

                    let result = ((b4 & 0b0000_0111) as u32) << 18
                        | ((b3 & 0b0011_1111) as u32) << 12
                        | ((b2 & 0b0011_1111) as u32) << 6
                        | (b1 & 0b0011_1111) as u32;
                    if result < 0x10000 {
                        return Some(Err(Utf8Error::OverlongEncoding(vec![b4, b3, b2, b1])));
                    }
                    result
                } else if b3 & 0b1111_0000 != 0b1110_0000 {
                    return Some(Err(Utf8Error::InvalidEncoding(vec![b3, b2, b1])));
                } else {
                    // 3 byte encoding.
                    let result = ((b3 & 0b0001_1111) as u32) << 12
                        | ((b2 & 0b0011_1111) as u32) << 6
                        | (b1 & 0b0011_1111) as u32;
                    if result < 0x800 {
                        return Some(Err(Utf8Error::OverlongEncoding(vec![b3, b2, b1])));
                    }
                    result
                }
            } else if b2 & 0b1110_0000 != 0b1100_0000 {
                return Some(Err(Utf8Error::InvalidEncoding(vec![b2, b1])));
            } else {
                let result = ((b2 & 0b0001_1111) as u32) << 6 | (b1 & 0b0011_1111) as u32;
                if result < 0x80 {
                    return Some(Err(Utf8Error::OverlongEncoding(vec![b2, b1])));
                }
                result
            }
        } else if b1 & 0b1000_0000 != 0b0000_0000 {
            // Lead byte found without continuation byte(s).
            return Some(Err(Utf8Error::InvalidEncoding(vec![b1])));
        } else {
            b1 as u32
        };

        match char::from_u32(c) {
            Some(c) => Some(Ok(c)),
            None => Some(Err(Utf8Error::InvalidCodepoint(c))),
        }
    }
}

impl<'a> FusedIterator for CharSliceIter<'a> {}

impl<'a> CharIterExt for &'a [u8] {
    type Iter = CharSliceIter<'a>;

    fn chars(&self) -> Self::Iter {
        CharSliceIter {
            slice_iter: self.iter(),
        }
    }
}

impl<'a> CharIterExt for &'a Vec<u8> {
    type Iter = CharSliceIter<'a>;

    fn chars(&self) -> Self::Iter {
        CharSliceIter {
            slice_iter: self.iter(),
        }
    }
}

/// The errors that can occur when decoding UTF-8.
#[derive(Debug, Eq, PartialEq)]
pub enum Utf8Error {
    /// The codepoint is not a valid Unicode codepoint.
    InvalidCodepoint(u32),

    /// The encoding is not valid UTF-8.
    InvalidEncoding(Vec<u8>),

    /// The encoding is "overlong," e.g., a two-byte UTF-8 encoding of a codepoint that could be encoded in a single
    /// byte. This is not allowed in UTF-8 for security reasons.
    OverlongEncoding(Vec<u8>),

    /// The character was truncated when being decoded.
    Truncated(Vec<u8>),
}

impl Display for Utf8Error {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self {
            Utf8Error::InvalidCodepoint(c) => write!(f, "Invalid Unicode codepoint: {c:#x}"),
            Utf8Error::InvalidEncoding(bytes) => {
                write!(f, "Invalid UTF-8 encoding: [")?;
                for (i, b) in bytes.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{b:#04x}")?;
                }
                write!(f, "]")
            }
            Utf8Error::OverlongEncoding(bytes) => {
                write!(f, "Overlong UTF-8 encoding: [")?;
                for (i, b) in bytes.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{b:#04x}")?;
                }
                write!(f, "]")
            }
            Utf8Error::Truncated(bytes) => {
                write!(f, "Truncated UTF-8 character: [")?;
                for (i, b) in bytes.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{b:#04x}")?;
                }
                write!(f, "]")
            }
        }
    }
}

impl Error for Utf8Error {}

#[cfg(test)]
mod tests {
    use super::{CharIterExt, Utf8Error};

    #[test]
    fn test_good() {
        // Characters: a \u{0061}, á \u{00e1}, ḁ \u{1e01}, 𝒜 \u{1d49c}
        let v = vec![0x61, 0xc3, 0xa1, 0xe1, 0xb8, 0x81, 0xf0, 0x9d, 0x92, 0x9c];
        let mut chars = (&v).chars();
        let mut chars2 = chars.clone();
        assert_eq!(chars.next(), Some(Ok('a')));
        assert_eq!(chars.remaining(), &vec![0xc3, 0xa1, 0xe1, 0xb8, 0x81, 0xf0, 0x9d, 0x92, 0x9c]);
        assert_eq!(chars.as_ref(), &vec![0xc3, 0xa1, 0xe1, 0xb8, 0x81, 0xf0, 0x9d, 0x92, 0x9c]);
        assert_eq!(chars.next(), Some(Ok('á')));
        assert_eq!(chars.remaining(), &vec![0xe1, 0xb8, 0x81, 0xf0, 0x9d, 0x92, 0x9c]);
        assert_eq!(chars.as_ref(), &vec![0xe1, 0xb8, 0x81, 0xf0, 0x9d, 0x92, 0x9c]);
        assert_eq!(chars.next(), Some(Ok('ḁ')));
        assert_eq!(chars.remaining(), &vec![0xf0, 0x9d, 0x92, 0x9c]);
        assert_eq!(chars.as_ref(), &vec![0xf0, 0x9d, 0x92, 0x9c]);
        assert_eq!(chars.next(), Some(Ok('𝒜')));
        assert_eq!(chars.remaining(), &vec![]);
        assert_eq!(chars.as_ref(), &vec![]);
        assert_eq!(chars.next(), None);
        assert_eq!(chars2.next_back(), Some(Ok('𝒜')));
        assert_eq!(chars2.remaining(), &vec![0x61, 0xc3, 0xa1, 0xe1, 0xb8, 0x81]);
        assert_eq!(chars2.as_ref(), &vec![0x61, 0xc3, 0xa1, 0xe1, 0xb8, 0x81]);
        assert_eq!(chars2.next_back(), Some(Ok('ḁ')));
        assert_eq!(chars2.remaining(), &vec![0x61, 0xc3, 0xa1]);
        assert_eq!(chars2.as_ref(), &vec![0x61, 0xc3, 0xa1]);
        assert_eq!(chars2.next_back(), Some(Ok('á')));
        assert_eq!(chars2.remaining(), &vec![0x61]);
        assert_eq!(chars2.as_ref(), &vec![0x61]);
        assert_eq!(chars2.next_back(), Some(Ok('a')));
        assert_eq!(chars2.remaining(), &vec![]);
        assert_eq!(chars2.as_ref(), &vec![]);
        assert_eq!(chars2.next_back(), None);
    }

    #[test]
    fn test_empty_vec() {
        let v = vec![];
        let mut chars = (&v).chars();
        assert!(chars.next().is_none());

        assert_eq!(chars.size_hint(), (0, Some(0)));

        // Make sure we can debug print.
        let _ = format!("{chars:?}");
    }

    #[test]
    fn test_truncated_forward() {
        // Two byte encoding
        let v = vec![0xc0];
        let mut chars = (&v).chars();
        let e = chars.next().unwrap().unwrap_err();
        assert_eq!(e, Utf8Error::Truncated(vec![0xc0]));

        // Three byte encoding
        let v = vec![0xe0];
        let mut chars = (&v).chars();
        let e = chars.next().unwrap().unwrap_err();
        assert_eq!(e, Utf8Error::Truncated(vec![0xe0]));

        let v = vec![0xe0, 0x80];
        let mut chars = (&v).chars();
        let e = chars.next().unwrap().unwrap_err();
        assert_eq!(e, Utf8Error::Truncated(vec![0xe0, 0x80]));

        // Four byte encoding
        let v = vec![0xf0];
        let mut chars = (&v).chars();
        let e = chars.next().unwrap().unwrap_err();
        assert_eq!(e, Utf8Error::Truncated(vec![0xf0]));

        let v = vec![0xf0, 0x80];
        let mut chars = (&v).chars();
        let e = chars.next().unwrap().unwrap_err();
        assert_eq!(e, Utf8Error::Truncated(vec![0xf0, 0x80]));

        let v = vec![0xf0, 0x80, 0x80];
        let mut chars = (&v).chars();
        let e = chars.next().unwrap().unwrap_err();
        assert_eq!(e, Utf8Error::Truncated(vec![0xf0, 0x80, 0x80]));
    }

    #[test]
    fn test_truncated_backward() {
        let v = vec![0x80];
        let mut chars = (&v).chars();
        let e = chars.next_back().unwrap().unwrap_err();
        assert_eq!(e, Utf8Error::Truncated(vec![0x80]));
        assert_eq!(format!("{e:?}"), "Truncated([128])");
        assert_eq!(format!("{e}"), "Truncated UTF-8 character: [0x80]");

        let v = vec![0x80, 0x80];
        let mut chars = (&v).chars();
        let e = chars.next_back().unwrap().unwrap_err();
        assert_eq!(e, Utf8Error::Truncated(vec![0x80, 0x80]));
        assert_eq!(format!("{e:?}"), "Truncated([128, 128])");
        assert_eq!(format!("{e}"), "Truncated UTF-8 character: [0x80, 0x80]");

        let v = vec![0x80, 0x80, 0x80];
        let mut chars = (&v).chars();
        let e = chars.next_back().unwrap().unwrap_err();
        assert_eq!(e, Utf8Error::Truncated(vec![0x80, 0x80, 0x80]));
        assert_eq!(format!("{e}"), "Truncated UTF-8 character: [0x80, 0x80, 0x80]");

        let v = vec![0x80, 0x80, 0x80, 0x80];
        let mut chars = (&v).chars();
        let e = chars.next_back().unwrap().unwrap_err();
        assert_eq!(e, Utf8Error::InvalidEncoding(vec![0x80, 0x80, 0x80, 0x80]));
        assert_eq!(format!("{e:?}"), "InvalidEncoding([128, 128, 128, 128])");
        assert_eq!(format!("{e}"), "Invalid UTF-8 encoding: [0x80, 0x80, 0x80, 0x80]");
    }

    #[test]
    fn test_overlong() {
        // Two bytes
        let v = vec![0xc0, 0x80, 0x00];
        let mut chars = (&v).chars();
        assert_eq!(chars.size_hint(), (1, Some(3)));
        let e = chars.next().unwrap().unwrap_err();
        assert_eq!(e, Utf8Error::OverlongEncoding(vec![0xc0, 0x80]));
        assert_eq!(format!("{e:?}"), "OverlongEncoding([192, 128])");
        assert_eq!(format!("{e}"), "Overlong UTF-8 encoding: [0xc0, 0x80]");

        let v = vec![0x00, 0xc0, 0x80];
        let mut chars = (&v).chars();
        assert_eq!(chars.size_hint(), (1, Some(3)));
        let e = chars.next_back().unwrap().unwrap_err();
        assert_eq!(e, Utf8Error::OverlongEncoding(vec![0xc0, 0x80]));
        assert_eq!(format!("{e:?}"), "OverlongEncoding([192, 128])");
        assert_eq!(format!("{e}"), "Overlong UTF-8 encoding: [0xc0, 0x80]");

        // Three bytes
        let v = vec![0xe0, 0x80, 0x80, 0x00];
        let mut chars = (&v).chars();
        assert_eq!(chars.size_hint(), (1, Some(4)));
        let e = chars.next().unwrap().unwrap_err();
        assert_eq!(e, Utf8Error::OverlongEncoding(vec![0xe0, 0x80, 0x80]));
        assert_eq!(format!("{e:?}"), "OverlongEncoding([224, 128, 128])");
        assert_eq!(format!("{e}"), "Overlong UTF-8 encoding: [0xe0, 0x80, 0x80]");

        let v = vec![0x00, 0xe0, 0x80, 0x80];
        let mut chars = (&v).chars();
        assert_eq!(chars.size_hint(), (1, Some(4)));
        let e = chars.next_back().unwrap().unwrap_err();
        assert_eq!(e, Utf8Error::OverlongEncoding(vec![0xe0, 0x80, 0x80]));
        assert_eq!(format!("{e:?}"), "OverlongEncoding([224, 128, 128])");
        assert_eq!(format!("{e}"), "Overlong UTF-8 encoding: [0xe0, 0x80, 0x80]");

        // Four bytes
        let v = vec![0xf0, 0x80, 0x80, 0x80, 0x00];
        let mut chars = (&v).chars();
        assert_eq!(chars.size_hint(), (2, Some(5)));
        let e = chars.next().unwrap().unwrap_err();
        assert_eq!(e, Utf8Error::OverlongEncoding(vec![0xf0, 0x80, 0x80, 0x80]));
        assert_eq!(format!("{e:?}"), "OverlongEncoding([240, 128, 128, 128])");
        assert_eq!(format!("{e}"), "Overlong UTF-8 encoding: [0xf0, 0x80, 0x80, 0x80]");

        let v = vec![0x00, 0xf0, 0x80, 0x80, 0x80];
        let mut chars = (&v).chars();
        assert_eq!(chars.size_hint(), (2, Some(5)));
        let e = chars.next_back().unwrap().unwrap_err();
        assert_eq!(e, Utf8Error::OverlongEncoding(vec![0xf0, 0x80, 0x80, 0x80]));
        assert_eq!(format!("{e:?}"), "OverlongEncoding([240, 128, 128, 128])");
        assert_eq!(format!("{e}"), "Overlong UTF-8 encoding: [0xf0, 0x80, 0x80, 0x80]");
    }

    #[test]
    fn test_invalid_codepoint() {
        let v = vec![0xf4, 0x90, 0x80, 0x80];
        let mut chars = (&v).chars();
        assert_eq!(chars.size_hint(), (1, Some(4)));
        let e = chars.next().unwrap().unwrap_err();
        assert_eq!(e, Utf8Error::InvalidCodepoint(0x110000));
        assert_eq!(format!("{e:?}"), "InvalidCodepoint(1114112)");
        assert_eq!(format!("{e}"), "Invalid Unicode codepoint: 0x110000");
    }

    #[test]
    fn test_invalid_encoding() {
        let v = vec![0x80, 0x0, 0x0];
        let mut chars = (&v).chars();
        let mut chars2 = chars.clone();
        assert_eq!(chars.size_hint(), (1, Some(3)));
        assert_eq!(chars.next(), Some(Err(Utf8Error::InvalidEncoding(vec![0x80]))));
        assert_eq!(chars2.next_back(), Some(Ok('\0')));
        assert_eq!(chars2.next_back(), Some(Ok('\0')));
        assert_eq!(chars2.next_back(), Some(Err(Utf8Error::Truncated(vec![0x80]))));

        let v = vec![0xc0, 0xc3, 0xbf];
        let mut chars = (&v).chars();
        let mut chars2 = chars.clone();
        assert_eq!(chars.size_hint(), (1, Some(3)));
        assert_eq!(chars.next(), Some(Err(Utf8Error::InvalidEncoding(vec![0xc0, 0xc3]))));
        assert_eq!(chars2.next_back(), Some(Ok('ÿ')));
        assert_eq!(chars2.next_back(), Some(Err(Utf8Error::InvalidEncoding(vec![0xc0]))));

        let v = vec![0xe0, 0xc3, 0xbf];
        let mut chars = (&v).chars();
        let mut chars2 = chars.clone();
        assert_eq!(chars.size_hint(), (1, Some(3)));
        assert_eq!(chars.next(), Some(Err(Utf8Error::InvalidEncoding(vec![0xe0, 0xc3]))));
        assert_eq!(chars2.next_back(), Some(Ok('ÿ')));
        assert_eq!(chars2.next_back(), Some(Err(Utf8Error::InvalidEncoding(vec![0xe0]))));

        let v = vec![0xe0, 0x80, 0xc0];
        let mut chars = (&v).chars();
        let mut chars2 = chars.clone();
        assert_eq!(chars.size_hint(), (1, Some(3)));
        assert_eq!(chars.next(), Some(Err(Utf8Error::InvalidEncoding(vec![0xe0, 0x80, 0xc0]))));
        assert_eq!(chars2.next_back(), Some(Err(Utf8Error::InvalidEncoding(vec![0xc0]))));
        assert_eq!(chars2.next_back(), Some(Err(Utf8Error::InvalidEncoding(vec![0xe0, 0x80]))));

        let v = vec![0xf0, 0xc0, 0x80, 0x80];
        let mut chars = (&v).chars();
        let mut chars2 = chars.clone();
        assert_eq!(chars.size_hint(), (1, Some(4)));
        assert_eq!(chars.next(), Some(Err(Utf8Error::InvalidEncoding(vec![0xf0, 0xc0]))));
        assert_eq!(chars2.next_back(), Some(Err(Utf8Error::InvalidEncoding(vec![0xc0, 0x80, 0x80]))));

        let v = vec![0xf0, 0x80, 0xc3, 0xbf];
        let mut chars = (&v).chars();
        let mut chars2 = chars.clone();
        assert_eq!(chars.size_hint(), (1, Some(4)));
        assert_eq!(chars.next(), Some(Err(Utf8Error::InvalidEncoding(vec![0xf0, 0x80, 0xc3]))));
        assert_eq!(chars2.next_back(), Some(Ok('ÿ')));
        assert_eq!(chars2.next_back(), Some(Err(Utf8Error::InvalidEncoding(vec![0xf0, 0x80]))));

        let v = vec![0xf0, 0x80, 0x80, 0xc0];
        let mut chars = (&v).chars();
        let mut chars2 = chars.clone();
        assert_eq!(chars.size_hint(), (1, Some(4)));
        assert_eq!(chars.next(), Some(Err(Utf8Error::InvalidEncoding(vec![0xf0, 0x80, 0x80, 0xc0]))));
        assert_eq!(chars2.next_back(), Some(Err(Utf8Error::InvalidEncoding(vec![0xc0]))));
        assert_eq!(chars2.next_back(), Some(Err(Utf8Error::InvalidEncoding(vec![0xf0, 0x80, 0x80]))));
    }

    #[test]
    fn test_double_ended() {
        let bread = "brød";
        let bread_bytes = bread.as_bytes();
        let mut chars = bread_bytes.chars();
        assert_eq!(chars.next_back(), Some(Ok('d')));
        assert_eq!(chars.next_back(), Some(Ok('ø')));
        assert_eq!(chars.next(), Some(Ok('b')));
        assert_eq!(chars.next_back(), Some(Ok('r')));
        assert_eq!(chars.next_back(), None);
    }

    #[test]
    fn test_double_ended_invalid_codepoint() {
        let v = vec![0x0, 0xf7, 0xaf, 0xaf, 0xaf];
        let mut chars = (&v).chars();
        assert_eq!(chars.next_back(), Some(Err(Utf8Error::InvalidCodepoint(0x1efbef))));
    }
}
