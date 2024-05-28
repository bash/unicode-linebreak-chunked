//! Modified version of [`unicode-linebreak`] with support for analyzing text
//! split across multiple non-contiguous chunks.
//!
//! This is quite an advanced use case: **You probably want to use [`unicode-linebreak`] instead.**
//!
//! Implementation of the Line Breaking Algorithm described in [Unicode Standard Annex #14][UAX14].
//!
//! Given an input text, locates "line break opportunities", or positions appropriate for wrapping
//! lines when displaying text.
//!
//! # Example
//!
//! ```
//! use unicode_linebreak_chunked::{Linebreaks, BreakOpportunity::{Mandatory, Allowed}};
//!
//! let mut l = Linebreaks::default();
//! assert!(l.chunk("a ").eq([]));
//! assert!(l.chunk("b ").eq([(0, Allowed)]));     // May break after first space
//! assert!(l.chunk("\nc").eq([(1, Mandatory)]));  // Must break after line feed
//! assert!(l.chunk("d e").eq([(2, Allowed)]));    // May break after space, no break between chunks
//! assert_eq!(l.eot(), Some(Mandatory));          // Must break at end of text, so that there always is at least one LB
//! ```
//!
//! [UAX14]: https://www.unicode.org/reports/tr14/
//!
//! [`unicode-linebreak`]: https://docs.rs/unicode-linebreak

#![no_std]
#![deny(missing_docs, missing_debug_implementations)]

use core::iter::once;
use iter_utils::ExhaustOnDrop;

/// The [Unicode version](https://www.unicode.org/versions/) conformed to.
pub const UNICODE_VERSION: (u8, u8, u8) = (15, 0, 0);

include!("shared.rs");
include!("tables.rs");
mod iter_utils;

/// Returns the line break property of the specified code point.
///
/// # Examples
///
/// ```
/// use unicode_linebreak_chunked::{BreakClass, break_property};
/// assert_eq!(break_property(0x2CF3), BreakClass::Alphabetic);
/// ```
#[inline(always)]
pub fn break_property(codepoint: u32) -> BreakClass {
    const BMP_INDEX_LENGTH: u32 = BMP_LIMIT >> BMP_SHIFT;
    const OMITTED_BMP_INDEX_1_LENGTH: u32 = BMP_LIMIT >> SHIFT_1;

    let data_pos = if codepoint < BMP_LIMIT {
        let i = codepoint >> BMP_SHIFT;
        BREAK_PROP_TRIE_INDEX[i as usize] + (codepoint & (BMP_DATA_BLOCK_LENGTH - 1)) as u16
    } else if codepoint < BREAK_PROP_TRIE_HIGH_START {
        let i1 = codepoint >> SHIFT_1;
        let i2 = BREAK_PROP_TRIE_INDEX
            [(i1 + BMP_INDEX_LENGTH - OMITTED_BMP_INDEX_1_LENGTH) as usize]
            + ((codepoint >> SHIFT_2) & (INDEX_2_BLOCK_LENGTH - 1)) as u16;
        let i3_block = BREAK_PROP_TRIE_INDEX[i2 as usize];
        let i3_pos = ((codepoint >> SHIFT_3) & (INDEX_3_BLOCK_LENGTH - 1)) as u16;

        debug_assert!(i3_block & 0x8000 == 0, "18-bit indices are unexpected");
        let data_block = BREAK_PROP_TRIE_INDEX[(i3_block + i3_pos) as usize];
        data_block + (codepoint & (SMALL_DATA_BLOCK_LENGTH - 1)) as u16
    } else {
        return XX;
    };
    BREAK_PROP_TRIE_DATA[data_pos as usize]
}

/// Break opportunity type.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum BreakOpportunity {
    /// A line must break at this spot.
    Mandatory,
    /// A line is allowed to end at this spot.
    Allowed,
}

/// Returns iterators over line break opportunities in some text
/// that is possibly split across multiple non-contiguous chunks.
///
/// Uses the default Line Breaking Algorithm with the tailoring that Complex-Context Dependent
/// (SA) characters get resolved to Ordinary Alphabetic and Symbol Characters (AL) regardless of
/// General_Category.
///
/// The input is provided as chunks using the [`Linebreaks::chunk`] method. \
/// Be sure to call [`Linebreaks::eot`] after providing all text.
#[derive(Clone, Debug)]
pub struct Linebreaks(u8, bool);

impl Default for Linebreaks {
    fn default() -> Self {
        Self(sot, false)
    }
}

impl Linebreaks {
    /// Get the break opportunities for the next chunk of text.
    ///
    /// Break opportunities are given as tuples of the byte index (relative to the current chunk)
    /// of the character succeeding the break and the type.
    ///
    /// Note that this will not return a [`BreakOpportunity`] at the end
    /// of the provided chunk. Call [`Linebreaks::eot`] after providing all chunks to
    /// get the final [`BreakOpportunity`].
    pub fn chunk<'a>(
        &'a mut self,
        s: &'a str,
    ) -> impl Iterator<Item = (usize, BreakOpportunity)> + 'a {
        ExhaustOnDrop(
            s.char_indices()
                .map(|(i, c)| (i, break_property(c as u32) as u8))
                .filter_map(|(i, cls)| self.next(cls).map(|o| (i, o))),
        )
    }

    /// End of text. This resets the [`Linebreaks`] struct for re-use.
    pub fn eot(&mut self) -> Option<BreakOpportunity> {
        let opportunity = self.next(eot);
        *self = Self::default();
        opportunity
    }

    fn next(&mut self, cls: u8) -> Option<BreakOpportunity> {
        use BreakOpportunity::{Allowed, Mandatory};

        // ZWJ is handled outside the table to reduce its size
        let val = PAIR_TABLE[self.0 as usize][cls as usize];
        let is_mandatory = val & MANDATORY_BREAK_BIT != 0;
        let is_break = val & ALLOWED_BREAK_BIT != 0 && (!self.1 || is_mandatory);
        *self = Linebreaks(
            val & !(ALLOWED_BREAK_BIT | MANDATORY_BREAK_BIT),
            cls == BreakClass::ZeroWidthJoiner as u8,
        );

        if is_break {
            Some(if is_mandatory { Mandatory } else { Allowed })
        } else {
            None
        }
    }
}

/// Returns an iterator over line break opportunities in the specified string.
///
/// Break opportunities are given as tuples of the byte index of the character succeeding the break
/// and the type.
///
/// Uses the default Line Breaking Algorithm with the tailoring that Complex-Context Dependent
/// (SA) characters get resolved to Ordinary Alphabetic and Symbol Characters (AL) regardless of
/// General_Category.
///
/// # Examples
///
/// ```
/// use unicode_linebreak_chunked::{linebreaks, BreakOpportunity::{Mandatory, Allowed}};
/// assert!(linebreaks("Hello world!").eq(vec![(6, Allowed), (12, Mandatory)]));
/// ```
pub fn linebreaks(s: &str) -> impl Iterator<Item = (usize, BreakOpportunity)> + Clone + '_ {
    use BreakOpportunity::{Allowed, Mandatory};

    s.char_indices()
        .map(|(i, c)| (i, break_property(c as u32) as u8))
        .chain(once((s.len(), eot)))
        .scan((sot, false), |state, (i, cls)| {
            // ZWJ is handled outside the table to reduce its size
            let val = PAIR_TABLE[state.0 as usize][cls as usize];
            let is_mandatory = val & MANDATORY_BREAK_BIT != 0;
            let is_break = val & ALLOWED_BREAK_BIT != 0 && (!state.1 || is_mandatory);
            *state = (
                val & !(ALLOWED_BREAK_BIT | MANDATORY_BREAK_BIT),
                cls == BreakClass::ZeroWidthJoiner as u8,
            );

            Some((i, is_break, is_mandatory))
        })
        .filter_map(|(i, is_break, is_mandatory)| {
            if is_break {
                Some((i, if is_mandatory { Mandatory } else { Allowed }))
            } else {
                None
            }
        })
}

/// Divides the string at the last index where further breaks do not depend on prior context.
///
/// The trivial index at `eot` is excluded.
///
/// A common optimization is to determine only the nearest line break opportunity before the first
/// character that would cause the line to become overfull, requiring backward traversal, of which
/// there are two approaches:
///
/// * Cache breaks from forward traversals
/// * Step backward and with `split_at_safe` find a pos to safely search forward from, repeatedly
///
/// # Examples
///
/// ```
/// use unicode_linebreak_chunked::{linebreaks, split_at_safe};
/// let s = "Not allowed to break within em dashes: — —";
/// let (prev, safe) = split_at_safe(s);
/// let n = prev.len();
/// assert!(linebreaks(safe).eq(linebreaks(s).filter_map(|(i, x)| i.checked_sub(n).map(|i| (i, x)))));
/// ```
pub fn split_at_safe(s: &str) -> (&str, &str) {
    let mut chars = s.char_indices().rev().scan(None, |state, (i, c)| {
        let cls = break_property(c as u32);
        let is_safe_pair = state
            .replace(cls)
            .map_or(false, |prev| is_safe_pair(cls, prev)); // Reversed since iterating backwards
        Some((i, is_safe_pair))
    });
    chars.find(|&(_, is_safe_pair)| is_safe_pair);
    // Include preceding char for `linebreaks` to pick up break before match (disallowed after sot)
    s.split_at(chars.next().map_or(0, |(i, _)| i))
}

#[cfg(doctest)]
#[doc = include_str!("../README.md")]
pub mod readme_doctests {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        assert_eq!(break_property(0xA), BreakClass::LineFeed);
        assert_eq!(break_property(0xDB80), BreakClass::Surrogate);
        assert_eq!(break_property(0xe01ef), BreakClass::CombiningMark);
        assert_eq!(break_property(0x10ffff), BreakClass::Unknown);
    }
}
