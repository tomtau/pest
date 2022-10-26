// pest. The Elegant Parser
// Copyright (c) 2018 Dragoș Tiselice
//
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. All files in the project carrying such notice may not be copied,
// modified, or distributed except according to those terms.
#![no_std]
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/pest-parser/pest/master/pest-logo.svg",
    html_favicon_url = "https://raw.githubusercontent.com/pest-parser/pest/master/pest-logo.svg"
)]
#![warn(missing_docs, rust_2018_idioms, unused_qualifications)]
//! # pest. The Elegant Parser
//!
//! pest is a general purpose parser written in Rust with a focus on accessibility, correctness,
//! and performance. It uses parsing expression grammars (or [PEG]) as input, which are similar in
//! spirit to regular expressions, but which offer the enhanced expressivity needed to parse
//! complex languages.
//!
//! [PEG]: https://en.wikipedia.org/wiki/Parsing_expression_grammar
//!
//! ## Getting started
//!
//! The recommended way to start parsing with pest is to read the official [book].
//!
//! Other helpful resources:
//!
//! * API reference on [docs.rs]
//! * play with grammars and share them on our [fiddle]
//! * find previous common questions answered or ask questions on [GitHub Discussions]
//! * leave feedback, ask questions, or greet us on [Gitter] or [Discord]
//!
//! [book]: https://pest.rs/book
//! [docs.rs]: https://docs.rs/pest
//! [fiddle]: https://pest.rs/#editor
//! [Gitter]: https://gitter.im/pest-parser/pest
//! [Discord]: https://discord.gg/XEGACtWpT2
//! [GitHub Discussions]: https://github.com/pest-parser/pest/discussions
//!
//! ## Usage
//!
//! The core of pest is the trait [`Parser`], which provides an interface to the parsing
//! functionality.
//!
//! The accompanying crate `pest_derive` can automatically generate a [`Parser`] from a PEG
//! grammar. Using `pest_derive` is highly encouraged, but it is also possible to implement
//! [`Parser`] manually if required.
//!
//! ## `.pest` files
//!
//! Grammar definitions reside in custom `.pest` files located in the crate `src` directory.
//! Parsers are automatically generated from these files using `#[derive(Parser)]` and a special
//! `#[grammar = "..."]` attribute on a dummy struct.
//!
//! ```ignore
//! #[derive(Parser)]
//! #[grammar = "path/to/my_grammar.pest"] // relative to src
//! struct MyParser;
//! ```
//!
//! The syntax of `.pest` files is documented in the [`pest_derive` crate].
//!
//! ## Inline grammars
//!
//! Grammars can also be inlined by using the `#[grammar_inline = "..."]` attribute.
//!
//! [`Parser`]: trait.Parser.html
//! [`pest_derive` crate]: https://docs.rs/pest_derive/

#![doc(html_root_url = "https://docs.rs/pest")]

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "pretty-print")]
extern crate serde;
#[cfg(feature = "pretty-print")]
extern crate serde_json;

pub use crate::parser::Parser;
pub use crate::parser_state::{
    set_call_limit, state, Atomicity, Lookahead, MatchDir, ParseResult, ParserState,
};
pub use crate::position::Position;
pub use crate::span::{Lines, LinesSpan, Span};
pub use crate::token::Token;
use core::fmt::Debug;
use core::hash::Hash;

pub mod error;
pub mod iterators;
mod macros;
mod parser;
mod parser_state;
mod position;
pub mod pratt_parser;
#[deprecated(
    since = "2.4.0",
    note = "Use `pest::pratt_parser` instead (it is an equivalent which also supports unary prefix/suffix operators).
While prec_climber is going to be kept in 2.x minor and patch releases, it may be removed in a future major release."
)]
pub mod prec_climber;
mod span;
mod stack;
mod token;
#[doc(hidden)]
pub mod unicode;

/// A trait which parser rules must implement.
///
/// This trait is set up so that any struct that implements all of its required traits will
/// automatically implement this trait as well.
///
/// This is essentially a [trait alias](https://github.com/rust-lang/rfcs/pull/1733). When trait
/// aliases are implemented, this may be replaced by one.
pub trait RuleType: Copy + Debug + Eq + Hash + Ord {}

impl<T: Copy + Debug + Eq + Hash + Ord> RuleType for T {}
