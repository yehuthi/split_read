//! [`Split`] [`Read`](std::io::Read) streams.
//!
//! # Key Points
//! - Can only separate by one byte.
//! - Always zero-copy.
//!   - [Copy/allocate](Piece::Partial) when you need to.
//!
//! # Alternatives
//! - [🦀 `slice::split`](slice::split) use this instead if you have the entire input in one slice.
//! - [🦀 `std::io::Lines`](std::io::Lines) makes more sense to use if you need to allocate every line.
//!   Otherwise it's slower.
//! - [📦 `split_by`](https://crates.io/crates/split_by) significantly slower for separating by just
//!   one byte than any of the mentioned options, but can separate by multiple patterns of multiple
//!   bytes.
//!
//! ![Performance comparison](https://docs.google.com/spreadsheets/d/e/2PACX-1vS1IrdVLCw6OrMko1O8rJDt7jCi0tgFgpsnFmJHK5W0NZQ_uPkwfDUPoj75Osn9MHhQ2ALOfWWamXhT/pubchart?oid=22547540&format=image)
//! ![Performance comparison on tiny data](https://docs.google.com/spreadsheets/d/e/2PACX-1vS1IrdVLCw6OrMko1O8rJDt7jCi0tgFgpsnFmJHK5W0NZQ_uPkwfDUPoj75Osn9MHhQ2ALOfWWamXhT/pubchart?oid=2021385866&format=image)
//! 

#![deny(unsafe_code, missing_docs)]
use std::{io::{Read, self}, ops::Range, fmt::{Debug, Display}, convert::identity};


/// A [`Read`](std::io::Read) splitter.
///
/// ## Construct
/// - [`Read`]
///   - [`Split::from_read`]
///   - [`Split::read_lines`]
/// - [`&[u8]`](slice) & [`AsRef<[u8]>`](AsRef)
///   - [`Split::from_bytes`]
///   - [`Split::bytes_lines`]
///
/// ## Buffer Size
/// The first parameter is the buffer size. The ideal value is based on your input, but generally
/// 512 seems to be a good option. 
#[derive(Hash, Clone, Copy, PartialEq, PartialOrd, Eq, Ord)]
pub struct Split<const BUF_SZ: usize, T> {
    /// The inner reader.
    inner: T,

    /// The separator
    sep: u8,

    /// The exclusive end from the start for data considered already yielded, inclusively ceiled
    /// up to the `end` field, i.e. it's garbage from previous iterations.
    yielded: usize,

    /// The exclusive end of the buffer data.
    /// Data on & past it is garbage from pervious iterations.
    end: usize,

    /// The buffer.
    ///
    /// This is where data is read into from the [`inner` reader](Self::inner) and where slices that
    /// are yielded to the user come from.
    buf: [u8; BUF_SZ],
}

impl<const BUF_SZ: usize, T: Debug> Debug for Split<BUF_SZ, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        struct BufferDebug<'a>(&'a [u8], usize, usize);
        impl<'a> Debug for BufferDebug<'a> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "[")?;
                for (i, &b) in self.0.iter().enumerate() {
                    let before_start = i < self.1;
                    let past_end = i >= self.2;
                    let ansi = match (before_start, past_end) {
                        (true, false)  => "4;34",
                        (false, true)  => "4;31",
                        (false, false) => "4;32",
                        (true, true)   => "41",
                    };
                    let as_char;
                    let as_byte;
                    struct ByteDisplay(u8);
                    impl Display for ByteDisplay { fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result { write!(f, "<{}>", self.0) } }
                    write!(f, "\u{1b}[{ansi}m{}\u{1b}[0m", identity::<&dyn Display>(if b.is_ascii() {
                        as_char = char::from_u32(b as u32).unwrap(); &as_char
                    } else { as_byte = ByteDisplay(b); &as_byte }))?;
                }
                write!(f, "]")?;
                Ok(())
            }
        }

        f
            .debug_struct("Split")
            .field("inner", &self.inner)
            .field("sep", &self.sep)
            .field("yielded", &self.yielded)
            .field("end", &self.end)
            .field("buf", &BufferDebug(&self.buf, self.yielded as usize, self.end as usize))
            .finish()

    }
}

/// A [`Split`] read result (from [`Split::next_piece`]).
#[derive(Debug, Hash, Default, Clone, Copy, PartialEq, PartialOrd, Eq, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Piece<'a> {
	// TODO: Add Part and make Terminal = Part + EOF? add EOF field to variants instead?
	// that way we don't force another call to next_piece when we know we EOFed already.
    /// A terminal piece, i.e. past it is either the separator or EOF.
    ///
    /// It may be the entire separated part, but it may also just be a piece of it if the
	/// previous iteration gave a [`Partial`](Piece::Partial).
    Terminal(&'a [u8]),
    /// The part _seems_<sup>1</sup> too big to fit in the buffer, one of the future reads will
    /// [terminate](Piece::Terminal) or [`End`](Self::End)<sup>1</sup> it.
	///
    /// You can examine it and decide if you want to ignore it by skipping to after the next
    /// [`Terminal`](Piece::Terminal), or keep it by allocating a [`Vec`] for it or the like.
	///
	/// <sup>1</sup> It's possible that the next read will find the separator or EOF immediately,
    /// in which case we'd want to yield [`Terminal`](Self::Terminal), but we couldn't determine
    /// that before reading again.
    /// When we find the separator, the next piece will be a [`Terminal`](Self::Terminal) of an
    /// empty slice.
    /// When we find EOF, the next piece will be [`End`](Self::End).
	///
    /// E.g. terminal past read:
	/// ```
	/// # use split_read::{Split, Piece};
	/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
	/// let mut s = Split::<3,_>::bytes_lines(b"aaa\n");
    /// assert_eq!(s.next_piece()?, Piece::Partial(b"aaa".as_ref()));
    /// assert_eq!(s.next_piece()?, Piece::Terminal(b"".as_ref()));
    /// assert_eq!(s.next_piece()?, Piece::End);
	/// # Ok(()) }
	/// ```
    ///
    /// E.g. EOF past read:
    /// ```
	/// # use split_read::{Split, Piece};
	/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
	/// let mut s = Split::<3,_>::bytes_lines(b"aaa");
    /// assert_eq!(s.next_piece()?, Piece::Partial(b"aaa".as_ref()));
    /// assert_eq!(s.next_piece()?, Piece::End);
	/// # Ok(()) }
    /// ```
    Partial(&'a [u8]),
    /// End of file.
    #[default] End,
}

impl<'a, const BUF_SZ: usize> Split<BUF_SZ, &'a [u8]> {
    /// [`Split`] by the given separator.
    pub fn from_bytes(inner: &'a impl AsRef<[u8]>, sep: u8) -> Self {
        Self::from_read(inner.as_ref(), sep)
    }

    /// [`Split`] by lines (`\n`).
    pub fn bytes_lines(inner: &'a impl AsRef<[u8]>) -> Self { Self::read_lines(inner.as_ref()) }
}

impl<const BUF_SZ: usize, T: Read> Split<BUF_SZ, T> {
    /// [`Split`] by the given separator.
    pub const fn from_read(inner: T, sep: u8) -> Self {
        let buf = [0; BUF_SZ];
        Self { inner, yielded: 0, end: 0, buf, sep }
    }

    /// [`Split`] by lines (`\n`).
    pub const fn read_lines(inner: T) -> Self { Self::from_read(inner, b'\n') }

    /// Get the next [`Piece`].
    pub fn next_piece(&mut self) -> io::Result<Piece> {
        let find_sep_in = |s: &[u8], range: Range<usize> | -> Option<usize> {
            s[range.start as usize..range.end as usize].iter().position(|&b| b == self.sep).map(|i| range.start as usize + i)
        };

        // check for newline with existing data
        if let Some(nl) = find_sep_in(&self.buf, self.yielded..self.end) {
            let result = &self.buf[self.yielded as usize..nl];
            self.yielded = nl + 1;
            Ok(Piece::Terminal(result))
        } else {
            let size_checked = self.end - self.yielded;

            // rotate yielded garbage off the buffer line
            self.buf.copy_within(self.yielded as usize..self.end as usize, 0);
            self.end -= self.yielded;
            self.yielded = 0;

            // fill the remainder of the buffer
            loop {
                let read = self.inner.read(&mut self.buf[self.end as usize..])?;
                self.end += read;

                // check for newline again but in the new data if any
                if read == 0 {
                    // we reached EOF so there's no new data and we already checked the old. It's game
                    // over.
                    // We might still have leftover data in the buffer, if so we yield it.
                    // If not we'll yield End.
                    if self.end > 0 {
                        let result = &self.buf[..self.end as usize];
                        self.end = 0;
                        self.yielded = 0;
                        break Ok(Piece::Terminal(result))
                    } else {
                        break Ok(Piece::End)
                    }
                } else if let Some(nl) = find_sep_in(&self.buf, size_checked..self.end) {
                    let result = &self.buf[..nl];
                    self.yielded = nl + 1;
                    break Ok(Piece::Terminal(result))
                } else {
                    // we read more but still didn't find it, which can be one of two reasons:
                    // A) the buffer is too small so we need to return a partial
                    // B) our last read didn't give us enough data, either because we reached EOL or
                    // maybe it's just not ready yet, and we can't know until we read again and get
                    // Ok(0), so we'll have to try to read again. We won't spinlock because if there's
                    // more data the read will block until we get it.
                    if self.end as usize == self.buf.len() {
                        let result = &self.buf[..self.end as usize];
                        self.yielded = 0;
                        self.end = 0;
                        break Ok(Piece::Partial(result))
                    } else {
                        continue
                    }
                }
            }
        }
    }
}

impl<const BUF_SZ: usize, T> Split<BUF_SZ, T> {
    /// Gets a reference to the inner [`Read`](std::io::Read) stream.
    pub const fn inner(&self) -> &T { &self.inner }
    /// Gets the separator byte/character.
    pub const fn sep(&self) -> u8 { self.sep }
    /// Gets the inner [`Read`](std::io::Read) stream.
    pub fn into_inner(self) -> T { self.inner }
}

#[cfg(test)]
mod test {
    use std::io::{BufRead, Cursor};

    use super::*;

    use proptest::prelude::*;

    impl<const N: usize, T: Read> Split<N, T> { fn fnext(&mut self) -> Piece { self.next_piece().unwrap() } }

    #[test]
    fn empty_yields_end() {
        let mut s = Split::<8,_>::bytes_lines(b"");
        assert_eq!(s.fnext(), Piece::End);
    }

    #[test]
    fn single_sep_yields_one_empty() {
        let mut s = Split::<8,_>::bytes_lines(b"\n");
        assert_eq!(s.fnext(), Piece::Terminal(b""));
        assert_eq!(s.fnext(), Piece::End);
    }

    #[test]
    fn single_yields_itself() {
        let mut s = Split::<8,_>::bytes_lines(b"a");
        assert_eq!(s.fnext(), Piece::Terminal(b"a"));
        assert_eq!(s.fnext(), Piece::End);
    }

    #[test]
    fn multiple_nl_yield_empty_parts() {
        let mut s = Split::<8,_>::bytes_lines(b"\n\n\n");
        assert_eq!(s.fnext(), Piece::Terminal(b""));
        assert_eq!(s.fnext(), Piece::Terminal(b""));
        assert_eq!(s.fnext(), Piece::Terminal(b""));
        assert_eq!(s.fnext(), Piece::End);
    }

    #[test]
    fn line_without_sep_yields_itself() {
        let mut s = Split::<32,_>::bytes_lines(b"hello");
        assert_eq!(s.fnext(), Piece::Terminal(b"hello".as_ref()));
        assert_eq!(s.fnext(), Piece::End);
    }

    #[test]
    fn line_with_trailing_sep_yields_itself_without_sep() {
        let mut s = Split::<32,_>::bytes_lines(b"hello\n");
        assert_eq!(s.fnext(), Piece::Terminal(b"hello".as_ref()));
        assert_eq!(s.fnext(), Piece::End);
    }

    #[test]
    fn test_two_pats_that_both_fit() {
        let mut s = Split::<32,_>::bytes_lines(b"hello\nworld\n");
        assert_eq!(s.fnext(), Piece::Terminal(b"hello".as_ref()));
        assert_eq!(s.fnext(), Piece::Terminal(b"world".as_ref()));
        assert_eq!(s.fnext(), Piece::End);
    }

    #[test]
    fn test_two_lines_where_second_doesnt_fit() {
        let mut s = Split::<4,_>::bytes_lines(b"AAA\nBB\n");
        assert_eq!(s.fnext(), Piece::Terminal(b"AAA".as_ref()));
        assert_eq!(s.fnext(), Piece::Terminal(b"BB".as_ref()));
        assert_eq!(s.fnext(), Piece::End);
    }

    #[test]
    fn test_single_part_overflow() {
        let mut s = Split::<3,_>::bytes_lines(b"AAABB");
        assert_eq!(s.fnext(), Piece::Partial(b"AAA".as_ref()));
        assert_eq!(s.fnext(), Piece::Terminal(b"BB".as_ref()));
        assert_eq!(s.fnext(), Piece::End);
    }

    #[test]
    fn test_second_line_overflows() {
        let mut s = Split::<3,_>::bytes_lines(b"AA\nBBBB");
        assert_eq!(s.fnext(), Piece::Terminal(b"AA".as_ref()));
        assert_eq!(s.fnext(), Piece::Partial(b"BBB".as_ref()));
        assert_eq!(s.fnext(), Piece::Terminal(b"B".as_ref()));
        assert_eq!(s.fnext(), Piece::End);
    }

    #[test]
    fn test_partial_was_ending() {
        let mut s = Split::<3,_>::bytes_lines(b"AAA\nBBB");
        assert_eq!(s.fnext(), Piece::Partial(b"AAA".as_ref()));
        assert_eq!(s.fnext(), Piece::Terminal(b"".as_ref()));
        assert_eq!(s.fnext(), Piece::Partial(b"BBB".as_ref()));
        assert_eq!(s.fnext(), Piece::End);
    }

    #[test]
    fn test_partial_was_terminal() {
        let mut it = Split::<3,_>::bytes_lines(b"aaa\n");
        assert_eq!(it.fnext(), Piece::Partial(b"aaa".as_ref()));
        assert_eq!(it.fnext(), Piece::Terminal(b"".as_ref()));
        assert_eq!(it.fnext(), Piece::End);
    }

    #[test]
    fn test_start_with_sep() {
        let mut it = Split::<3,_>::bytes_lines(b"\na");
        assert_eq!(it.fnext(), Piece::Terminal(b"".as_ref()));
        assert_eq!(it.fnext(), Piece::Terminal(b"a".as_ref()));
        assert_eq!(it.fnext(), Piece::End);
    }

    #[test]
    fn test_pciid_sample_lines() {
        let s = include_bytes!("../test/pciid_sample");
        let mut s = Split::<2048,_>::bytes_lines(s);
        let mut terms = 0;
        let mut parts = 0;
        loop {
            match s.next_piece().unwrap() {
                Piece::Terminal(_) => { terms += 1 },
                Piece::Partial (_) => { parts += 1 },
                Piece::End => break,
            }
        };
        assert_eq!(parts, 0);
        assert_eq!(terms, 41);
    }

    /// Used for testing
    fn allocating_sep(bs: &[u8], sep: u8) -> Vec<Vec<u8>> {
        let mut result = Vec::<Vec<u8>>::new();
        let mut reader = Split::<256,_>::from_read(bs, sep);
        let mut in_partial = false;
        let mut partial = Vec::new();
        loop {
            match reader.next_piece().unwrap() {
                Piece::Terminal(l) if in_partial => {
                    in_partial = false;
                    partial.extend_from_slice(l);
                    result.push(std::mem::take(&mut partial));
                },
                Piece::Terminal(l) => {
                    result.push(l.to_owned());
                },
                Piece::Partial(p) => {
                    in_partial = true;
                    partial.extend_from_slice(p);
                },
                Piece::End => {
                    if in_partial { result.push(partial); }
                    break;
                },
            }
        }
        result
    }

    #[test]
    fn test_allocating_sep_helper() {
        assert_eq!(allocating_sep(b"aaaa\nbbbb\ncccc", b'\n'), [b"aaaa", b"bbbb", b"cccc"]);
        assert_eq!(allocating_sep(b"0", b'\n'), [b"0"]);
    }

    proptest! {
        #[test]
        fn proxy_std_slice_split(bs: Vec<u8>, sep: u8) {
            let bs = &bs[..];

            let std: Vec<Vec<u8>> = bs.split(|&b| b == sep).map(|p| p.to_owned()).collect();
            prop_assume!(std.iter().all(|l| !l.is_empty()));
            // we don't agree with std lib's behavior of sep => [].
            // e.g. splitting "\n" gives [[], []], for us it's just [[]].

            let lib = allocating_sep(bs, sep);
            prop_assert_eq!(std, lib);
        }

        #[test]
        fn proxy_std_io_split(bs: Vec<u8>, sep: u8) {
            let bs = &bs[..];
            let std: Vec<Vec<u8>> = Cursor::new(bs).split(sep).map(|l| l.unwrap()).collect();
            let lib = allocating_sep(bs, sep);
            prop_assert_eq!(std, lib);
        }
    }
}
