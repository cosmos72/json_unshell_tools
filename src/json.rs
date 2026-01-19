/**
 * MIT License
 *
 * Copyright (C) 2026 by Massimiliano Ghilardi
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 */
use std::{ascii, fmt, io};
//use num_bigint;

pub trait Writable {
    fn write_to<W: io::Write>(&self, dst: &mut W) -> io::Result<()>;
}

#[derive(PartialEq)]
pub enum Token {
    StartObject,
    EndObject,
    StartArray,
    EndArray,
    Boolean(bool),
    Number(String), /* contains literal digits, including sign, fraction and exponent */
    String(String), /* contains literal characters, including escape sequences \n \r \t \uxxxx ... */
    Null,
    Colon,
    Comma,
    Eof,
}

pub struct PullParser<R: io::Read> {
    pos: usize,
    len: usize,
    reader: R,
    buf: Vec<u8>,

    stack: Vec<Expect>,
    root: RootState,
    eof: bool,
}

impl Writable for Token {
    fn write_to<W: io::Write>(&self, dst: &mut W) -> io::Result<()> {
        match self {
            Token::StartObject => write_bytes(dst, b"{"),
            Token::EndObject => write_bytes(dst, b"}"),
            Token::StartArray => write_bytes(dst, b"["),
            Token::EndArray => write_bytes(dst, b"]"),
            Token::Boolean(b) => write_bytes(dst, if *b { b"true" } else { b"false" }),
            Token::Number(n) => write_bytes(dst, n.as_bytes()),
            Token::String(s) => {
                write_bytes(dst, b"\"")?;
                write_bytes(dst, s.as_bytes())?;
                write_bytes(dst, b"\"")
            }
            Token::Null => write_bytes(dst, b"null"),
            Token::Colon => write_bytes(dst, b":"),
            Token::Comma => write_bytes(dst, b","),
            Token::Eof => Ok(()),
        }
    }
}

impl fmt::Debug for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::StartObject => write!(f, "{{"),
            Token::EndObject => write!(f, "}}"),
            Token::StartArray => write!(f, "["),
            Token::EndArray => write!(f, "]"),
            Token::Boolean(b) => write!(f, "{}", b),
            Token::Number(n) => write!(f, "{}", &n),
            Token::String(s) => write!(f, "\"{}\"", &s),
            Token::Null => write!(f, "null"),
            Token::Colon => write!(f, ":"),
            Token::Comma => write!(f, ","),
            Token::Eof => Ok(()),
        }
    }
}

/* -------------------------------- implementation -------------------------- */

fn write_bytes<W: io::Write>(dst: &mut W, bytes: &[u8]) -> io::Result<()> {
    check(dst.write(bytes))
}

fn check(val: io::Result<usize>) -> io::Result<()> {
    match val {
        Ok(_) => Ok(()),
        Err(e) => Err(e),
    }
}

#[derive(Copy, Clone)]
enum Kind {
    StartObject,
    EndObject,
    StartArray,
    EndArray,
    Boolean,
    Number,
    String,
    Null,
    Colon,
    Comma,
    Eof,
}

#[derive(Debug, Copy, Clone)]
enum Expect {
    ObjectKey,
    ObjectKeyOrEnd,
    ObjectColon,
    ObjectValue,
    ObjectCommaOrEnd,
    ArrayValue,
    ArrayValueOrEnd,
    ArrayCommaOrEnd,
}

#[derive(Debug, PartialEq)]
enum RootState {
    ExpectValue,
    Done,
}

#[derive(Debug, Copy, Clone, PartialEq)]
enum ParseMode {
    Parse,
    Skip,
}

impl fmt::Debug for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Kind::StartObject => write!(f, "'{{'"),
            Kind::EndObject => write!(f, "'}}'"),
            Kind::StartArray => write!(f, "'['"),
            Kind::EndArray => write!(f, "']'"),
            Kind::Boolean => write!(f, "boolean"),
            Kind::Number => write!(f, "number"),
            Kind::String => write!(f, "string"),
            Kind::Null => write!(f, "null"),
            Kind::Colon => write!(f, "':'"),
            Kind::Comma => write!(f, "','"),
            Kind::Eof => write!(f, "EOF"),
        }
    }
}

impl Token {
    fn kind(&self) -> Kind {
        match self {
            Token::StartObject => Kind::StartObject,
            Token::EndObject => Kind::EndObject,
            Token::StartArray => Kind::StartArray,
            Token::EndArray => Kind::EndArray,
            Token::Boolean(_) => Kind::Boolean,
            Token::Number(_) => Kind::Number,
            Token::String(_) => Kind::String,
            Token::Null => Kind::Null,
            Token::Colon => Kind::Colon,
            Token::Comma => Kind::Comma,
            Token::Eof => Kind::Eof,
        }
    }
}

impl<R: io::Read> PullParser<R> {
    pub fn new(reader: R) -> Self {
        Self {
            pos: 0,
            len: 0,
            reader,
            buf: [0; 4096].to_vec(),
            stack: [].to_vec(),
            root: RootState::ExpectValue,
            eof: false,
        }
    }

    pub fn depth(&self) -> usize {
        self.stack.len()
    }

    /**
     * Parse a single json token and return it.
     *
     * @return Ok(Token) containing the next parsed json token,
     * which will be Token::Eof at end of input stream.
     */
    pub fn next_token(&mut self) -> io::Result<Token> {
        let tok = self.parse_token(ParseMode::Parse)?;
        self.validate_kind(tok.kind())?;
        Ok(tok)
    }

    /**
     * Parse a single json token,
     * discarding its content in case it is a number or string
     * (but preserving its kind), and return it.
     *
     * Faster than next().
     *
     * @return Ok(Token) containing the next parsed json token,
     * which will be Token::Eof at end of input stream.
     */
    pub fn skip_token(&mut self) -> io::Result<Token> {
        let tok = self.parse_token(ParseMode::Skip)?;
        self.validate_kind(tok.kind())?;
        Ok(tok)
    }

    /**
     * @return Ok(true) if top-level json value just finished,
     * and another top-level json value can be read.
     *
     * This means input stream violates Json specs, but is commonly used in the wild
     * for appending multiple top-level json values into the same file.
     *
     * If you want to strictly comply with Json specs, simply do NOT call this function.
     */
    pub fn next_stream(&mut self) -> io::Result<bool> {
        if self.eof {
            Ok(false)
        } else if self.root == RootState::Done && self.stack.is_empty() {
            self.skip_whitespace()?; // updates self.eof
            if !self.eof {
                self.root = RootState::ExpectValue;
            }
            Ok(!self.eof)
        } else {
            Ok(false)
        }
    }

    /**
     * skip whitespace, then @return Ok(true) if reached EOF.
     *
     * Usually not needed, as parser detects and reports EOF.
     * Useful mostly to detect empty files (which do not comply with Json specs).
     */
    pub fn is_eof(&mut self) -> io::Result<bool> {
        self.skip_whitespace()?;
        Ok(self.eof)
    }

    fn parse_token(&mut self, mode: ParseMode) -> io::Result<Token> {
        self.skip_whitespace()?;

        let b = match self.peek_byte()? {
            Some(x) => x,
            None => return Ok(Token::Eof),
        };

        match b {
            b'{' => {
                self.consume_byte()?;
                Ok(Token::StartObject)
            }
            b'}' => {
                self.consume_byte()?;
                Ok(Token::EndObject)
            }
            b'[' => {
                self.consume_byte()?;
                Ok(Token::StartArray)
            }
            b']' => {
                self.consume_byte()?;
                Ok(Token::EndArray)
            }
            b':' => {
                self.consume_byte()?;
                Ok(Token::Colon)
            }
            b',' => {
                self.consume_byte()?;
                Ok(Token::Comma)
            }
            b'"' => self.parse_string(mode),
            b'-' | b'0'..=b'9' => self.parse_number(mode),
            b'f' | b't' => self.parse_boolean(b),
            b'n' => self.parse_null(),
            _ => err(&format!(
                "unexpected character '{}'",
                ascii::escape_default(b)
            )),
        }
    }

    /* ---------- Parsing ---------- */

    fn parse_string(&mut self, mode: ParseMode) -> io::Result<Token> {
        self.consume_expected(b'"')?;
        let mut out: Vec<u8> = Vec::new();

        loop {
            let b = self
                .next_byte()?
                .ok_or_else(|| error("unterminated json string"))?;
            match b {
                b'"' => break,
                b'\\' => {
                    if mode == ParseMode::Parse {
                        out.push(b);
                    }
                    self.parse_string_esc(mode, &mut out)?;
                }
                0x00..=0x1F => return err(&format!("invalid control byte {} in json string", b)),
                _ => {
                    if mode == ParseMode::Parse {
                        out.push(b);
                    }
                }
            }
        }

        match String::from_utf8(out) {
            Ok(s) => Ok(Token::String(s)),
            Err(_) => err(&format!("invalid UTF-8 bytes in json string")),
        }
    }

    fn parse_string_esc(&mut self, mode: ParseMode, out: &mut Vec<u8>) -> io::Result<()> {
        let b = self
            .next_byte()?
            .ok_or_else(|| error("unterminated json string"))?;
        let push = |out: &mut Vec<u8>, b: u8| {
            if mode == ParseMode::Parse {
                out.push(b);
            }
        };
        match b {
            b'"' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't' => push(out, b),
            b'u' => {
                let high = self.parse_hex4(mode, out)?;

                if (0xD800..=0xDBFF).contains(&high) {
                    self.parse_low_surrogate(mode, out, high)?;
                } else if (0xDC00..=0xDFFF).contains(&high) {
                    return err_unpaired_low_surrogate(high);
                } else {
                    codepoint_to_char(high as u32)?;
                };
            }
            _ => {
                return err_invalid_escape(b);
            }
        }
        Ok(())
    }

    fn parse_hex4(&mut self, mode: ParseMode, out: &mut Vec<u8>) -> io::Result<u16> {
        let mut value: u16 = 0;

        for _ in 0..4 {
            let b = self
                .peek_byte()?
                .ok_or_else(|| error_incomplete_escape_uxxxx())?;

            let digit = match b {
                b'0'..=b'9' => (b - b'0') as u16,
                b'a'..=b'f' => (b - b'a' + 10) as u16,
                b'A'..=b'F' => (b - b'A' + 10) as u16,
                _ => return err_invalid_hex_digit(b),
            };
            self.consume_byte()?;
            if mode == ParseMode::Parse {
                out.push(b);
            }
            value = (value << 4) | digit;
        }
        Ok(value)
    }

    fn parse_low_surrogate(
        &mut self,
        mode: ParseMode,
        out: &mut Vec<u8>,
        high: u16,
    ) -> io::Result<()> {
        match (self.next_byte()?, self.next_byte()?) {
            (Some(b'\\'), Some(b'u')) => {
                let low = self.parse_hex4(mode, out)?;
                if !(0xDC00..=0xDFFF).contains(&low) {
                    return err_invalid_low_surrogate(high, low);
                }
                if mode == ParseMode::Parse {
                    out.push(b'\\');
                    out.push(b'u');
                }
                let _ = surrogate_pair_to_char(high, low)?;
                Ok(())
            }
            _ => err_missing_low_surrogate(high),
        }
    }

    fn parse_number(&mut self, mode: ParseMode) -> io::Result<Token> {
        let mut s = String::new();
        let push = |s: &mut String, c: char| {
            if mode == ParseMode::Parse {
                s.push(c);
            }
        };

        if self.peek_byte()? == Some(b'-') {
            push(&mut s, '-');
            self.consume_byte()?;
        }

        match self.peek_byte()? {
            Some(b'0') => {
                push(&mut s, '0');
                self.consume_byte()?;
                match self.peek_byte()? {
                    Some(x) => {
                        if !matches!(
                            x,
                            b',' | b']' | b'}' | b' ' | b'.' | b'e' | b'E' | b'\n' | b'\r' | b'\t'
                        ) {
                            return err(&format!("invalid byte {} after 0 in json number", x));
                        }
                    }
                    None => {}
                }
            }
            Some(b'1'..=b'9') => {
                while let Some(b'0'..=b'9') = self.peek_byte()? {
                    push(&mut s, self.next_byte()?.unwrap() as char);
                }
            }
            Some(b) => return err(&format!("invalid byte {} in json number", b)),
            _ => return err("invalid json number"),
        }

        if self.peek_byte()? == Some(b'.') {
            push(&mut s, '.');
            self.consume_byte()?;
            let mut digit = false;
            while let Some(b'0'..=b'9') = self.peek_byte()? {
                digit = true;
                push(&mut s, self.next_byte()?.unwrap() as char);
            }
            if !digit {
                return err(&format!("missing fraction digits in json number {}", s));
            }
        }

        if matches!(self.peek_byte()?, Some(b'e' | b'E')) {
            push(&mut s, self.next_byte()?.unwrap() as char);
            if matches!(self.peek_byte()?, Some(b'+' | b'-')) {
                push(&mut s, self.next_byte()?.unwrap() as char);
            }
            let mut digit = false;
            while let Some(b'0'..=b'9') = self.peek_byte()? {
                digit = true;
                push(&mut s, self.next_byte()?.unwrap() as char);
            }
            if !digit {
                return err(&format!("missing exponent digits in json number {}", s));
            }
        }

        Ok(Token::Number(s))
    }

    fn parse_boolean(&mut self, b: u8) -> io::Result<Token> {
        if b == b't' && self.consume_keyword("true")? {
            Ok(Token::Boolean(true))
        } else if b == b'f' && self.consume_keyword("false")? {
            Ok(Token::Boolean(false))
        } else {
            err("invalid json boolean keyword")
        }
    }

    fn parse_null(&mut self) -> io::Result<Token> {
        if self.consume_keyword("null")? {
            Ok(Token::Null)
        } else {
            err("invalid json null keyword")
        }
    }

    /* ---------- Syntax Validation ---------- */

    fn validate_kind(&mut self, kind: Kind) -> io::Result<()> {
        // println!("validate kind {:?}, state {:?}", kind, self.stack.last());

        match self.stack.last_mut() {
            None => self.validate_root(kind),
            Some(state) => match state {
                Expect::ObjectKey => match kind {
                    Kind::String => Ok(*state = Expect::ObjectColon),
                    _ => err(&format!("expecting json object key, found {:?}", kind)),
                },

                Expect::ObjectKeyOrEnd => match kind {
                    Kind::String => Ok(*state = Expect::ObjectColon),
                    Kind::EndObject => {
                        self.stack.pop();
                        self.after_value()
                    }
                    _ => err(&format!(
                        "expecting json object key or '}}', found {:?}",
                        kind
                    )),
                },

                Expect::ObjectColon => match kind {
                    Kind::Colon => Ok(*state = Expect::ObjectValue),
                    _ => err("expected ':'"),
                },

                Expect::ObjectValue => match kind {
                    Kind::StartObject
                    | Kind::StartArray
                    | Kind::Boolean
                    | Kind::Number
                    | Kind::String
                    | Kind::Null => {
                        *state = Expect::ObjectCommaOrEnd;
                        self.accept_value(kind)?;
                        Ok(())
                    }
                    _ => err(&format!("expecting json object value, found {:?}", kind)),
                },

                Expect::ObjectCommaOrEnd => match kind {
                    Kind::Comma => Ok(*state = Expect::ObjectKey),
                    Kind::EndObject => {
                        self.stack.pop();
                        self.after_value()
                    }
                    _ => err(&format!(
                        "expecting ',' or '}}' in json object, found {:?}",
                        kind
                    )),
                },

                Expect::ArrayValue => match kind {
                    Kind::StartObject
                    | Kind::StartArray
                    | Kind::Boolean
                    | Kind::Number
                    | Kind::String
                    | Kind::Null => {
                        *state = Expect::ArrayCommaOrEnd;
                        self.accept_value(kind)?;
                        Ok(())
                    }
                    _ => err(&format!("expecting json array element, found {:?}", kind)),
                },

                Expect::ArrayValueOrEnd => match kind {
                    Kind::StartObject
                    | Kind::StartArray
                    | Kind::Boolean
                    | Kind::Number
                    | Kind::String
                    | Kind::Null => {
                        *state = Expect::ArrayCommaOrEnd;
                        self.accept_value(kind)?;
                        Ok(())
                    }
                    Kind::EndArray => {
                        self.stack.pop();
                        self.after_value()
                    }
                    _ => err(&format!(
                        "expecting json array element or ']', found {:?}",
                        kind
                    )),
                },

                Expect::ArrayCommaOrEnd => match kind {
                    Kind::Comma => Ok(*state = Expect::ArrayValue),
                    Kind::EndArray => {
                        self.stack.pop();
                        self.after_value()
                    }
                    _ => err(&format!(
                        "expecting ',' or ']' in json array, found {:?}",
                        kind
                    )),
                },
            },
        }
    }

    fn validate_root(&mut self, kind: Kind) -> io::Result<()> {
        match self.root {
            RootState::ExpectValue => {
                self.accept_value(kind)?;
                self.root = RootState::Done;
                Ok(())
            }
            RootState::Done => match kind {
                Kind::Eof => Ok(()),
                _ => err(&format!(
                    "expecting EOF after top-level json value, found {:?}",
                    kind
                )),
            },
        }
    }

    fn accept_value(&mut self, kind: Kind) -> io::Result<()> {
        match kind {
            Kind::StartObject => {
                self.stack.push(Expect::ObjectKeyOrEnd);
                Ok(())
            }
            Kind::StartArray => {
                self.stack.push(Expect::ArrayValueOrEnd);
                Ok(())
            }
            Kind::Boolean | Kind::Number | Kind::String | Kind::Null => Ok(()),
            _ => err(&format!(
                "expecting json array, json object or value, found {:?}",
                kind
            )),
        }
    }

    fn after_value(&mut self) -> io::Result<()> {
        if let Some(parent) = self.stack.last_mut() {
            match parent {
                Expect::ObjectValue => {
                    *parent = Expect::ObjectCommaOrEnd;
                }
                Expect::ArrayValue => {
                    *parent = Expect::ArrayCommaOrEnd;
                }
                _ => {}
            }
        }
        Ok(())
    }

    /* ---------- Buffer Management ---------- */

    fn peek_byte(&mut self) -> io::Result<Option<u8>> {
        if self.pos >= self.len && !self.eof {
            self.fill_buffer()?;
        }
        Ok(if self.pos < self.len {
            Some(self.buf[self.pos])
        } else {
            None
        })
    }

    fn next_byte(&mut self) -> io::Result<Option<u8>> {
        let b = self.peek_byte()?;
        if b.is_some() {
            self.pos += 1;
        }
        Ok(b)
    }

    fn consume_byte(&mut self) -> io::Result<()> {
        self.next_byte()?.ok_or_else(|| error_unexpected_eof())?;
        Ok(())
    }

    fn consume_expected(&mut self, expected: u8) -> io::Result<()> {
        let b = self.next_byte()?.ok_or_else(|| error_unexpected_eof())?;
        if b != expected {
            err(&format!(
                "unexpected character '{}', expecting '{}'",
                ascii::escape_default(b),
                expected
            ))
        } else {
            Ok(())
        }
    }

    fn consume_keyword(&mut self, kw: &str) -> io::Result<bool> {
        for &b in kw.as_bytes() {
            match self.next_byte()? {
                Some(x) => {
                    if x != b {
                        return Ok(false);
                    }
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    fn skip_whitespace(&mut self) -> io::Result<()> {
        while let Some(b) = self.peek_byte()? {
            if matches!(b, b' ' | b'\n' | b'\r' | b'\t') {
                self.consume_byte()?;
            } else {
                break;
            }
        }
        Ok(())
    }

    fn fill_buffer(&mut self) -> io::Result<()> {
        self.len = self.reader.read(&mut self.buf)?;
        self.pos = 0;
        if self.len == 0 {
            self.eof = true;
        }
        Ok(())
    }
}

/**
 * interpret any escape sequence found in a Json string (represented as Vec<u8>)
 * and return the corresponding unescaped Vec<u8>
 *
 * converting between String and Vec<u8> is up to the caller.
 */
pub fn json_unescape_string(v: Vec<u8>) -> io::Result<Vec<u8>> {
    let mut buf = v;
    let len = buf.len();
    let mut ipos: usize = 0;
    let mut opos: usize = 0;

    while ipos < len {
        if buf[ipos] != b'\\' {
            buf[opos] = buf[ipos];
            ipos += 1;
            opos += 1;
            continue;
        }

        ipos += 1;
        if ipos >= len {
            return err("unexpected end while unescaping json string");
        }

        let b = buf[ipos];
        match b {
            b'"' | b'\\' | b'/' => append_byte(&mut buf, &mut opos, b),
            b'b' => append_byte(&mut buf, &mut opos, 0x08),
            b'f' => append_byte(&mut buf, &mut opos, 0x0C),
            b'n' => append_byte(&mut buf, &mut opos, b'\n'),
            b'r' => append_byte(&mut buf, &mut opos, b'\r'),
            b't' => append_byte(&mut buf, &mut opos, b'\t'),
            b'u' => {
                ipos += 1;
                let high = unescape_hex4(&buf, &mut ipos, len)?;

                let ch = if (0xD800..=0xDBFF).contains(&high) {
                    unescape_low_surrogate_to_char(&mut buf, &mut ipos, len, high)?
                } else if (0xDC00..=0xDFFF).contains(&high) {
                    return err_unpaired_low_surrogate(high);
                } else {
                    codepoint_to_char(high as u32)?
                };

                append_utf8(&mut buf, &mut opos, ch);
                continue;
            }
            _ => return err_invalid_escape(b),
        }
        ipos += 1;
    }

    buf.truncate(opos);

    Ok(buf)
}

#[inline]
fn append_byte(buf: &mut Vec<u8>, opos: &mut usize, b: u8) {
    buf[*opos] = b;
    *opos += 1;
}

#[inline]
fn append_utf8(buf: &mut Vec<u8>, opos: &mut usize, ch: char) {
    let mut tmp = [0u8; 4];
    let encoded = ch.encode_utf8(&mut tmp);
    buf[*opos..*opos + encoded.len()].copy_from_slice(encoded.as_bytes());
    *opos += encoded.len();
}

fn surrogate_pair_to_char(high: u16, low: u16) -> io::Result<char> {
    let uni32 = 0x10000 + (((high - 0xD800) as u32) << 10) + ((low - 0xDC00) as u32);

    char::from_u32(uni32).ok_or_else(|| {
        error(&format!(
            "invalid Unicode codepoint U+{:x} in json string escape pair \\u{:04x}\\u{:04x}",
            uni32, high, low
        ))
    })
}

fn codepoint_to_char(uni32: u32) -> io::Result<char> {
    char::from_u32(uni32).ok_or_else(|| {
        error(&format!(
            "invalid Unicode codepoint U+{:x} in json string escape \\u{:04x}",
            uni32, uni32
        ))
    })
}

fn unescape_low_surrogate_to_char(
    buf: &mut Vec<u8>,
    ipos: &mut usize,
    len: usize,
    high: u16,
) -> io::Result<char> {
    let pos = *ipos;
    if pos + 1 >= len || buf[pos] != b'\\' || buf[pos + 1] != b'u' {
        return err_missing_low_surrogate(high);
    }
    *ipos += 2;
    let low = unescape_hex4(&buf, ipos, len)?;
    if !(0xDC00..=0xDFFF).contains(&low) {
        return err_invalid_low_surrogate(high, low);
    }
    surrogate_pair_to_char(high, low)
}

fn unescape_hex4(buf: &[u8], read: &mut usize, len: usize) -> io::Result<u16> {
    if *read + 4 > len {
        return Err(error_incomplete_escape_uxxxx());
    }

    let mut val: u16 = 0;
    for _ in 0..4 {
        let b = buf[*read];
        *read += 1;
        let digit = match b {
            b'0'..=b'9' => (b - b'0') as u16,
            b'a'..=b'f' => (b - b'a' + 10) as u16,
            b'A'..=b'F' => (b - b'A' + 10) as u16,
            _ => return err_invalid_hex_digit(b),
        };
        val = val << 4 | digit;
    }
    Ok(val)
}

fn err_unpaired_low_surrogate<T>(val: u16) -> io::Result<T> {
    err(&format!(
        "unpaired low surrogate \\u{:x} in json string",
        val
    ))
}

fn err_invalid_low_surrogate<T>(high: u16, low: u16) -> io::Result<T> {
    err(&format!(
        "out-of-range low surrogate \\u{:04x} after high surrogate \\u{:04x} in json string",
        low, high
    ))
}

fn err_missing_low_surrogate<T>(high: u16) -> io::Result<T> {
    err(&format!(
        "missing \\u and low surrogate after high surrogate \\u{:x} in json string",
        high
    ))
}

fn err_invalid_escape<T>(b: u8) -> io::Result<T> {
    err(&format!(
        "invalid escape sequence \\{} in json string",
        ascii::escape_default(b)
    ))
}

fn err_invalid_hex_digit<T>(b: u8) -> io::Result<T> {
    err(&format!(
        "invalid hex digit '{}' in \\u json string escape",
        ascii::escape_default(b)
    ))
}

#[inline]
fn err<T>(msg: &str) -> io::Result<T> {
    Err(error(msg))
}

fn error_incomplete_escape_uxxxx() -> io::Error {
    error("incomplete \\u json string escape")
}

fn error_unexpected_eof() -> io::Error {
    error("unexpected EOF")
}

fn error(msg: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, msg)
}
