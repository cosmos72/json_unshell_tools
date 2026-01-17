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

#[derive(PartialEq)]
pub enum Token {
    StartObject,
    EndObject,
    StartArray,
    EndArray,
    Boolean(bool),
    Number(String), /* contains literal digits, including sign, fraction and exponent */
    String(Vec<u8>), /* contains literal bytes, including escape sequences \uxxxx */
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

impl fmt::Debug for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::StartObject => write!(f, "{{"),
            Token::EndObject => write!(f, "}}"),
            Token::StartArray => write!(f, "["),
            Token::EndArray => write!(f, "]"),
            Token::Boolean(b) => write!(f, "{}", b),
            Token::Number(n) => write!(f, "{:?}", &n),
            Token::String(s) => write!(f, "\"{}\"", String::from_utf8_lossy(&s)),
            Token::Null => write!(f, "null"),
            Token::Colon => write!(f, ":"),
            Token::Comma => write!(f, ","),
            Token::Eof => write!(f, "EOF"),
        }
    }
}

/* -------------------------------- implementation -------------------------- */

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
     * @return Ok(Token) containing the next parsed json token,
     * which will be Token::Eof at end of input stream.
     */
    pub fn next_token(&mut self) -> io::Result<Token> {
        let tok = self.next_raw_token()?;
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
        if self.root == RootState::Done && self.stack.is_empty() {
            self.skip_whitespace()?;
            if !self.eof {
                self.root = RootState::ExpectValue;
            }
            Ok(!self.eof)
        } else {
            Ok(false)
        }
    }

    fn next_raw_token(&mut self) -> io::Result<Token> {
        self.skip_whitespace()?;

        let ch = match self.peek_byte()? {
            Some(b) => b,
            None => return Ok(Token::Eof),
        };

        match ch {
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
            b'"' => self.parse_string(),
            b'-' | b'0'..=b'9' => self.parse_number(),
            b'f' | b't' => self.parse_boolean(ch),
            b'n' => self.parse_null(),
            _ => err(&format!(
                "unexpected character '{}'",
                ascii::escape_default(ch)
            )),
        }
    }

    /* ---------- Parsing ---------- */

    fn parse_string(&mut self) -> io::Result<Token> {
        self.consume_expected(b'"')?;
        let mut out: Vec<u8> = Vec::new();

        loop {
            let b = self
                .next_byte()?
                .ok_or_else(|| error("unterminated json string"))?;
            match b {
                b'"' => break,
                b'\\' => {
                    out.push(b);
                    let e = self
                        .next_byte()?
                        .ok_or_else(|| error("unterminated json string"))?;
                    out.push(e);
                }
                0x00..=0x1F => return err(&format!("invalid control byte {} in json string", b)),
                _ => out.push(b),
            }
        }

        Ok(Token::String(out))
    }

    fn parse_number(&mut self) -> io::Result<Token> {
        let mut s = String::new();

        if self.peek_byte()? == Some(b'-') {
            s.push('-');
            self.consume_byte()?;
        }

        match self.peek_byte()? {
            Some(b'0') => {
                s.push('0');
                self.consume_byte()?;
                match self.peek_byte()? {
                    Some(x) => {
                        if !matches!(x, b',' | b']' | b'}' | b' ' | b'\n' | b'\r' | b'\t') {
                            return err(&format!("invalid byte {} after 0 in json number", x));
                        }
                    }
                    None => {}
                }
            }
            Some(b'1'..=b'9') => {
                while let Some(b'0'..=b'9') = self.peek_byte()? {
                    s.push(self.next_byte()?.unwrap() as char);
                }
            }
            Some(b) => return err(&format!("invalid byte {} in json number", b)),
            _ => return err("invalid json number"),
        }

        if self.peek_byte()? == Some(b'.') {
            s.push('.');
            self.consume_byte()?;
            let mut digit = false;
            while let Some(b'0'..=b'9') = self.peek_byte()? {
                digit = true;
                s.push(self.next_byte()?.unwrap() as char);
            }
            if !digit {
                return err(&format!("missing fraction digits in json number {}", s));
            }
        }

        if matches!(self.peek_byte()?, Some(b'e' | b'E')) {
            s.push(self.next_byte()?.unwrap() as char);
            if matches!(self.peek_byte()?, Some(b'+' | b'-')) {
                s.push(self.next_byte()?.unwrap() as char);
            }
            let mut digit = false;
            while let Some(b'0'..=b'9') = self.peek_byte()? {
                digit = true;
                s.push(self.next_byte()?.unwrap() as char);
            }
            if !digit {
                return err(&format!("missing exponent digits in json number {}", s));
            }
        }

        Ok(Token::Number(s))
    }

    fn parse_boolean(&mut self, ch: u8) -> io::Result<Token> {
        if ch == b't' && self.consume_keyword("true")? {
            Ok(Token::Boolean(true))
        } else if ch == b'f' && self.consume_keyword("false")? {
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
                    _ => err(&format!("expecting ',' or '}}', found {:?}", kind)),
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
                    _ => err(&format!("expecting ',' or ']' found {:?}", kind)),
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
                "expecting json array, object or value, found {:?}",
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
        self.next_byte()?.ok_or_else(|| error("unexpected EOF"))?;
        Ok(())
    }

    fn consume_expected(&mut self, expected: u8) -> io::Result<()> {
        let b = self.next_byte()?.ok_or_else(|| error("unexpected EOF"))?;
        if b != expected {
            err(&format!(
                "unexpected character {:?}, expecting {:?}",
                b, expected
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
 * interpret any escape sequence found in a Json string (represented as &[u8])
 * and return the corresponding unescaped String
 */
pub fn unescape(input: &[u8]) -> io::Result<String> {
    let mut bytes = input.iter().copied().peekable();
    let mut output = String::new();

    while let Some(b) = bytes.next() {
        if b != b'\\' {
            output.push(b as char);
            continue;
        }

        let esc = match bytes.next() {
            Some(b) => b,
            None => return err("invalid trailing backslash in json string"),
        };

        match esc {
            b'"' => output.push('"'),
            b'\\' => output.push('\\'),
            b'/' => output.push('/'),
            b'b' => output.push('\u{0008}'),
            b'f' => output.push('\u{000C}'),
            b'n' => output.push('\n'),
            b'r' => output.push('\r'),
            b't' => output.push('\t'),
            b'u' => {
                let uni16 = read_hex4(&mut bytes)?;

                let ch = if (0xD800..=0xDBFF).contains(&uni16) {
                    decode_low_surrogate(&mut bytes, uni16)?
                } else if (0xDC00..=0xDFFF).contains(&uni16) {
                    return err(&format!(
                        "unpaired low surrogate {} in \\u escape in json string",
                        uni16
                    ));
                } else {
                    char::from_u32(uni16 as u32).ok_or_else(|| {
                        error(&format!(
                            "invalid Unicode codepoint {} in \\u escape in json string",
                            uni16
                        ))
                    })?
                };

                output.push(ch);
            }
            _ => {
                return err(&format!(
                    "invalid escape sequence \\{} in json string",
                    esc as char
                ));
            }
        }
    }

    Ok(output)
}

fn decode_low_surrogate<I>(bytes: &mut std::iter::Peekable<I>, high: u16) -> io::Result<char>
where
    I: Iterator<Item = u8>,
{
    match (bytes.next(), bytes.next()) {
        (Some(b'\\'), Some(b'u')) => {
            let low = read_hex4(bytes)?;
            if !(0xDC00..=0xDFFF).contains(&low) {
                return err(&format!(
                    "invalid low surrogate {} in \\u escape in json string",
                    low
                ));
            }

            let uni32 = 0x10000 + (((high - 0xD800) as u32) << 10) + ((low - 0xDC00) as u32);

            char::from_u32(uni32).ok_or_else(|| {
                error(&format!(
                    "invalid Unicode codepoint {} in \\u escape in json string",
                    uni32
                ))
            })
        }
        _ => err(&format!(
            "missing \\u and low surrogate after high surrogate {} in json string",
            high
        )),
    }
}

fn read_hex4<I>(bytes: &mut std::iter::Peekable<I>) -> io::Result<u16>
where
    I: Iterator<Item = u8>,
{
    let mut value: u16 = 0;

    for _ in 0..4 {
        let b = bytes
            .next()
            .ok_or_else(|| error("incomplete \\u escape in json string"))?;

        let digit = match b {
            b'0'..=b'9' => (b - b'0') as u16,
            b'a'..=b'f' => (b - b'a' + 10) as u16,
            b'A'..=b'F' => (b - b'A' + 10) as u16,
            _ => {
                return err(&format!(
                    "invalid hex digit {} in \\u escape in json string",
                    b as char
                ))
            }
        };

        value = (value << 4) | digit;
    }

    Ok(value)
}

fn err<T>(msg: &str) -> io::Result<T> {
    Err(error(msg))
}

fn error(msg: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, msg)
}

/*
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
*/
