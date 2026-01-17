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
use std::env;
use std::ffi::OsStr;
use std::fs;
use std::io;

use json_unshell_tools::json::{self, Writable};

fn main() -> io::Result<()> {
    let mut args = env::args_os();
    let mut output = io::stdout();
    if args.len() <= 1 {
        return copy(io::stdin(), &mut output);
    }
    loop {
        match args.next() {
            Some(arg) => open(arg.as_os_str(), &mut output)?,
            None => return Ok(()),
        }
    }
}


fn open<W: io::Write>(path: &OsStr, mut output: W) -> io::Result<()> {
    let mut input = fs::File::open(path)?;
    copy(&mut input, &mut output)
}

fn copy<R: io::Read, W: io::Write>(input: R, mut output: W) -> io::Result<()> {
    let mut parser = json::PullParser::new(input);

    loop {
        let tok = parser.next_token()?;
        if tok == json::Token::Eof {
            break;
        }
        tok.write_to(&mut output)?;
        if parser.next_stream()? {
            output.write(b"\n")?;
        }
    }
    output.write(b"\n")?;
    Ok(())
}
