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
    let mut output = io::stdout();
    let mut args = env::args_os();
    let _ = args.next(); // skip argv[0]
    if args.len() == 0 {
        return copy(io::stdin(), &mut output);
    }
    for arg in args {
        open(arg.as_os_str(), &mut output)?;
    }
    Ok(())
}

fn open<W: io::Write>(path: &OsStr, mut output: W) -> io::Result<()> {
    let mut input = fs::File::open(path)?;
    copy(&mut input, &mut output)
}

fn copy<R: io::Read, W: io::Write>(input: R, mut output: W) -> io::Result<()> {
    let ret = copy_loop(input, &mut output);
    // flush stdout before reporting any error to stderr
    let _ = output.flush();
    ret
}

fn copy_loop<R: io::Read, W: io::Write>(input: R, mut output: W) -> io::Result<()> {
    let mut parser = json::PullParser::new(input);
    if parser.is_eof()? {
        return Ok(());
    }
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
