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
use std::io::{self, Write};

use json_unshell_tools::json::{self, Writable};

fn main() -> io::Result<()> {
    let mut parser = json::PullParser::new(io::stdin()); // io::Cursor::new(json);
    let mut out = io::stdout();

    loop {
        let tok = parser.next_token()?;
        if tok == json::Token::Eof {
            break;
        }
        tok.write_to(&mut out)?;
        if parser.next_stream()? {
            out.write(b"\n")?;
        }
    }
    out.write(b"\n")?;
    Ok(())
}
