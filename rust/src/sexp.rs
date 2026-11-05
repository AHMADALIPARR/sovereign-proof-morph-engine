// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Minimal S-expression reader (atoms and lists; `;` line comments).

#[derive(Clone, Debug, PartialEq)]
pub enum Sx {
    Atom(String),
    List(Vec<Sx>),
}

pub fn parse_all(src: &str) -> Result<Vec<Sx>, String> {
    let toks = tokenize(src);
    let mut pos = 0;
    let mut out = Vec::new();
    while pos < toks.len() {
        out.push(parse_one(&toks, &mut pos)?);
    }
    Ok(out)
}

pub fn parse(src: &str) -> Result<Sx, String> {
    let mut v = parse_all(src)?;
    if v.len() != 1 {
        return Err(format!("expected exactly one s-expression, found {}", v.len()));
    }
    Ok(v.remove(0))
}

fn tokenize(src: &str) -> Vec<String> {
    let mut toks = Vec::new();
    let mut cur = String::new();
    let mut chars = src.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            ';' => {
                while let Some(&d) = chars.peek() {
                    if d == '\n' {
                        break;
                    }
                    chars.next();
                }
            }
            '(' | ')' => {
                if !cur.is_empty() {
                    toks.push(std::mem::take(&mut cur));
                }
                toks.push(c.to_string());
            }
            c if c.is_whitespace() => {
                if !cur.is_empty() {
                    toks.push(std::mem::take(&mut cur));
                }
            }
            c => cur.push(c),
        }
    }
    if !cur.is_empty() {
        toks.push(cur);
    }
    toks
}

fn parse_one(toks: &[String], pos: &mut usize) -> Result<Sx, String> {
    if *pos >= toks.len() {
        return Err("unexpected end of input".into());
    }
    let t = &toks[*pos];
    *pos += 1;
    match t.as_str() {
        "(" => {
            let mut items = Vec::new();
            loop {
                if *pos >= toks.len() {
                    return Err("unclosed '('".into());
                }
                if toks[*pos] == ")" {
                    *pos += 1;
                    return Ok(Sx::List(items));
                }
                items.push(parse_one(toks, pos)?);
            }
        }
        ")" => Err("unexpected ')'".into()),
        a => Ok(Sx::Atom(a.to_string())),
    }
}

impl Sx {
    pub fn atom(&self) -> Option<&str> {
        match self {
            Sx::Atom(a) => Some(a),
            _ => None,
        }
    }
}
