// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
//! Small JSON value type with a deterministic serializer (object keys keep
//! insertion order) and a strict parser, used by the ledger and reports.

#[derive(Clone, Debug, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Num(String), // kept textual so integers round-trip exactly
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

impl Json {
    pub fn obj() -> Json {
        Json::Obj(Vec::new())
    }
    pub fn with(mut self, k: &str, v: impl Into<Json>) -> Json {
        if let Json::Obj(ref mut m) = self {
            m.push((k.to_string(), v.into()));
        }
        self
    }
    pub fn get(&self, k: &str) -> Option<&Json> {
        match self {
            Json::Obj(m) => m.iter().find(|(x, _)| x == k).map(|(_, v)| v),
            _ => None,
        }
    }
    pub fn str(&self) -> Option<&str> {
        match self {
            Json::Str(s) => Some(s),
            _ => None,
        }
    }
    pub fn u64(&self) -> Option<u64> {
        match self {
            Json::Num(n) => n.parse().ok(),
            _ => None,
        }
    }
    pub fn f64(&self) -> Option<f64> {
        match self {
            Json::Num(n) => n.parse().ok(),
            _ => None,
        }
    }
    pub fn boolean(&self) -> Option<bool> {
        match self {
            Json::Bool(b) => Some(*b),
            _ => None,
        }
    }
    pub fn arr(&self) -> Option<&[Json]> {
        match self {
            Json::Arr(a) => Some(a),
            _ => None,
        }
    }
    pub fn dump(&self) -> String {
        let mut s = String::new();
        self.write(&mut s);
        s
    }
    fn write(&self, out: &mut String) {
        match self {
            Json::Null => out.push_str("null"),
            Json::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Json::Num(n) => out.push_str(n),
            Json::Str(s) => esc(s, out),
            Json::Arr(a) => {
                out.push('[');
                for (i, x) in a.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    x.write(out);
                }
                out.push(']');
            }
            Json::Obj(m) => {
                out.push('{');
                for (i, (k, v)) in m.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    esc(k, out);
                    out.push(':');
                    v.write(out);
                }
                out.push('}');
            }
        }
    }
    pub fn parse(s: &str) -> Result<Json, String> {
        let b = s.as_bytes();
        let mut p = 0;
        let v = parse_v(b, &mut p)?;
        ws(b, &mut p);
        if p != b.len() {
            return Err(format!("trailing data at {}", p));
        }
        Ok(v)
    }
}

fn esc(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

fn ws(b: &[u8], p: &mut usize) {
    while *p < b.len() && (b[*p] as char).is_ascii_whitespace() {
        *p += 1;
    }
}

fn parse_v(b: &[u8], p: &mut usize) -> Result<Json, String> {
    ws(b, p);
    if *p >= b.len() {
        return Err("unexpected end".into());
    }
    match b[*p] {
        b'n' if b[*p..].starts_with(b"null") => {
            *p += 4;
            Ok(Json::Null)
        }
        b't' if b[*p..].starts_with(b"true") => {
            *p += 4;
            Ok(Json::Bool(true))
        }
        b'f' if b[*p..].starts_with(b"false") => {
            *p += 5;
            Ok(Json::Bool(false))
        }
        b'"' => Ok(Json::Str(parse_s(b, p)?)),
        b'[' => {
            *p += 1;
            let mut a = Vec::new();
            ws(b, p);
            if *p < b.len() && b[*p] == b']' {
                *p += 1;
                return Ok(Json::Arr(a));
            }
            loop {
                a.push(parse_v(b, p)?);
                ws(b, p);
                match b.get(*p) {
                    Some(b',') => *p += 1,
                    Some(b']') => {
                        *p += 1;
                        return Ok(Json::Arr(a));
                    }
                    _ => return Err("expected , or ]".into()),
                }
            }
        }
        b'{' => {
            *p += 1;
            let mut m = Vec::new();
            ws(b, p);
            if *p < b.len() && b[*p] == b'}' {
                *p += 1;
                return Ok(Json::Obj(m));
            }
            loop {
                ws(b, p);
                let k = parse_s(b, p)?;
                ws(b, p);
                if b.get(*p) != Some(&b':') {
                    return Err("expected :".into());
                }
                *p += 1;
                let v = parse_v(b, p)?;
                m.push((k, v));
                ws(b, p);
                match b.get(*p) {
                    Some(b',') => *p += 1,
                    Some(b'}') => {
                        *p += 1;
                        return Ok(Json::Obj(m));
                    }
                    _ => return Err("expected , or }".into()),
                }
            }
        }
        c if c == b'-' || c.is_ascii_digit() => {
            let st = *p;
            *p += 1;
            while *p < b.len() && (b[*p].is_ascii_digit() || b"+-.eE".contains(&b[*p])) {
                *p += 1;
            }
            Ok(Json::Num(String::from_utf8_lossy(&b[st..*p]).into_owned()))
        }
        c => Err(format!("unexpected byte {:?}", c as char)),
    }
}

fn parse_s(b: &[u8], p: &mut usize) -> Result<String, String> {
    if b.get(*p) != Some(&b'"') {
        return Err("expected string".into());
    }
    *p += 1;
    let mut out: Vec<u8> = Vec::new();
    while *p < b.len() {
        let c = b[*p];
        *p += 1;
        match c {
            b'"' => return String::from_utf8(out).map_err(|e| e.to_string()),
            b'\\' => {
                let e = *b.get(*p).ok_or("bad escape")?;
                *p += 1;
                match e {
                    b'"' => out.push(b'"'),
                    b'\\' => out.push(b'\\'),
                    b'/' => out.push(b'/'),
                    b'n' => out.push(b'\n'),
                    b'r' => out.push(b'\r'),
                    b't' => out.push(b'\t'),
                    b'u' => {
                        let h = std::str::from_utf8(b.get(*p..*p + 4).ok_or("bad \\u")?).map_err(|e| e.to_string())?;
                        let cp = u32::from_str_radix(h, 16).map_err(|e| e.to_string())?;
                        *p += 4;
                        let ch = char::from_u32(cp).ok_or("bad codepoint")?;
                        let mut buf = [0u8; 4];
                        out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
                    }
                    _ => return Err("bad escape".into()),
                }
            }
            c => out.push(c),
        }
    }
    Err("unterminated string".into())
}

impl From<&str> for Json {
    fn from(s: &str) -> Json {
        Json::Str(s.to_string())
    }
}
impl From<String> for Json {
    fn from(s: String) -> Json {
        Json::Str(s)
    }
}
impl From<bool> for Json {
    fn from(b: bool) -> Json {
        Json::Bool(b)
    }
}
impl From<u64> for Json {
    fn from(n: u64) -> Json {
        Json::Num(n.to_string())
    }
}
impl From<usize> for Json {
    fn from(n: usize) -> Json {
        Json::Num(n.to_string())
    }
}
impl From<i64> for Json {
    fn from(n: i64) -> Json {
        Json::Num(n.to_string())
    }
}
impl From<f64> for Json {
    fn from(x: f64) -> Json {
        if x.is_finite() {
            Json::Num(format!("{}", x))
        } else {
            Json::Null
        }
    }
}
impl From<Vec<Json>> for Json {
    fn from(v: Vec<Json>) -> Json {
        Json::Arr(v)
    }
}
