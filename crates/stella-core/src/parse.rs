//! A small surface syntax for constellations, and a hand-written
//! recursive-descent parser for it (no external crate; wasm-safe).
//!
//! # Grammar
//!
//! ```text
//! constellation ::= star ( ('+' | ';' | '\n')  star )*
//! star          ::= '[' ']' | '[' ray (',' ray)* ']'
//! ray           ::= term
//! term          ::= polarity? ident ( '(' term (',' term)* ')' )?
//!                  | ident                       (constant, e.g. 0, a, accept)
//!                  | VARIABLE                    (X, Y, Result, …)
//! polarity      ::= '+' | '-' | '−'              (U+2212 also accepted)
//! ```
//!
//! An identifier whose first character is an ASCII uppercase letter is a
//! **variable**; anything else (lowercase, digit, `_`, `$`, `ε`, …) is a
//! **function symbol** (a zero-argument application is a constant).
//!
//! Variables are renamed apart **per star** — `[+f(X)] + [-f(X)]` parses with
//! the two `X`s distinct, matching how constellations are built in code.

use rustc_hash::FxHashMap;

use crate::constellation::{Constellation, Star};
use crate::subst::Renaming;
use crate::term::{mk_app, mk_var_interned, Sym, Term, Var};

/// A parse failure, with a byte offset into the source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub pos: usize,
    pub msg: String,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "parse error at {}: {}", self.pos, self.msg)
    }
}
impl std::error::Error for ParseError {}

type PResult<T> = Result<T, ParseError>;

struct Parser<'a> {
    s: &'a [u8],
    src: &'a str,
    i: usize,
}

impl<'a> Parser<'a> {
    fn new(src: &'a str) -> Self {
        Self { s: src.as_bytes(), src, i: 0 }
    }

    fn err<T>(&self, msg: impl Into<String>) -> PResult<T> {
        Err(ParseError { pos: self.i, msg: msg.into() })
    }

    fn ws(&mut self) {
        while self.i < self.s.len() {
            let c = self.s[self.i];
            if c == b' ' || c == b'\t' || c == b'\r' {
                self.i += 1;
            } else if c == b'#' {
                // line comment to end of line
                while self.i < self.s.len() && self.s[self.i] != b'\n' {
                    self.i += 1;
                }
            } else {
                break;
            }
        }
    }

    fn peek(&self) -> Option<u8> {
        self.s.get(self.i).copied()
    }

    fn eat(&mut self, c: u8) -> bool {
        if self.peek() == Some(c) {
            self.i += 1;
            true
        } else {
            false
        }
    }

    /// Consume a U+2212 MINUS SIGN if present (3-byte UTF-8: E2 88 92).
    fn eat_unicode_minus(&mut self) -> bool {
        if self.s[self.i..].starts_with("−".as_bytes()) {
            self.i += "−".len();
            true
        } else {
            false
        }
    }

    fn is_ident_start(c: u8) -> bool {
        c.is_ascii_alphanumeric() || c == b'_' || c == b'$' || c == b'.'
    }
    fn is_ident_cont(c: u8) -> bool {
        Self::is_ident_start(c) || matches!(c, b'\'' | b'-' )
    }

    /// Read a bare identifier (no polarity). Also accepts a few non-ASCII
    /// constants used in the literature (ε) as whole-token symbols.
    fn ident(&mut self) -> PResult<&'a str> {
        // multi-byte literal symbols seen in the corpus
        for lit in ["ε", "□", "★"] {
            if self.src[self.i..].starts_with(lit) {
                let start = self.i;
                self.i += lit.len();
                return Ok(&self.src[start..self.i]);
            }
        }
        let start = self.i;
        match self.peek() {
            Some(c) if Self::is_ident_start(c) => {}
            _ => return self.err("expected an identifier"),
        }
        while let Some(c) = self.peek() {
            if Self::is_ident_cont(c) {
                self.i += 1;
            } else {
                break;
            }
        }
        Ok(&self.src[start..self.i])
    }

    fn is_variable(name: &str) -> bool {
        name.as_bytes().first().is_some_and(u8::is_ascii_uppercase)
    }

    /// term ::= polarity? ident ( '(' args ')' )? | VARIABLE
    fn term(&mut self) -> PResult<Term> {
        self.ws();
        let mut prefix = "";
        if self.eat(b'+') {
            prefix = "+";
        } else if self.eat(b'-') || self.eat_unicode_minus() {
            prefix = "-";
        }
        self.ws();
        let name = self.ident()?;

        if prefix.is_empty() && Self::is_variable(name) {
            // A bare variable. Variables take no arguments.
            return Ok(mk_var_interned(Var::intern(name)));
        }

        let mut args: Vec<Term> = Vec::new();
        self.ws();
        if self.eat(b'(') {
            loop {
                self.ws();
                if self.eat(b')') {
                    break;
                }
                args.push(self.term()?);
                self.ws();
                if self.eat(b',') {
                    continue;
                }
                if self.eat(b')') {
                    break;
                }
                return self.err("expected ',' or ')' in argument list");
            }
        }
        let sym = Sym::parse(&format!("{prefix}{name}"));
        Ok(mk_app(sym, args))
    }

    /// star ::= '[' ']' | '[' ray (',' ray)* ']'
    fn star(&mut self) -> PResult<Star> {
        self.ws();
        if !self.eat(b'[') {
            return self.err("expected '[' to begin a star");
        }
        let mut rays: Star = Vec::new();
        self.ws();
        if self.eat(b']') {
            return Ok(rays);
        }
        loop {
            rays.push(self.term()?);
            self.ws();
            if self.eat(b',') {
                continue;
            }
            if self.eat(b']') {
                break;
            }
            return self.err("expected ',' or ']' in star");
        }
        Ok(rays)
    }

    fn at_end(&mut self) -> bool {
        self.ws();
        // newlines are separators, not whitespace; skip trailing ones at EOF check
        while self.peek() == Some(b'\n') {
            self.i += 1;
            self.ws();
        }
        self.i >= self.s.len()
    }

    /// constellation ::= star ( ('+'|';'|'\n')+ star )*
    fn constellation(&mut self) -> PResult<Constellation> {
        let mut stars: Constellation = Vec::new();
        loop {
            stars.push(self.star()?);
            // separators: + ; or newline(s)
            let mut saw_sep = false;
            loop {
                self.ws();
                match self.peek() {
                    Some(b'+') => {
                        // '+' is a separator only when not the start of a +ray,
                        // i.e. only between stars (next non-ws is not '[' means
                        // malformed anyway). A star always starts with '['.
                        self.i += 1;
                        saw_sep = true;
                    }
                    Some(b';') | Some(b'\n') => {
                        self.i += 1;
                        saw_sep = true;
                    }
                    _ => break,
                }
            }
            self.ws();
            while self.peek() == Some(b'\n') {
                self.i += 1;
                self.ws();
            }
            if self.i >= self.s.len() {
                break;
            }
            if !saw_sep && self.peek() != Some(b'[') {
                return self.err("expected '+' (or newline) between stars");
            }
            if self.peek() != Some(b'[') {
                break;
            }
        }
        Ok(stars)
    }
}

/// Rename variables apart per star so two stars never accidentally share a
/// variable — but keep the names *readable*: the first star keeps the names
/// as written; later stars get a `_<i>` suffix. (Opaque fresh names would
/// make the unifier readout unintelligible.)
fn rename_star_apart(star: &Star, star_idx: usize, _counter: &mut u32) -> Star {
    if star_idx == 0 {
        return star.clone();
    }
    let mut map: FxHashMap<Var, Var> = FxHashMap::default();
    for &r in star {
        for v in r.vars() {
            map.entry(v).or_insert_with(|| {
                Var::intern(&format!("{}_{star_idx}", v.as_str()))
            });
        }
    }
    if map.is_empty() {
        return star.clone();
    }
    let ren = Renaming::from_map(map);
    star.iter().map(|&r| ren.apply(r)).collect()
}

/// Parse a constellation from the surface syntax. Variables are renamed apart
/// per star.
pub fn parse_constellation(src: &str) -> Result<Constellation, ParseError> {
    let src = src.trim();
    if src.is_empty() {
        return Ok(Vec::new());
    }
    let mut p = Parser::new(src);
    let raw = p.constellation()?;
    if !p.at_end() {
        return Err(ParseError {
            pos: p.i,
            msg: "unexpected trailing input".to_string(),
        });
    }
    let mut counter = 0u32;
    Ok(raw
        .iter()
        .enumerate()
        .map(|(idx, star)| rename_star_apart(star, idx, &mut counter))
        .collect())
}

/// Parse a single star (one bracketed group). Variables are renamed apart from
/// any other star you parse separately (uses the `0` star index + a counter you
/// own, so call with distinct prefixes if mixing).
pub fn parse_star(src: &str) -> Result<Star, ParseError> {
    let c = parse_constellation(src)?;
    match c.len() {
        0 => Ok(Vec::new()),
        1 => Ok(c.into_iter().next().unwrap()),
        _ => Err(ParseError { pos: 0, msg: "expected a single star".to_string() }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interactive::iex;

    #[test]
    fn parses_horn_add_and_runs() {
        // Φ: Horn addition.
        let phi = parse_constellation(
            "[+add(0, Y, Y)] + [-add(X, Y, Z), +add(s(X), Y, s(Z))]",
        )
        .expect("phi parses");
        assert_eq!(phi.len(), 2);
        // Ψ: 1 + 1 = R ?
        let psi = parse_constellation("[-add(s(0), s(0), R), R]").expect("psi parses");
        let out = iex(&phi, psi, 200);
        let s: String = out
            .psi
            .iter()
            .map(|st| st.iter().map(|r| format!("{r}")).collect::<String>())
            .collect();
        assert!(s.contains("s(s(0))"), "1+1 should be s(s(0)); got {s}");
    }

    #[test]
    fn vars_are_renamed_apart_per_star() {
        let c = parse_constellation("[+f(X)] + [-f(X), X]").unwrap();
        let v0: Vec<Var> = c[0].iter().flat_map(|r| r.vars()).collect();
        let v1: Vec<Var> = c[1].iter().flat_map(|r| r.vars()).collect();
        for a in &v0 {
            assert!(!v1.contains(a), "stars must not share variables");
        }
    }

    #[test]
    fn empty_and_unicode_minus() {
        assert_eq!(parse_constellation("").unwrap().len(), 0);
        assert_eq!(parse_constellation("[]").unwrap().len(), 1);
        let c = parse_constellation("[−f(X), X]").unwrap();
        assert_eq!(c.len(), 1);
        assert_eq!(c[0].len(), 2);
    }

    #[test]
    fn rejects_garbage() {
        assert!(parse_constellation("[+f(X)").is_err());
        assert!(parse_constellation("+f(X)]").is_err());
        assert!(parse_constellation("[f(]]").is_err());
    }
}
