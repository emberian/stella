//! KG6 — the ICFP-2020 interaction protocol + frame extraction.
//!
//! `galaxy::eval_forced` + `galaxy_decode::decode_forced` give the forced
//! protocol triple `(flag, newState, data)` of ONE application
//! `ap ap protocol state vector`. The ICFP-2020 "Message from Space"
//! interaction protocol wraps that in a loop:
//!
//! ```text
//! interact(protocol, state, vector):
//!     (flag, newState, data) = ap ap protocol state vector
//!     if flag == 0:  return (newState, multipledraw(data))
//!     else:          interact(protocol, newState, modem(data))
//! ```
//!
//! For the self-contained offline galaxy there is no alien server, so the
//! `send` step is the identity `modem = demodulate ∘ modulate` (the galaxy
//! modem round-trips well-formed values) — implemented here via
//! [`crate::modulation`]. `multipledraw` turns `data` (a list of images;
//! each image a list of point vectors `cons x y`) into integer point sets
//! ready to rasterise.
//!
//! FAITHFULNESS: every *reduction* is the engine via `eval_forced` (whose
//! disclosed §60 / sbinarith host-i128 boundary applies — see those docs).
//! This module is pure protocol plumbing over the decoded `GValue`; it
//! fabricates nothing — a malformed/`Opaque`/unforced structure makes the
//! relevant function return `None` (honest stop), never a fake frame.

use crate::constellation::Constellation;
use crate::galaxy;
use crate::galaxy_decode::{decode_forced, GValue};
use crate::modulation::{self, MVal};
use crate::term::{self, TermId};

/// A rendered frame: a list of images, each a list of integer points.
pub type Frame = Vec<Vec<(i128, i128)>>;

// ── GValue ↔ term (feed state/vector back into the engine) ──────────────────

fn cst(name: &str) -> TermId {
    term::mk_app_str(name, vec![])
}
fn ap(f: TermId, x: TermId) -> TermId {
    term::mk_app_str("a", vec![f, x])
}

/// Encode a decoded `GValue` back into the galaxy term universe so it can
/// be applied by the engine: `Num → sbinarith::sint`, `Nil → nil` atom,
/// `Cons → a(a(cons,h),t)` (the ICFP cons value), `Atom → that atom`.
/// `Opaque` (or an `Opaque`-containing structure) ⇒ `None` — we never
/// invent a term for something the engine did not actually produce.
pub fn encode(g: &GValue) -> Option<TermId> {
    match g {
        GValue::Num(n) => Some(crate::sbinarith::sint(*n)),
        GValue::Nil => Some(cst("nil")),
        GValue::Atom(s) => Some(cst(s)),
        GValue::Cons(h, t) => {
            let h = encode(h)?;
            let t = encode(t)?;
            Some(ap(ap(cst("cons"), h), t))
        }
        GValue::Opaque(_) => None,
    }
}

// ── GValue ↔ MVal (the offline modem) ───────────────────────────────────────

fn g_to_m(g: &GValue) -> Option<MVal> {
    match g {
        GValue::Nil => Some(MVal::Nil),
        GValue::Num(n) => Some(MVal::Int(*n)),
        GValue::Cons(h, t) => Some(MVal::Cons(Box::new(g_to_m(h)?), Box::new(g_to_m(t)?))),
        // The modem domain is integers/cons/nil only (ICFP signals); an
        // atom/opaque in `data` is malformed for `send`.
        GValue::Atom(_) | GValue::Opaque(_) => None,
    }
}

fn m_to_g(m: &MVal) -> GValue {
    match m {
        MVal::Nil => GValue::Nil,
        MVal::Int(n) => GValue::Num(*n),
        MVal::Cons(h, t) => GValue::Cons(Box::new(m_to_g(h)), Box::new(m_to_g(t))),
    }
}

/// The offline `modem`: `demodulate ∘ modulate`. Identity on well-formed
/// signal values; the round-trip through the real bit codec is the honest
/// stand-in for `send` to the (absent) alien server. `None` if `data`
/// isn't a pure int/cons/nil signal or the codec round-trip fails.
pub fn modem(data: &GValue) -> Option<GValue> {
    let m = g_to_m(data)?;
    let bits = modulation::modulate(&m);
    let back = modulation::demodulate_all(&bits)?;
    Some(m_to_g(&back))
}

// ── protocol triple + multipledraw ──────────────────────────────────────────

/// A proper `GValue` cons-list → `Vec` of its elements (`None` if improper
/// or not a list).
fn list_vec(g: &GValue) -> Option<Vec<&GValue>> {
    let mut out = Vec::new();
    let mut cur = g;
    loop {
        match cur {
            GValue::Nil => return Some(out),
            GValue::Cons(h, t) => {
                out.push(h.as_ref());
                cur = t;
            }
            _ => return None,
        }
    }
}

/// The decoded result is the 3-list `[flag, newState, data]`. Extract it.
/// (ICFP encodes the triple as `cons flag (cons newState (cons data nil))`.)
pub fn parse_triple(g: &GValue) -> Option<(i128, GValue, GValue)> {
    let v = list_vec(g)?;
    if v.len() != 3 {
        return None;
    }
    let flag = match v[0] {
        GValue::Num(n) => *n,
        _ => return None,
    };
    Some((flag, v[1].clone(), v[2].clone()))
}

/// `multipledraw(data)`: `data` is a list of images; each image is a list
/// of point *vectors* `cons x y` (an improper `Cons(Num,Num)` pair, the
/// ICFP "vec"). Returns the integer point sets, or `None` if the structure
/// isn't that shape (e.g. still-`Opaque` unforced payload).
pub fn multipledraw(data: &GValue) -> Option<Frame> {
    let images = list_vec(data)?;
    let mut frame = Vec::with_capacity(images.len());
    for img in images {
        let pts = list_vec(img)?;
        let mut image = Vec::with_capacity(pts.len());
        for p in pts {
            match p {
                GValue::Cons(x, y) => match (x.as_ref(), y.as_ref()) {
                    (GValue::Num(px), GValue::Num(py)) => image.push((*px, *py)),
                    _ => return None,
                },
                _ => return None,
            }
        }
        frame.push(image);
    }
    Some(frame)
}

// ── the interaction loop ────────────────────────────────────────────────────

/// One protocol step: build `ap ap protocol state vector`, force it, decode
/// the forced result, parse the `(flag,newState,data)` triple. `None` =
/// honest stop (couldn't encode an input, engine didn't yield a clean
/// triple, etc.) — never a fabricated step.
pub fn step(
    phi: &Constellation,
    protocol: TermId,
    state: &GValue,
    vector: &GValue,
    fuel: usize,
    max_forcings: usize,
) -> Option<(i128, GValue, GValue)> {
    let prog = ap(ap(protocol, encode(state)?), encode(vector)?);
    let f = galaxy::eval_forced(phi, prog, fuel, max_forcings);
    let g = decode_forced(phi, &f, fuel, max_forcings);
    parse_triple(&g)
}

/// Run the ICFP interaction loop to a `flag==0` frame (bounded by
/// `max_rounds`). Returns `(finalState, frame)` or `None` if it does not
/// converge / a step failed honestly.
pub fn interact(
    phi: &Constellation,
    protocol: TermId,
    mut state: GValue,
    mut vector: GValue,
    fuel: usize,
    max_forcings: usize,
    max_rounds: usize,
) -> Option<(GValue, Frame)> {
    for _ in 0..max_rounds {
        let (flag, new_state, data) = step(phi, protocol, &state, &vector, fuel, max_forcings)?;
        if flag == 0 {
            return Some((new_state, multipledraw(&data)?));
        }
        state = new_state;
        vector = modem(&data)?;
    }
    None
}

/// Convenience: the galaxy's canonical first interaction — protocol
/// `:entry`, state `nil`, click vector `(0,0)`.
pub fn galaxy_first_frame(
    phi: &Constellation,
    entry: u64,
    fuel: usize,
    max_forcings: usize,
    max_rounds: usize,
) -> Option<(GValue, Frame)> {
    let protocol = galaxy::ref_atom(entry);
    let click = GValue::Cons(Box::new(GValue::Num(0)), Box::new(GValue::Num(0)));
    interact(phi, protocol, GValue::Nil, click, fuel, max_forcings, max_rounds)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn num(n: i128) -> GValue {
        GValue::Num(n)
    }
    fn cons(h: GValue, t: GValue) -> GValue {
        GValue::Cons(Box::new(h), Box::new(t))
    }
    fn list(xs: Vec<GValue>) -> GValue {
        xs.into_iter().rev().fold(GValue::Nil, |acc, x| cons(x, acc))
    }

    #[test]
    fn triple_parses() {
        let g = list(vec![num(0), GValue::Nil, GValue::Nil]);
        assert_eq!(parse_triple(&g), Some((0, GValue::Nil, GValue::Nil)));
        // flag=1, some state, some data
        let g = list(vec![num(1), num(7), GValue::Nil]);
        assert_eq!(parse_triple(&g), Some((1, num(7), GValue::Nil)));
        // not a 3-list
        assert_eq!(parse_triple(&list(vec![num(0), num(1)])), None);
        assert_eq!(parse_triple(&num(0)), None);
    }

    #[test]
    fn multipledraw_shapes() {
        // data = [ [ (1,2), (3,4) ], [ (5,6) ] ]
        let pt = |x, y| cons(num(x), num(y));
        let img1 = list(vec![pt(1, 2), pt(3, 4)]);
        let img2 = list(vec![pt(5, 6)]);
        let data = list(vec![img1, img2]);
        assert_eq!(
            multipledraw(&data),
            Some(vec![vec![(1, 2), (3, 4)], vec![(5, 6)]])
        );
        // empty data ⇒ empty frame
        assert_eq!(multipledraw(&GValue::Nil), Some(vec![]));
        // malformed (a point that isn't a Num pair) ⇒ None, not faked
        let bad = list(vec![list(vec![cons(GValue::Nil, num(1))])]);
        assert_eq!(multipledraw(&bad), None);
        // Opaque payload ⇒ None
        assert_eq!(multipledraw(&GValue::Opaque("unforced:a/2".into())), None);
    }

    #[test]
    fn modem_roundtrips_signals() {
        let v = list(vec![num(1), num(-256), cons(num(0), num(255))]);
        assert_eq!(modem(&v), Some(v.clone()));
        assert_eq!(modem(&GValue::Nil), Some(GValue::Nil));
        assert_eq!(modem(&num(123229502148636)), Some(num(123229502148636)));
        // an atom is not a signal ⇒ honest None
        assert_eq!(modem(&GValue::Atom("t".into())), None);
    }

    #[test]
    fn encode_roundtrips_via_decoder() {
        // encode(Cons(1, Cons(2, Nil))) must be a real cons value the
        // decoder reads back identically.
        let g = list(vec![num(1), num(2)]);
        let t = encode(&g).expect("encodable");
        assert_eq!(crate::galaxy_decode::decode(t), g);
        // Opaque is not encodable (never invent a term).
        assert_eq!(encode(&GValue::Opaque("x".into())), None);
    }
}
