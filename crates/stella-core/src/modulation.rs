//! ICFP-2020 "Message from Space" linear bit modulation codec.
//!
//! This is a faithful, dependency-free implementation of the galaxy "modem":
//! the self-describing linear bit encoding used by the ICFP-2020 contest's
//! *Message from Space* / *galaxy* protocol. It encodes a tiny value universe
//! — nil, signed integers, and cons cells (pairs / lists) — into a string of
//! `'0'`/`'1'` characters, and parses it back.
//!
//! The value type is defined locally ([`MVal`]) so this file stays disjoint
//! from `crate::galaxy_decode`; nothing here imports from the rest of the
//! crate.
//!
//! ## Encoding (authoritative)
//!
//! [`modulate`] is defined structurally:
//!
//! * `Nil`            → `"00"`.
//! * `Cons(h, t)`     → `"11"` ++ `modulate(h)` ++ `modulate(t)`.
//! * `Int(n)`:
//!   1. **Sign bits**: `n >= 0` → `"01"`, `n < 0` → `"10"`.
//!   2. Let `a = |n|` as an unsigned magnitude.
//!      * If `a == 0`: width prefix is the single bit `"0"` and there is no
//!        payload, so `modulate(Int(0)) == "01" + "0" == "010"`.
//!      * Otherwise let `bits` = number of significant binary digits of `a`
//!        and `k = ceil(bits / 4)` = number of 4-bit nibbles needed. The
//!        width prefix is `"1"` repeated `k` times followed by a single
//!        `"0"`. The payload is `a` in big-endian binary, zero-padded on the
//!        left to exactly `4 * k` bits.
//!   3. The full encoding is `sign ++ widthprefix ++ payload`.
//!
//! Three reference encodings pin the spec down:
//! `modulate(Nil) == "00"`, `modulate(Int(0)) == "010"`, and
//! `modulate(Int(1)) == "01100001"` — `"01"` sign ++ `"10"` width (one
//! nibble) ++ `"0001"` 4-bit payload (8 bits total). This matches the public
//! ICFP-2020 modem; the build prompt's "0110001" was an internal-inconsistent
//! typo (its own rule yields 8 bits, not 7).
//!
//! [`demodulate`] is the exact inverse: it parses one value from the front of
//! a bit string and reports how many bits it consumed. It is total and never
//! panics — malformed input yields `None`. [`demodulate_all`] additionally
//! requires that the value consume the entire input.
//!
//! The round-trip law holds for every well-formed value `v`:
//! `demodulate(&modulate(v)) == Some((v.clone(), modulate(v).len()))`.
//!
//! ## Range note
//!
//! Magnitudes are carried as `u128`. `Int(i128::MIN)` is intentionally *not*
//! supported because `|i128::MIN|` does not fit in `i128`; its magnitude
//! still fits in `u128`, so [`modulate`] handles it via `unsigned_abs`, but
//! constructing it is outside the tested well-formed range. All other `i128`
//! values round-trip.

/// The value universe of the ICFP-2020 modem: nil, signed integers, and
/// cons cells. Lists are right-nested `Cons` chains terminated by `Nil`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MVal {
    /// The empty list / `nil`.
    Nil,
    /// A signed integer literal.
    Int(i128),
    /// A pair: `Cons(head, tail)`.
    Cons(Box<MVal>, Box<MVal>),
}

/// Modulate a value into a string of `'0'`/`'1'` per the ICFP-2020 modem.
///
/// See the module docs for the full rule set. Total; never panics.
pub fn modulate(v: &MVal) -> String {
    let mut out = String::new();
    modulate_into(v, &mut out);
    out
}

fn modulate_into(v: &MVal, out: &mut String) {
    match v {
        MVal::Nil => out.push_str("00"),
        MVal::Cons(h, t) => {
            out.push_str("11");
            modulate_into(h, out);
            modulate_into(t, out);
        }
        MVal::Int(n) => modulate_int_into(*n, out),
    }
}

fn modulate_int_into(n: i128, out: &mut String) {
    // Sign bits.
    out.push_str(if n >= 0 { "01" } else { "10" });

    // Magnitude as u128 (handles i128::MIN whose abs overflows i128).
    let a: u128 = n.unsigned_abs();

    if a == 0 {
        // Width prefix "0", no payload.
        out.push('0');
        return;
    }

    // Number of significant binary digits.
    let bits = (u128::BITS - a.leading_zeros()) as usize;
    // Number of 4-bit nibbles, ceil(bits / 4).
    let k = bits.div_ceil(4);

    // Width prefix: k ones then a zero.
    for _ in 0..k {
        out.push('1');
    }
    out.push('0');

    // Payload: big-endian binary, zero-padded to exactly 4*k bits.
    let width = 4 * k;
    for i in (0..width).rev() {
        let bit = (a >> i) & 1;
        out.push(if bit == 1 { '1' } else { '0' });
    }
}

/// Parse exactly one value from the front of `bits`.
///
/// Returns the decoded [`MVal`] together with the number of leading bit
/// characters consumed, or `None` if the prefix is not a well-formed modem
/// encoding. Total; never panics. Inverse of [`modulate`].
pub fn demodulate(bits: &str) -> Option<(MVal, usize)> {
    let b = bits.as_bytes();
    // Reject any non-'0'/'1' byte up front so indexing stays well-defined.
    if b.iter().any(|&c| c != b'0' && c != b'1') {
        return None;
    }
    parse(b, 0)
}

/// Demodulate exactly one value and require that it consumes *all* of `bits`.
///
/// Returns `None` if the input is malformed or if there are leftover bits.
pub fn demodulate_all(bits: &str) -> Option<MVal> {
    let (v, used) = demodulate(bits)?;
    if used == bits.len() {
        Some(v)
    } else {
        None
    }
}

/// Recursive-descent parser over the byte slice starting at `pos`.
/// Returns the value and the absolute end position (so consumed = end - pos
/// for the top-level call where pos == 0).
fn parse(b: &[u8], pos: usize) -> Option<(MVal, usize)> {
    // Need at least the 2 tag/sign bits.
    let t0 = *b.get(pos)?;
    let t1 = *b.get(pos + 1)?;
    let mut p = pos + 2;

    match (t0, t1) {
        (b'0', b'0') => Some((MVal::Nil, p)),
        (b'1', b'1') => {
            let (h, p1) = parse(b, p)?;
            let (t, p2) = parse(b, p1)?;
            Some((MVal::Cons(Box::new(h), Box::new(t)), p2))
        }
        (b'0', b'1') | (b'1', b'0') => {
            let negative = t0 == b'1'; // "10" → negative, "01" → non-negative.

            // Width prefix: count leading '1's until a terminating '0'.
            let mut k: usize = 0;
            loop {
                match b.get(p) {
                    Some(b'1') => {
                        k += 1;
                        p += 1;
                    }
                    Some(b'0') => {
                        p += 1;
                        break;
                    }
                    _ => return None, // ran off the end with no terminator
                }
            }

            if k == 0 {
                // Encodes zero; no payload. Sign is irrelevant (canonically
                // "01" "0"), but accept either sign tag for robustness.
                return Some((MVal::Int(0), p));
            }

            // Payload: exactly 4*k bits, big-endian.
            let width = 4 * k;
            if p + width > b.len() {
                return None;
            }
            // 4*k must fit a u128 magnitude to round-trip i128 cleanly; we
            // still parse wider payloads but guard the final i128 cast.
            let mut a: u128 = 0;
            for i in 0..width {
                let bit = match b[p + i] {
                    b'0' => 0u128,
                    b'1' => 1u128,
                    _ => return None,
                };
                // u128 overflow guard: payloads with more than 128
                // significant bits cannot be represented and yield None.
                // `checked_mul`/`checked_add` (not `checked_shl`, which only
                // validates the shift amount) catch the wrap.
                a = a.checked_mul(2)?.checked_add(bit)?;
            }
            p += width;

            let val: i128 = if negative {
                // -a: representable when a <= |i128::MIN|.
                if a == (i128::MIN as u128).wrapping_neg() {
                    // a == 2^127 → i128::MIN
                    i128::MIN
                } else {
                    let m: i128 = i128::try_from(a).ok()?;
                    m.checked_neg()?
                }
            } else {
                i128::try_from(a).ok()?
            };
            Some((MVal::Int(val), p))
        }
        _ => None, // unreachable: bytes are pre-validated to be '0'/'1'
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rt(v: MVal) {
        let m = modulate(&v);
        assert!(
            m.chars().all(|c| c == '0' || c == '1'),
            "modulate produced non-bit chars for {v:?}: {m}"
        );
        assert_eq!(
            demodulate(&m),
            Some((v.clone(), m.len())),
            "demodulate round-trip failed for {v:?} (encoding {m})"
        );
        assert_eq!(
            demodulate_all(&m),
            Some(v.clone()),
            "demodulate_all round-trip failed for {v:?} (encoding {m})"
        );
    }

    #[test]
    fn reference_encodings() {
        // Canonical ICFP-2020 modem reference values.
        assert_eq!(modulate(&MVal::Nil), "00");
        assert_eq!(modulate(&MVal::Int(0)), "010");
        // NOTE: the build prompt asserted modulate(Int(1)) == "0110001"
        // (7 bits). That contradicts the prompt's own construction rule
        // (sign "01" ++ width "10" ++ 4-bit payload "0001" = 8 bits) and the
        // public ICFP-2020 reference. The faithful value is "01100001".
        assert_eq!(modulate(&MVal::Int(1)), "01100001");
        // A few more canonical pins.
        assert_eq!(modulate(&MVal::Int(-1)), "10100001");
        assert_eq!(modulate(&MVal::Int(2)), "01100010");
        assert_eq!(modulate(&MVal::Int(255)), "0111011111111");
        assert_eq!(modulate(&MVal::Int(256)), "011110000100000000");
    }

    #[test]
    fn roundtrip_nil() {
        rt(MVal::Nil);
    }

    #[test]
    fn roundtrip_small_ints() {
        rt(MVal::Int(0));
        rt(MVal::Int(1));
        rt(MVal::Int(-1));
        rt(MVal::Int(255));
        rt(MVal::Int(256));
        rt(MVal::Int(-256));
        rt(MVal::Int(2));
        rt(MVal::Int(-2));
        rt(MVal::Int(15));
        rt(MVal::Int(16));
    }

    #[test]
    fn int_payload_shapes() {
        // 1: "01" sign + "10" width (k=1) + "0001" payload (4 bits).
        assert_eq!(modulate(&MVal::Int(1)), "01".to_string() + "10" + "0001");
        // 255 is 8 bits → k=2 nibbles, width "110", payload "11111111".
        assert_eq!(
            modulate(&MVal::Int(255)),
            "01".to_string() + "110" + "11111111"
        );
        // 256 needs 9 bits → k=3 nibbles (12 bits), width "1110".
        assert_eq!(
            modulate(&MVal::Int(256)),
            "01".to_string() + "1110" + "000100000000"
        );
        // -256: sign "10", same width/payload as 256.
        assert_eq!(
            modulate(&MVal::Int(-256)),
            "10".to_string() + "1110" + "000100000000"
        );
    }

    #[test]
    fn roundtrip_nested_list() {
        let list = MVal::Cons(
            Box::new(MVal::Int(1)),
            Box::new(MVal::Cons(Box::new(MVal::Int(2)), Box::new(MVal::Nil))),
        );
        rt(list);
    }

    #[test]
    fn roundtrip_deep_and_large() {
        rt(MVal::Int(123_229_502_148_636));
        rt(MVal::Int(-123_229_502_148_636));
        rt(MVal::Int(i128::MAX / 2));
        rt(MVal::Int(-(i128::MAX / 2)));
        rt(MVal::Int(i128::MAX));
        rt(MVal::Int(i128::MIN + 1));
        rt(MVal::Int(u64::MAX as i128));
        rt(MVal::Int(-(u64::MAX as i128)));

        // A deeply nested heterogeneous structure.
        let deep = MVal::Cons(
            Box::new(MVal::Cons(
                Box::new(MVal::Int(-7)),
                Box::new(MVal::Cons(Box::new(MVal::Int(0)), Box::new(MVal::Nil))),
            )),
            Box::new(MVal::Cons(
                Box::new(MVal::Nil),
                Box::new(MVal::Cons(
                    Box::new(MVal::Int(i128::MAX / 3)),
                    Box::new(MVal::Int(-99999)),
                )),
            )),
        );
        rt(deep);
    }

    #[test]
    fn property_constructed_vals() {
        let samples = vec![
            MVal::Nil,
            MVal::Int(0),
            MVal::Int(1),
            MVal::Int(-1),
            MVal::Int(42),
            MVal::Int(-4096),
            MVal::Cons(Box::new(MVal::Nil), Box::new(MVal::Nil)),
            MVal::Cons(Box::new(MVal::Int(7)), Box::new(MVal::Nil)),
            MVal::Cons(
                Box::new(MVal::Int(-3)),
                Box::new(MVal::Cons(
                    Box::new(MVal::Int(1_000_000)),
                    Box::new(MVal::Nil),
                )),
            ),
        ];
        for v in samples {
            assert_eq!(
                demodulate_all(&modulate(&v)),
                Some(v.clone()),
                "property failed for {v:?}"
            );
        }
    }

    #[test]
    fn malformed_inputs_return_none() {
        assert_eq!(demodulate(""), None);
        assert_eq!(demodulate("0"), None); // truncated tag
        assert_eq!(demodulate("1"), None);
        assert_eq!(demodulate("11"), None); // cons with no head
        assert_eq!(demodulate("1100"), None); // cons head ok, no tail
        assert_eq!(demodulate("01"), None); // int: no width terminator
        assert_eq!(demodulate("0111"), None); // width prefix, no terminator
        assert_eq!(demodulate("0110"), None); // k=1 width, missing 4-bit payload
        assert_eq!(demodulate("011000"), None); // payload too short
        assert_eq!(demodulate("0120001"), None); // non-bit char
        assert_eq!(demodulate("abc"), None);
    }

    #[test]
    fn demodulate_all_rejects_leftover() {
        // Valid Nil followed by an extra bit.
        assert_eq!(demodulate_all("000"), None);
        // demodulate alone accepts and reports it consumed only 2 bits.
        assert_eq!(demodulate("000"), Some((MVal::Nil, 2)));
    }
}
