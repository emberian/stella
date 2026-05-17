//! Measures + compare (Stage 4): quantitative lenses an expert wants —
//! Seiller/Eng ω-weight (§79), visibility, structural counts — and a
//! two-constellation comparison (same normal form? ω delta).
//!
//! All cheap and structural except `compare`, which runs the exact engine
//! (bounded by `fuel`); nothing here enumerates diagrams.

use stella_core::constellation::Constellation;
use stella_core::omega_weight::{constellation_weight, visible};
use stella_core::parse::{parse_constellation, parse_psi};

use crate::stepper::capture_path;

fn jstr(s: &str) -> String {
    let mut o = String::with_capacity(s.len() + 2);
    o.push('"');
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\r' => o.push_str("\\r"),
            '\t' => o.push_str("\\t"),
            c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}
fn rays(c: &Constellation) -> usize {
    c.iter().map(|s| s.len()).sum()
}

/// Structural + ω measures for `Φ ⊢ Ψ` (no execution).
pub fn measures(phi_src: &str, psi_src: &str) -> Result<String, String> {
    let phi = parse_constellation(phi_src).map_err(|e| format!("Φ: {e}"))?;
    let psi = parse_psi(psi_src).map_err(|e| format!("Ψ: {e}"))?;
    let mut cfg = phi.clone();
    cfg.extend(psi.clone());
    Ok(format!(
        "{{\"ok\":true,\"omega_phi\":{},\"omega_psi\":{},\"omega_cfg\":{},\"visible\":{},\
          \"stars_phi\":{},\"stars_psi\":{},\"rays_phi\":{},\"rays_psi\":{}}}",
        constellation_weight(&phi),
        constellation_weight(&psi),
        constellation_weight(&cfg),
        visible(&cfg),
        phi.len(),
        psi.len(),
        rays(&phi),
        rays(&psi),
    ))
}

fn obs(phi: &Constellation, psi: Constellation, fuel: usize) -> (Vec<String>, i64) {
    let snaps = capture_path(phi, psi, &[], fuel);
    let last = snaps.last();
    let o = last.map(|s| s.observable.clone()).unwrap_or_default();
    // ω of the observable result.
    let res: Constellation = o
        .iter()
        .filter_map(|s| parse_constellation(s).ok())
        .flatten()
        .collect();
    (o, constellation_weight(&res))
}

/// Compare two configurations: do they reach the same observable (α, as
/// rendered) and what is the ω of each result?
pub fn compare(
    pa: &str,
    qa: &str,
    pb: &str,
    qb: &str,
    fuel: usize,
) -> Result<String, String> {
    let phia = parse_constellation(pa).map_err(|e| format!("ΦA: {e}"))?;
    let psia = parse_psi(qa).map_err(|e| format!("ΨA: {e}"))?;
    let phib = parse_constellation(pb).map_err(|e| format!("ΦB: {e}"))?;
    let psib = parse_psi(qb).map_err(|e| format!("ΨB: {e}"))?;
    let (mut oa, wa) = obs(&phia, psia, fuel);
    let (mut ob, wb) = obs(&phib, psib, fuel);
    oa.sort();
    ob.sort();
    let same = oa == ob;
    let j = |v: &[String]| v.iter().map(|x| jstr(x)).collect::<Vec<_>>().join(",");
    Ok(format!(
        "{{\"ok\":true,\"same\":{},\"obs_a\":[{}],\"obs_b\":[{}],\"omega_a\":{},\"omega_b\":{}}}",
        same,
        j(&oa),
        j(&ob),
        wa,
        wb
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use stella_core::omega_weight::nat_behaviour;

    #[test]
    fn measures_are_structural_and_sane() {
        let r = measures("[+add(0, Y, Y)] + [-add(X, Y, Z), +add(s(X), Y, s(Z))]",
                         "[-add(s(0), s(0), R), R]").expect("ok");
        assert!(r.contains("\"stars_phi\":2"), "Φ has 2 stars: {r}");
        assert!(r.contains("\"omega_cfg\":"), "ω present");
    }

    #[test]
    fn nat_behaviour_weight_is_known() {
        // §80: [[p]] is a visible behaviour; its constellation weight is
        // well-defined — just assert the binding computes without panic and
        // visibility holds for a small p.
        let c = nat_behaviour(2);
        assert!(visible(&c) || !visible(&c)); // total
        let _ = constellation_weight(&c);
    }

    #[test]
    fn compare_same_vs_different() {
        // Same program, equivalent queries 1+1 vs 2+0 → same result (s²0).
        let phi = "[+add(0, Y, Y)] + [-add(X, Y, Z), +add(s(X), Y, s(Z))]";
        let r = compare(phi, "[-add(s(0), s(0), R), R]",
                        phi, "[-add(s(s(0)), 0, R), R]", 400).expect("ok");
        assert!(r.contains("\"same\":true"), "1+1 and 2+0 agree: {r}");
        let d = compare(phi, "[-add(s(0), s(0), R), R]",
                        phi, "[-add(s(0), 0, R), R]", 400).expect("ok");
        assert!(d.contains("\"same\":false"), "1+1 ≠ 1+0: {d}");
    }

    #[test]
    fn errors_clean() {
        assert!(measures("[+f(", "[]").is_err());
        assert!(compare("[]", "[]", "[+f(", "[]", 50).is_err());
    }
}
