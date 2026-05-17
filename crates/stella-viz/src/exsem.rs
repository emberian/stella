//! Ex semantics, honest version (Stage 2a).
//!
//! "The meaning of a constellation is its result regardless of strategy."
//! We demonstrate that with the **trusted exact engine** (Stage 0): the
//! canonical result is ɟ(IEx) along the default left-to-right order, and
//! strategy-independence is shown by re-running along a *different* firing
//! order and observing the same ɟ. This is cheap and faithful.
//!
//! A raw concrete-execution cross-check at an explicit copy budget `k` is
//! offered too, clearly secondary — CEx produces freshly-renamed copies and
//! saturates exponentially for recursive Φ, so it is a research aid, not the
//! headline.

use stella_core::concrete::{cex_with_copies, conceal_and_filter};
use stella_core::constellation::{Constellation, Star};
use stella_core::execution::stars_alpha_equiv;
use stella_core::parse::{parse_constellation, parse_psi};

use crate::stepper::capture_path;

fn render_set(stars: &[Star]) -> Vec<String> {
    let mut v: Vec<String> = stars
        .iter()
        .map(|s| {
            let r: Vec<String> = s.iter().map(|x| format!("{x}")).collect();
            format!("[{}]", r.join(", "))
        })
        .collect();
    v.sort();
    v
}

fn same_up_to_alpha(a: &[Star], b: &[Star]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut used = vec![false; b.len()];
    for x in a {
        match b.iter().enumerate().find(|(k, y)| !used[*k] && stars_alpha_equiv(x, y)) {
            Some((k, _)) => used[k] = true,
            None => return false,
        }
    }
    true
}

/// Parse the ɟ-strings of a snapshot's `observable` back to stars for
/// α-comparison. (The stepper already applied the engine's conceal+filter
/// and rendered them; re-parsing keeps the comparison structural.)
fn obs_stars(strs: &[String]) -> Vec<Star> {
    strs
        .iter()
        .filter_map(|s| parse_constellation(s).ok())
        .flatten()
        .collect()
}

pub struct ExSummary {
    /// The canonical result: ɟ(IEx) under the default order (exact, Stage 0).
    pub result: Vec<String>,
    /// ɟ under a deliberately *different* firing order (exact engine).
    pub alt: Vec<String>,
    /// Did the two orders reach the same normal form? (confluence, shown).
    pub order_independent: bool,
    /// Secondary cross-check: ɟ of raw CEx at copy budget `k`.
    pub cex: Vec<String>,
    pub cex_k: usize,
    pub note: String,
}

/// Strategy-independence summary for `Φ ⊢ Ψ`. Uses only the exact engine
/// for the headline; CEx(k) is a clamped secondary cross-check.
pub fn ex_summary(phi_src: &str, psi_src: &str, k: usize, fuel: usize) -> Result<ExSummary, String> {
    let phi = parse_constellation(phi_src).map_err(|e| format!("Φ: {e}"))?;
    let psi = parse_psi(psi_src).map_err(|e| format!("Ψ: {e}"))?;
    let k = k.clamp(1, 12);

    // Default exact run (left-to-right).
    let def = capture_path(&phi, psi.clone(), &[], fuel);
    let def_last = def.last().ok_or("empty run")?;
    let result = def_last.observable.clone();

    // An alternate order: at each step take the *last* available redex
    // instead of the first (capture_path falls back to first where a named
    // choice is no longer valid — still a genuinely different trajectory).
    let alt_path: Vec<(usize, usize)> = def
        .iter()
        .filter(|s| !s.is_final)
        .filter_map(|s| s.fireable.last().map(|f| (f.star, f.ray)))
        .collect();
    let altrun = capture_path(&phi, psi.clone(), &alt_path, fuel);
    let alt = altrun.last().map(|s| s.observable.clone()).unwrap_or_default();

    let order_independent =
        same_up_to_alpha(&obs_stars(&result), &obs_stars(&alt));

    // Secondary: raw concrete execution at copy budget k.
    let mut cfg: Constellation = phi.clone();
    cfg.extend(psi);
    let cex = render_set(&conceal_and_filter(&cex_with_copies(&cfg, k)));

    let note = if order_independent {
        "Same normal form under the default and an alternate firing order — \
         strategy-independent here, shown by the exact engine. (CEx below is \
         a raw concrete-execution cross-check; it renames copies and \
         saturates exponentially for recursive Φ — keep k small.)"
            .to_string()
    } else {
        "The two firing orders gave different ɟ — either the constellation is \
         genuinely non-confluent, or fuel was exhausted before normal form. \
         The CEx cross-check (raw copies, k-bounded) is below."
            .to_string()
    };

    Ok(ExSummary { result, alt, order_independent, cex, cex_k: k, note })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::presets::preset_io;

    fn fmt_c(c: &Constellation) -> String {
        c.iter()
            .map(|s| {
                let r: Vec<String> = s.iter().map(|x| format!("{x}")).collect();
                format!("[{}]", r.join(", "))
            })
            .collect::<Vec<_>>()
            .join(" + ")
    }

    /// Confluence, demonstrated cheaply by the exact engine: Horn addition
    /// reaches the same ɟ under the default and an alternate firing order.
    #[test]
    fn horn_addition_is_order_independent() {
        let (phi, psi) = preset_io(0).unwrap();
        let s = ex_summary(&fmt_c(&phi), &fmt_c(&psi), 2, 400).expect("ok");
        assert!(!s.result.is_empty(), "result non-empty");
        assert!(
            s.order_independent,
            "Horn add must be order-independent; result={:?} alt={:?}",
            s.result, s.alt
        );
        // exact 2+2 = 4
        assert!(
            s.result.iter().any(|r| r.contains("s(s(s(s(0))))")),
            "2+2 = s^4(0); got {:?}",
            s.result
        );
    }

    #[test]
    fn errors_are_clean() {
        assert!(ex_summary("[+f(", "[]", 2, 100).is_err());
    }
}
