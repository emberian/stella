//! Interactive execution `IEx_C(Φ, Ψ)` (Eng §51).
//!
//! ## Overview (§51.2)
//!
//! Interactive execution constructs diagram actualisations "on the fly" by making
//! stars interact directly via fusion, without explicitly building diagrams. It is a
//! *directed* version of concrete execution where the interaction space `Ψ` is
//! consumed linearly.
//!
//! ## Interactive configuration (§51.3)
//!
//! An *interactive configuration* `Φ ⊢_C Ψ` has:
//! - `Φ`: the *reference constellation* — non-linear (infinite supply of each star,
//!   modelled as fresh instances generated on demand via alpha-renaming).
//! - `Ψ`: the *interaction space* — linear (each star is consumed once).
//!
//! ## Set of matchable rays (§51.6)
//!
//! For a ray `r` and constellation `Φ` w.r.t. colour set `C`:
//!
//! ```text
//! mat_Φ^C(r) := {(i, j) ∈ ±IdRays(Φ) | r ⋈ Φ[i][j], colours(r) ∪ colours(Φ[i][j]) ⊆ C}
//! ```
//!
//! ## Self-interaction (§51.7)
//!
//! The *self-interaction* `^{j,j'}▷ Φ[i]` of a star `Φ[i]` along rays `j` and `j'`
//! produces the star `φ` such that:
//! - `I_φ = θ(I_{Φ[i]} − {j, j'})` where `θ = solution{Φ[i][j] =? Φ[i][j']}`.
//!
//! If the unification fails, the self-interaction is undefined (the summand disappears).
//!
//! ## Fusion `φ₁ ^{j,j'}∇ φ₂` (§49.30)
//!
//! The fusion of two stars `φ₁ := φ₁' ⊎ {r₁}` and `φ₂ := φ₂' ⊎ {r₂}` along
//! rays `r₁ = φ₁[j]` and `r₂ = φ₂[j']` (with `r₁ ⋈ r₂`) is:
//!
//! ```text
//! θφ₁' ⊎ θφ₂'
//! ```
//!
//! where `θ = solution{φ₁[j] =? φ₂[j']}` (over underlying terms, §49.27).
//! We write `φ₁ ∇_α φ₂` for fusion after renaming variables apart (§49.30).
//!
//! ## Stellar interaction step (§51.9)
//!
//! Given `Φ ⊢_C Ψ' + Ψ[i]` (select star `Ψ[i]` from interaction space),
//! pick a coloured ray `(i, j) ∈ ±IdRays(Ψ)`. One step rewrites:
//!
//! ```text
//! Φ ⊢_C Ψ' + Ψ[i]
//!
//!   (i,j)
//!    ~~>  Φ ⊢_C Ψ' + Σ_{(i_k,j_k)∈mat_Φ^C(Ψ[i][j])}  Ψ[i] ^{j,j_k}∇_α Φ[i_k]   (ext fusions)
//!                    + Σ_{(i,j_k)∈mat_{Ψ[i]}^C(Ψ[i][j])} ^{j,j_k}▷_α Ψ[i]          (self-interactions)
//! ```
//!
//! The first sum fuses the selected star with a *fresh copy* of each matchable star
//! from `Φ`. The second sum connects two matchable rays within `Ψ[i]` itself.
//! Unification failure causes a summand to silently disappear.
//!
//! The star `Ψ[i]` is consumed (not retained in `Ψ'`).
//!
//! ## `IEx_C(Φ, Ψ)` (§51.10)
//!
//! Drive `Φ ⊢_C Ψ ↝* Φ ⊢_C IEx_C(Φ, Ψ)` to normal form.
//! `IEx_C(Φ) := IEx_C(Φ, Φ)`.
//!
//! Normal form: no coloured ray remains in any star of `Ψ` that is matchable with any
//! ray in `Φ` or within itself.
//!
//! ## Termination (§51.10)
//!
//! Interactive execution is not guaranteed to terminate. We impose a fuel bound
//! (maximum number of steps) and return whether normal form was reached.

use crate::constellation::{Constellation, Star};
use crate::dep_graph::{all_colours, ray_colours};
use crate::polarised::{matchable, ray_polarity, underlying_term, Polarity};
use crate::subst::{freshen, Substitution};
use crate::term::{mk_var_interned, Var, Term};
use crate::unify::{unify, Equation};

// ─────────────────────────────────────────────────────────────────────────────
// Helpers
// ─────────────────────────────────────────────────────────────────────────────

/// Produce a fresh copy of a star by renaming all its variables (§49.26).
///
/// This implements the "infinite supply" semantics of the reference constellation
/// Φ (§51.3, §51.13): Φ is non-linear so each use fetches a fresh rename.
fn freshen_star(star: &Star, counter: &mut u32) -> Star {
    let prefix = format!("f{}", *counter);
    *counter += *counter / 10 + 1;
    let mut c = *counter;
    star.iter()
        .map(|&r| freshen(r, &prefix, &mut c).0)
        .collect()
}

/// Rename all variables in a star with a given prefix, returning the renamed star
/// and substitution. Used for α-renaming before fusion (§49.30 ∇_α).
fn alpha_rename_star(star: &Star, prefix: &str, counter: &mut u32) -> (Star, Substitution) {
    use rustc_hash::FxHashSet;
    let all_vars: Vec<Var> = star
        .iter()
        .flat_map(|&r| r.vars())
        .collect::<FxHashSet<_>>()
        .into_iter()
        .collect();

    let pairs: Vec<(Var, Term)> = all_vars
        .into_iter()
        .map(|v| {
            let fresh_name = format!("{prefix}_{}{counter}", v.as_str());
            *counter += 1;
            let fresh_var = Var::intern(&fresh_name);
            (v, mk_var_interned(fresh_var))
        })
        .collect();
    let subst = Substitution::from_var_pairs(pairs);
    let renamed = star.iter().map(|&r| subst.apply(r)).collect();
    (renamed, subst)
}

// ─────────────────────────────────────────────────────────────────────────────
// mat_Φ^C(r): set of matchable ray identifiers (§51.6)
// ─────────────────────────────────────────────────────────────────────────────

/// `mat_Φ^C(r)` — the set of ray identifiers in `Φ` matchable with `r` (§51.6).
///
/// `mat_Φ^C(r) := {(i, j) ∈ ±IdRays(Φ) | r ⋈ Φ[i][j], colours(r) ∪ colours(Φ[i][j]) ⊆ C}`
///
/// We use all colours of `Φ` for `C` (the full-colour case).
pub fn mat_phi(phi: &Constellation, r: Term) -> Vec<(usize, usize)> {
    mat_phi_c(phi, r, &std::collections::HashSet::new())
}

fn mat_phi_c(phi: &Constellation, r: Term, extra_c: &std::collections::HashSet<String>) -> Vec<(usize, usize)> {
    let mut c_set = all_colours(phi);
    c_set.extend(extra_c.iter().cloned());
    let cr = ray_colours(r);
    let mut result = Vec::new();
    for (i, star) in phi.iter().enumerate() {
        for (j, &ray) in star.iter().enumerate() {
            let rj_pol = ray_polarity(ray);
            if rj_pol == Polarity::Neutral {
                continue;
            }
            let crj = ray_colours(ray);
            if !cr.is_subset(&c_set) || !crj.is_subset(&c_set) {
                continue;
            }
            if matchable(r, ray) {
                result.push((i, j));
            }
        }
    }
    result
}

fn mat_self(star: &Star, j: usize) -> Vec<usize> {
    let r = star[j];
    let mut result = Vec::new();
    for (jk, &ray) in star.iter().enumerate() {
        if jk == j { continue; }
        if matchable(r, ray) {
            result.push(jk);
        }
    }
    result
}

// ─────────────────────────────────────────────────────────────────────────────
// Fusion (§49.30)
// ─────────────────────────────────────────────────────────────────────────────

/// Fusion `φ₁ ^{j,j'}∇_α φ₂` (§49.30).
///
/// Given:
/// - `phi1`: a star with `phi1[j]` the selected ray,
/// - `phi2`: a star with `phi2[j_prime]` the matchable ray,
/// - `phi1[j] ⋈ phi2[j_prime]`.
///
/// Steps:
/// 1. Rename `phi2` variables to make them disjoint from `phi1` (the `_α` part).
/// 2. Compute `θ = solution{underlying(phi1[j]) =? underlying(phi2_renamed[j_prime])}`.
/// 3. Return `θ(phi1 − {phi1[j]}) ⊎ θ(phi2_renamed − {phi2_renamed[j_prime]})`.
///
/// Returns `None` if unification fails (the summand disappears, §51.9).
fn fuse(phi1: &Star, j: usize, phi2_renamed: &Star, j_prime: usize) -> Option<Star> {
    let r1 = underlying_term(phi1[j]);
    let r2 = underlying_term(phi2_renamed[j_prime]);
    let theta = unify(vec![Equation::new(r1, r2)])?;

    let mut result: Star = phi1
        .iter()
        .enumerate()
        .filter(|&(idx, _)| idx != j)
        .map(|(_, &r)| theta.apply(r))
        .collect();

    let rest2: Star = phi2_renamed
        .iter()
        .enumerate()
        .filter(|&(idx, _)| idx != j_prime)
        .map(|(_, &r)| theta.apply(r))
        .collect();

    result.extend(rest2);
    Some(result)
}

// ─────────────────────────────────────────────────────────────────────────────
// Self-interaction (§51.7)
// ─────────────────────────────────────────────────────────────────────────────

/// Self-interaction `^{j,j'}▷ star` (§51.7).
///
/// Connect two matchable rays `j` and `j'` within the same star. Compute
/// `θ = solution{star[j] =? star[j']}` (over underlying terms). Returns
/// `θ(star − {j, j'})` or `None` if unification fails.
fn self_interact(star: &Star, j: usize, j_prime: usize) -> Option<Star> {
    let r1 = underlying_term(star[j]);
    let r2 = underlying_term(star[j_prime]);
    let theta = unify(vec![Equation::new(r1, r2)])?;

    let result: Star = star
        .iter()
        .enumerate()
        .filter(|&(idx, _)| idx != j && idx != j_prime)
        .map(|(_, &r)| theta.apply(r))
        .collect();
    Some(result)
}

// ─────────────────────────────────────────────────────────────────────────────
// Stellar interaction step (§51.9)
// ─────────────────────────────────────────────────────────────────────────────

/// One stellar interaction step (§51.9).
///
/// Given `Φ ⊢_C Ψ' + Ψ[i]`, select a coloured ray `(i, j)` of `Ψ[i]` and
/// produce the new interaction space:
///
/// ```text
/// Ψ' + Σ_{(i_k,j_k)∈mat_Φ(Ψ[i][j])}  Ψ[i] ^{j,j_k}∇_α Φ[i_k]       (external fusions)
///      + Σ_{j_k∈mat_{Ψ[i]}(Ψ[i][j])}  ^{j,j_k}▷ Ψ[i]                 (self-interactions)
/// ```
///
/// Returns the updated `Ψ` (new interaction space), or `None` if no coloured
/// matchable ray could be selected (normal form for this star).
///
/// The selected star `Ψ[i]` is consumed (removed from `Ψ`).
fn interaction_step(
    phi: &Constellation,
    psi: Vec<Star>,
    star_idx: usize,
    ray_idx: usize,
    counter: &mut u32,
    psi_colours: &std::collections::HashSet<String>,
) -> Vec<Star> {
    // Consume Ψ[i] from the interaction space.
    let selected_star = psi[star_idx].clone();
    let mut psi_prime: Vec<Star> = psi
        .into_iter()
        .enumerate()
        .filter(|(idx, _)| *idx != star_idx)
        .map(|(_, s)| s)
        .collect();

    let r = selected_star[ray_idx];

    // First sum: external fusions — interact with fresh copies of Φ stars.
    // C = colours(Φ) ∪ colours(Ψ) (§51.6: full configuration colour set).
    let ext_matches = mat_phi_c(phi, r, psi_colours);
    for (ik, jk) in ext_matches {
        // Fresh copy of Φ[i_k] (§51.13: Φ provides infinite supply).
        // α-rename the entire star at once so shared variables remain linked.
        let phi_star_renamed = {
            let prefix = format!("ext{ik}_{counter}");
            *counter += 1;
            let (renamed, _) = alpha_rename_star(&phi[ik], &prefix, counter);
            renamed
        };
        // Fuse Ψ[i] ^{j, j_k}∇_α Φ[i_k]: rename Φ[i_k] and fuse.
        if let Some(fused) = fuse(&selected_star, ray_idx, &phi_star_renamed, jk) {
            psi_prime.push(fused);
        }
        // unification failure → summand silently disappears (§51.9).
    }

    // Second sum: self-interactions within Ψ[i].
    let self_matches = mat_self(&selected_star, ray_idx);
    for jk in self_matches {
        if let Some(si) = self_interact(&selected_star, ray_idx, jk) {
            psi_prime.push(si);
        }
        // unification failure → summand silently disappears (§51.9).
    }

    psi_prime
}

// ─────────────────────────────────────────────────────────────────────────────
// Normal-form check
// ─────────────────────────────────────────────────────────────────────────────

/// Check whether an interactive configuration `Φ ⊢_C Ψ` is in normal form (§51.9).
///
/// Normal form: no coloured ray `(i, j)` in `Ψ` has any match in `Φ` or within `Ψ[i]`.
///
/// We check:
/// 1. For every coloured ray `r = Ψ[i][j]`, `mat_Φ(r)` is empty, AND
/// 2. `mat_{Ψ[i]}(r)` (self-matchable within the same star, excluding j) is empty.
fn is_normal_form(phi: &Constellation, psi: &[Star]) -> bool {
    let psi_vec: Constellation = psi.to_vec();
    let psi_colours = all_colours(&psi_vec);
    for (_i, star) in psi.iter().enumerate() {
        for (j, &r) in star.iter().enumerate() {
            if ray_polarity(r) == Polarity::Neutral {
                continue;
            }
            if !mat_phi_c(phi, r, &psi_colours).is_empty() {
                return false;
            }
            if !mat_self(star, j).is_empty() {
                return false;
            }
        }
    }
    true
}

// ─────────────────────────────────────────────────────────────────────────────
// IEx_C(Φ, Ψ) (§51.10)
// ─────────────────────────────────────────────────────────────────────────────

/// Result of `IEx_C(Φ, Ψ)`.
#[derive(Debug)]
pub struct IExResult {
    /// The interaction space at normal form (or at fuel exhaustion).
    pub psi: Vec<Star>,
    /// Whether the result is a true normal form (§51.9).
    pub is_normal_form: bool,
    /// Number of steps taken.
    pub steps: usize,
}

/// `IEx_C(Φ, Ψ)` — interactive execution (§51.10).
///
/// Drive `Φ ⊢_C Ψ ↝* Φ ⊢_C IEx_C(Φ, Ψ)` until normal form or fuel exhaustion.
///
/// **Strategy**: at each step, scan `Ψ` for the first coloured ray `(i, j)` that
/// has at least one external or self-interaction available, then apply one step.
/// This is a deterministic (depth-first, left-to-right) strategy; the final result
/// is non-deterministic over all orderings per §51.20, but for Horn programs (which
/// are SLD-complete and deterministic after query selection, §55.6) this produces
/// the correct answer.
///
/// `fuel`: maximum number of steps (to handle non-termination per §51.10).
///         A reasonable default is 1000.
///
/// Returns `IExResult` with the final `Ψ` and whether it is a normal form.
pub fn iex(phi: &Constellation, psi_init: Vec<Star>, fuel: usize) -> IExResult {
    let mut psi = psi_init;
    let mut counter = 0u32;
    let mut steps = 0;

    while steps < fuel {
        // C = colours(Φ) ∪ colours(Ψ) for the full configuration (§51.6).
        let psi_colours = all_colours(&psi);

        // Find the first applicable step: a coloured ray (i,j) in Ψ that has
        // at least one external or self-interaction.
        let mut found_step = None;
        'outer: for (i, star) in psi.iter().enumerate() {
            for (j, &r) in star.iter().enumerate() {
                if ray_polarity(r) == Polarity::Neutral {
                    continue;
                }
                let has_ext = !mat_phi_c(phi, r, &psi_colours).is_empty();
                let has_self = !mat_self(star, j).is_empty();
                if has_ext || has_self {
                    found_step = Some((i, j));
                    break 'outer;
                }
            }
        }

        match found_step {
            None => {
                // Normal form reached.
                return IExResult { psi, is_normal_form: true, steps };
            }
            Some((i, j)) => {
                psi = interaction_step(phi, psi, i, j, &mut counter, &psi_colours);
                steps += 1;
            }
        }
    }

    // Fuel exhausted.
    let nf = is_normal_form(phi, &psi);
    IExResult { psi, is_normal_form: nf, steps }
}

/// Apply **one** resolution step at an explicitly chosen ray `Ψ[i][j]`
/// (§51.8) and return the successor interaction space.
///
/// This is the per-step primitive `iex` uses internally, exposed so a UI can
/// drive non-deterministic execution — letting the reader pick *which* redex
/// resolves, not only the left-to-right one. `counter` must persist across a
/// run so freshly-renamed Φ variables never collide.
///
/// Returns `None` if `(i, j)` is out of range, neutral, or not a redex.
pub fn step_at(
    phi: &Constellation,
    psi: Vec<Star>,
    star_idx: usize,
    ray_idx: usize,
    counter: &mut u32,
) -> Option<Vec<Star>> {
    let star = psi.get(star_idx)?;
    let r = *star.get(ray_idx)?;
    if ray_polarity(r) == Polarity::Neutral {
        return None;
    }
    let psi_colours = all_colours(&psi);
    let has_ext = !mat_phi_c(phi, r, &psi_colours).is_empty();
    let has_self = !mat_self(star, ray_idx).is_empty();
    if !has_ext && !has_self {
        return None;
    }
    Some(interaction_step(
        phi, psi, star_idx, ray_idx, counter, &psi_colours,
    ))
}

/// `IEx_C(Φ) := IEx_C(Φ, Φ)` (§51.10).
///
/// Uses `Φ` itself as both reference constellation and initial interaction space.
/// Fuel default: 1000 steps.
pub fn iex_self(phi: &Constellation, fuel: usize) -> IExResult {
    iex(phi, phi.clone(), fuel)
}

// ─────────────────────────────────────────────────────────────────────────────
// Concealing and noise filtering (re-exported from concrete.rs)
// ─────────────────────────────────────────────────────────────────────────────

pub use crate::concrete::{conceal, conceal_and_filter, noise_filter};

// ─────────────────────────────────────────────────────────────────────────────
// Convenience: IEx with concealing + noise filtering (§55.6, §56.5)
// ─────────────────────────────────────────────────────────────────────────────

/// `↨♭ IEx_C(Φ, Ψ)` — interactive execution followed by concealing and noise filtering.
///
/// This is the standard observable output: only stars with all-neutral rays survive
/// (`↨`), and empty stars are dropped (`♭`). Used in §55.6 (Horn) and §56.5 (NFA).
pub fn iex_concealed(phi: &Constellation, psi: Vec<Star>, fuel: usize) -> (Vec<Star>, bool) {
    let res = iex(phi, psi, fuel);
    let visible = conceal_and_filter(&res.psi);
    (visible, res.is_normal_form)
}

/// `↨♭ IEx_C(Φ, Ψ)` for NFA acceptance: check if `[accept]` is in the result.
///
/// Per §56.5: `A accepts w iff [accept] ∈ ↨♭ IEx(A⋆, w⋆)`.
pub fn iex_nfa_accepts(phi: &Constellation, psi: Vec<Star>, fuel: usize) -> bool {
    let (visible, _) = iex_concealed(phi, psi, fuel);
    let accept_star: Star = vec![crate::term::mk_app_str("accept", vec![])];
    visible.iter().any(|s| s == &accept_star)
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::execution::stars_alpha_equiv;
    use crate::polarised::{neg_ray, pos_ray};
    use crate::automata::{encode_word, encode_nfa, eng_fig561_nfa, nfa_constellation};

    fn var(x: &str) -> Term { crate::term::mk_var(x) }
    fn app(f: &str, args: Vec<Term>) -> Term { crate::term::mk_app_str(f, args) }
    fn c(name: &str) -> Term { crate::term::mk_app_str(name, vec![]) }

    fn nat(n: usize) -> Term {
        let mut t = c("0");
        for _ in 0..n { t = app("s", vec![t]); }
        t
    }

    fn add_prog() -> Constellation {
        vec![
            // star 0: base case [+add(0, Y, Y)]
            vec![pos_ray("add", vec![c("0"), var("Y"), var("Y")])],
            // star 1: step  [-add(X,Y,Z), +add(s(X),Y,s(Z))]
            vec![
                neg_ray("add", vec![var("X"), var("Y"), var("Z")]),
                pos_ray("add", vec![app("s", vec![var("X")]), var("Y"), app("s", vec![var("Z")])]),
            ],
        ]
    }

    fn query_star(m: usize, n: usize) -> Star {
        vec![
            neg_ray("add", vec![nat(m), nat(n), var("R")]),
            var("R"),
        ]
    }

    // ── §55.6: Horn logic program — addition ─────────────────────────────────

    /// §55.6 / §51.11 trace: `↨♭ IEx(Φ⁺_N, [-add(2̄,2̄,R),R])` ≈α `[4̄]`.
    ///
    /// Eng §51.11 explicitly traces this computation. IEx is called with
    /// reference Φ = Φ⁺_N^{2+2} and initial Ψ = query star.
    #[test]
    fn iex_horn_2_plus_2() {
        // Reference constellation: program stars (infinite supply via fresh copies).
        let phi = add_prog();
        // Initial interaction space: the query star.
        let psi = vec![query_star(2, 2)];

        let (visible, normal) = iex_concealed(&phi, psi, 500);

        assert!(normal, "IEx should reach normal form for Horn 2+2");
        let expected = vec![nat(4)];
        let found = visible.iter().any(|s| stars_alpha_equiv(s, &expected));
        assert!(
            found,
            "↨♭ IEx(Φ⁺_N, query(2,2)) should contain [4̄]; got {:?}",
            visible
        );
    }

    /// `↨♭ IEx(Φ⁺_N, [-add(1̄,1̄,R),R])` ≈α `[2̄]` (§55.6, 1+1 case).
    #[test]
    fn iex_horn_1_plus_1() {
        let phi = add_prog();
        let psi = vec![query_star(1, 1)];
        let raw = iex(&phi, psi.clone(), 200);
        eprintln!("DEBUG 1+1: steps={} normal={} psi_len={}", raw.steps, raw.is_normal_form, raw.psi.len());
        for (i, s) in raw.psi.iter().enumerate() { eprintln!("  star[{}]: {:?}", i, s); }
        let (visible, normal) = iex_concealed(&phi, psi, 200);
        assert!(normal, "IEx should reach normal form for Horn 1+1");
        let expected = vec![nat(2)];
        let found = visible.iter().any(|s| stars_alpha_equiv(s, &expected));
        assert!(
            found,
            "↨♭ IEx(Φ⁺_N, query(1,1)) should contain [2̄]; got {:?}",
            visible
        );
    }

    // ── §56.5: NFA acceptance via IEx ────────────────────────────────────────
    //
    // Per §56.5: A accepts w iff [accept] ∈ ↨♭ IEx(A⋆, w⋆).
    //
    // The NFA is Eng's Fig 56.1: accepts {0,1}* words ending in "00".
    // States: q0 (initial), q1, q2 (final).
    // Transitions: q0—0→q0, q0—1→q0, q0—0→q1, q1—0→q2.
    //
    // §56.5 fig: ↨♭ IEx(A⋆, [+i(0·0·0·ε)]) = [accept].

    fn make_nfa_phi_and_psi(word: &[&str]) -> (Constellation, Vec<Star>) {
        let nfa = eng_fig561_nfa();
        // Reference constellation A⋆ (without word star — word is initial Ψ).
        let phi = encode_nfa(&nfa);
        // Initial interaction space: the word star w⋆.
        let psi = vec![encode_word(word)];
        (phi, psi)
    }

    /// §56.5 acceptance: "00" (direct path q0→q1→q2).
    #[test]
    fn iex_nfa_accepts_00() {
        let (phi, psi) = make_nfa_phi_and_psi(&["0", "0"]);
        assert!(
            iex_nfa_accepts(&phi, psi, 500),
            "IEx: NFA should accept '00' (§56.5)"
        );
    }

    /// §56.5 acceptance: "100" (ends in "00").
    #[test]
    fn iex_nfa_accepts_100() {
        let (phi, psi) = make_nfa_phi_and_psi(&["1", "0", "0"]);
        assert!(
            iex_nfa_accepts(&phi, psi, 500),
            "IEx: NFA should accept '100' (§56.5)"
        );
    }

    /// §56.5 rejection: "1" (does not end in "00").
    #[test]
    fn iex_nfa_rejects_1() {
        let (phi, psi) = make_nfa_phi_and_psi(&["1"]);
        assert!(
            !iex_nfa_accepts(&phi, psi, 500),
            "IEx: NFA should reject '1' (§56.5)"
        );
    }

    /// §56.5 rejection: "10" (does not end in "00").
    #[test]
    fn iex_nfa_rejects_10() {
        let (phi, psi) = make_nfa_phi_and_psi(&["1", "0"]);
        assert!(
            !iex_nfa_accepts(&phi, psi, 500),
            "IEx: NFA should reject '10' (§56.5)"
        );
    }

    // ── Basic IEx sanity (§51.14 examples) ───────────────────────────────────

    /// §51.8 example: `^{0,1}▷ [+c(X), -c(X), a] = [a]`.
    ///
    /// Self-interaction of `[+c(X), -c(X), a]` on rays 0 and 1.
    /// Solution: `{X =? X}` → identity. Remove rays 0,1. Result: `[a]`.
    #[test]
    fn self_interact_basic() {
        let star: Star = vec![
            pos_ray("c", vec![var("X")]),
            neg_ray("c", vec![var("X")]),
            c("a"),
        ];
        let result = self_interact(&star, 0, 1);
        assert!(result.is_some(), "self-interaction should succeed");
        let res = result.unwrap();
        // Should have one ray: c("a").
        assert_eq!(res.len(), 1);
        assert_eq!(res[0], c("a"));
    }

    /// Fusion: `[+f(X), a] ^{0,0}∇_α [-f(Y), b]` = `[a, b]` (with X↦Y or vice versa).
    #[test]
    fn fusion_basic() {
        let phi1: Star = vec![pos_ray("f", vec![var("X")]), c("a")];
        let phi2: Star = vec![neg_ray("f", vec![var("Y")]), c("b")];
        let result = fuse(&phi1, 0, &phi2, 0);
        assert!(result.is_some(), "fusion should succeed");
        let res = result.unwrap();
        // [a, b] (order may vary, but both should appear).
        assert_eq!(res.len(), 2);
    }

    /// mat_phi: the query star's -add ray matches the base and step stars of Φ⁺_N.
    #[test]
    fn mat_phi_horn() {
        let phi = add_prog();
        // query ray: -add(2̄, 2̄, R) — matches +add(0,Y,Y) (base) and +add(s(X),Y,s(Z)) (step).
        let r = neg_ray("add", vec![nat(2), nat(2), var("R")]);
        let matches = mat_phi(&phi, r);
        // Should match star 0 ray 0 (+add(0,Y,Y)) and star 1 ray 1 (+add(s(X),Y,s(Z))).
        assert!(!matches.is_empty(), "query ray should match something in Φ⁺_N");
        // At minimum must match the step rule.
        assert!(
            matches.contains(&(1, 1)),
            "query ray should match step rule at (1,1); got {:?}", matches
        );
    }
}
