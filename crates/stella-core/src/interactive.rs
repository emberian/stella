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
use crate::polarised::{matchable, matchable_fast, ray_polarity, underlying_term, Polarity};
use crate::subst::{freshen, Substitution};
use crate::term::{get, mk_app, mk_var_interned, Term, TermData, Var};
use crate::unify::{unify, Equation};
use crate::index::DiscIndex;
use crate::spec_phi::{spec_star, SelPhi, Transition as SpecTr};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::HashSet;

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

/// Collect a term's distinct variables into `seen` (a small linear-probe
/// `Vec`), assigning each first-seen var a fresh `Var::Idx` slot from
/// `counter`.  Φ stars carry only a handful of distinct vars, so a `Vec`
/// scan beats an `FxHashMap` *and* the doubled term-walk of `Substitution`.
fn collect_remap(t: Term, seen: &mut Vec<(Var, Var)>, counter: &mut u32) {
    match get(t) {
        TermData::Var(v) => {
            if !seen.iter().any(|&(o, _)| o == v) {
                let fresh = Var::Idx(*counter);
                *counter += 1;
                seen.push((v, fresh));
            }
        }
        TermData::App(_, args) => {
            for &a in args.iter() {
                collect_remap(a, seen, counter);
            }
        }
    }
}

/// Apply a small `Vec` var-remap to a term in one pass, rebuilding only the
/// spine that actually changed (hash-consing dedups the rest).
fn apply_remap(t: Term, map: &[(Var, Var)]) -> Term {
    match get(t) {
        TermData::Var(v) => match map.iter().find(|&&(o, _)| o == v) {
            Some(&(_, fresh)) => mk_var_interned(fresh),
            None => t,
        },
        TermData::App(sym, args) => {
            let mut changed = false;
            let new_args: Vec<Term> = args
                .iter()
                .map(|&a| {
                    let na = apply_remap(a, map);
                    changed |= na != a;
                    na
                })
                .collect();
            if changed {
                crate::term::mk_app_interned(sym, new_args)
            } else {
                t
            }
        }
    }
}

/// Rename all variables in a star with a given prefix, returning the renamed
/// star and substitution. Used for α-renaming before fusion (§49.30 ∇_α).
///
/// The freshening is **pure integer work**: each distinct source var of the Φ
/// star is mapped to a fresh canonical-index [`Var::Idx`] consuming one
/// `counter` slot — no `format!`, no `Var::intern` (no global `ThreadedRodeo`
/// lock), and no `Substitution` `FxHashMap` / doubled term-walk.  `Idx` is
/// disjoint from every `Named` var (Ψ is built from named/parsed vars) and
/// from `Idx`s of earlier generations, so the monotone `counter` reproduces
/// exactly the variable-disjointness the old `"{prefix}_{v}{counter}"` string
/// scheme guaranteed.  The returned `Substitution` (built cheaply from the
/// same small `Vec`) is consumed only by the cold `step_detail`/`render_theta`
/// path; the hot fusion path uses `alpha_rename_star_fast`.
fn alpha_rename_star(star: &Star, _prefix: &str, counter: &mut u32) -> (Star, Substitution) {
    let mut map: Vec<(Var, Var)> = Vec::new();
    for &r in star.iter() {
        collect_remap(r, &mut map, counter);
    }
    let renamed: Star = star.iter().map(|&r| apply_remap(r, &map)).collect();
    let subst = Substitution::from_var_pairs(
        map.iter().map(|&(o, f)| (o, mk_var_interned(f))),
    );
    (renamed, subst)
}

/// Hot-path freshening: identical `Var::Idx` assignment as
/// [`alpha_rename_star`] but **without** building/returning the
/// `Substitution` (the fast fusion path discards it).  Same `counter`
/// progression ⇒ byte-identical residual stars (N-KS gate).
fn alpha_rename_star_fast(star: &Star, counter: &mut u32) -> Star {
    let mut map: Vec<(Var, Var)> = Vec::new();
    for &r in star.iter() {
        collect_remap(r, &mut map, counter);
    }
    star.iter().map(|&r| apply_remap(r, &map)).collect()
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

/// Colour-aware matchable rays for a *configuration* `Φ ⊢ Ψ` (§51.6): the
/// colour set is `colours(Φ) ∪ colours(Ψ)`, exactly what `iex` uses. The
/// plain [`mat_phi`] uses no extra colours and so misses every match in a
/// coloured constellation (all the automata encodings) — UI step drivers
/// must use this, or coloured machines never fire.
pub fn mat_phi_colored(phi: &Constellation, psi: &[Star], r: Term) -> Vec<(usize, usize)> {
    let psi_c = all_colours(&psi.to_vec());
    mat_phi_c(phi, r, &psi_c)
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
// KS accelerator (spec docs/05 §8) — head-indexed `mat_Φ`, colours cached once.
//
// FAITHFULNESS: `mat_phi_c_accel` returns the **identical** `Vec<(i,j)>` as the
// reference `mat_phi_c` (same set, same order). Justification:
//  * `DiscIndex::build(phi, all_colours(phi))` keeps *every* App ray of Φ
//    (same ray set / key / `id_rays` order as `RayIndex::build` — it is a
//    pure refinement of the head bucket) — each Φ-ray's own colours ⊆
//    all_colours(phi) trivially, so the build-time colour filter never
//    drops a Φ ray.
//  * `DiscIndex::for_each_candidate` visits a **superset** of the
//    `partner_key`-bucket rays that are `matchable` with the query (the
//    discrimination tree only rejects rays *provably* non-unifiable by
//    first-order term structure — variables never prune; fuzz-proven
//    `disc_superset_of_matchable_fuzz` + the N-KS gate). So every
//    `mat_phi_c` match is still visited; the per-candidate `matchable_fast`
//    (unchanged) remains the sole decider — same match set.
//  * The exact same per-ray filters (neutral skip, `cr ⊆ c_set`,
//    `crj ⊆ c_set`, `matchable`) are re-applied here; `sort_unstable`
//    restores the canonical (i,j) order regardless of trie visit order.
// The reference engine (`iex`/`mat_phi_c`/`interaction_step`) is left UNTOUCHED
// as the differential oracle (spec §8 N-KS): see `iex_fast` equivalence tests.
// ─────────────────────────────────────────────────────────────────────────────

/// Colour of a ray as an interned `Sym` (the allocation-free equivalent of
/// `ray_colours`: `ray_colours(r)` is `∅` for Var/Neutral and the singleton
/// `{display_name(head)}` otherwise — `Sym = (name,pol)` is a bijection with
/// that display-name, so `Some(sym)` ≡ that singleton, `None` ≡ `∅`).
fn ray_csym(r: Term) -> Option<crate::term::Sym> {
    match get(r) {
        TermData::App(sym, _) if sym.pol != Polarity::Neutral => Some(sym),
        _ => None,
    }
}

/// Accelerator built once per run from the (fixed) reference constellation Φ.
///
/// `phi_csyms` is `all_colours(phi)` as an interned-`Sym` set (bijective with
/// the `String` display-names) — built once, queried `O(1)`, zero allocation.
pub struct IexAccel {
    /// Discrimination (substitution) tree over Φ's pattern rays
    /// (perf #4 / strategic-map C-#1). Replaces the head/colour
    /// [`RayIndex`] in the per-step candidate scan: it sub-divides each
    /// already-correct `partner_key` head bucket by first-order argument
    /// structure, so a resolvable head yields ≈1 candidate instead of the
    /// whole δ-bucket. Faithful by construction — the visited set is a
    /// **superset** of the matchable set (`index.rs` module gate +
    /// `disc_superset_of_matchable_fuzz`); `matchable_fast` stays the sole
    /// decider. `RayIndex` remains in `index.rs` as the oracle reference
    /// (`DepGraph::build_indexed`, oracle-equiv tests).
    idx: DiscIndex,
    phi_csyms: FxHashSet<crate::term::Sym>,
    /// Σ(Φ) residual, parallel to `phi` by star index: the precomputed
    /// closed [`SpecTr`] + its negative-ray index for each specialisable
    /// Φ-star (`None` ⇒ not specialisable ⇒ generic path). Built once per
    /// fixed Φ (the partial-evaluation residual); consulted **only** by the
    /// `iex_spec` tier — `iex_fast`/`iex_tabled`/reference `iex` never read
    /// it, so their proven byte-identity is untouched.
    spec: Vec<Option<(usize, SpecTr)>>,
    /// Σ(Φ) **selection**-side residual (thesis-audit 04 §2). The closed,
    /// per-Φ table of focus heads whose redex-existence is provable in O(1)
    /// without the generic `-P`-bucket `matchable_fast` scan. A pure function
    /// of Φ; consulted **only** by the `iex_spec` selection loop as a sound
    /// positive short-circuit (`SelPhi::decide`) — `iex_fast`/`iex_tabled`/
    /// reference `iex` never read it ⇒ their byte-identity is untouched.
    sel: SelPhi,
}

impl IexAccel {
    pub fn build(phi: &Constellation) -> Self {
        let phi_colours = all_colours(phi);
        // c = all_colours(phi) ⇒ every App ray of Φ is retained (its own
        // colours ⊆ all_colours(phi) by construction).
        let idx = DiscIndex::build(phi, &phi_colours);
        let mut phi_csyms = FxHashSet::default();
        for star in phi {
            for &ray in star {
                if let Some(s) = ray_csym(ray) {
                    phi_csyms.insert(s);
                }
            }
        }
        let spec = phi.iter().map(|s| spec_star(s)).collect();
        let sel = SelPhi::build(phi);
        Self { idx, phi_csyms, spec, sel }
    }
}

/// Indexed, allocation-free `mat_Φ^C(r)` — provably identical output to
/// [`mat_phi_c`].
///
/// Faithfulness vs the reference predicate:
///  * `cr ⊆ c_set`: `cr` is `∅` (→ trivially true) or the singleton
///    `{ray_csym(r)}`; membership in `c_set = all_colours(phi) ∪ extra_c` is
///    the `O(1)` check `s ∈ phi_csyms ∪ psi_csyms` (Sym↔display-name bijection).
///  * `crj ⊆ c_set`: **always true** for any indexed Φ ray — its colours ⊆
///    `all_colours(phi)` ⊆ `c_set` by construction — so the per-candidate
///    check is provably redundant and dropped (removing a per-candidate
///    `ray_colours` allocation). Same match set, same (i,j) order.
fn mat_phi_c_accel(
    accel: &IexAccel,
    phi: &Constellation,
    r: Term,
    psi_csyms: &FxHashSet<crate::term::Sym>,
) -> Vec<(usize, usize)> {
    // cr ⊆ c_set
    if let Some(s) = ray_csym(r) {
        if !accel.phi_csyms.contains(&s) && !psi_csyms.contains(&s) {
            return Vec::new();
        }
    }
    let (name, pol) = match get(r) {
        TermData::App(sym, _) => (sym.name, sym.pol),
        _ => return Vec::new(),
    };
    let mut result: Vec<(usize, usize)> = Vec::new();
    // Disc-tree visits a SUPERSET of the matchable `partner_key`-bucket
    // rays (index.rs gate); `fp_unifiable`+`matchable_fast` stay the sole
    // decider, so the accepted set is identical to the old full-bucket
    // scan. `sort_unstable` restores canonical (i,j) order regardless of
    // trie visit order.
    accel.idx.for_each_candidate(name, pol, r, |(i, j)| {
        let ray = phi[i][j];
        if ray_polarity(ray) == Polarity::Neutral {
            return;
        }
        if fp_unifiable(r, ray) && matchable_fast(r, ray) {
            result.push((i, j));
        }
    });
    result.sort_unstable();
    result
}

/// Existence-only variant of [`mat_phi_c_accel`]: returns `true` iff the match
/// list would be non-empty. Early-exits on the first matchable candidate — no
/// `Vec` allocation, no sort. Faithful: `any_match_accel(..)` ≡
/// `!mat_phi_c_accel(..).is_empty()` by construction (same colour gate, same
/// candidate set, same `matchable` test). Used by the per-step *selection*
/// scan (which only needs existence); full enumeration stays in
/// [`mat_phi_c_accel`] for the chosen redex.
fn any_match_accel(
    accel: &IexAccel,
    phi: &Constellation,
    r: Term,
    psi_csyms: &FxHashSet<crate::term::Sym>,
) -> bool {
    if let Some(s) = ray_csym(r) {
        if !accel.phi_csyms.contains(&s) && !psi_csyms.contains(&s) {
            return false;
        }
    }
    let (name, pol) = match get(r) {
        TermData::App(sym, _) => (sym.name, sym.pol),
        _ => return false,
    };
    // Existence-only: stop deciding once a match is found. The disc-tree
    // visits a SUPERSET of the matchable bucket rays (index.rs gate), so
    // `found` becomes true on exactly the same condition as the old
    // full-bucket early-exit scan — same boolean, fewer `matchable_fast`
    // calls. (`for_each_candidate` keeps visiting after `found`, but the
    // residual visits are a cheap `Polarity`/branch — no `matchable_fast`,
    // no `T_MATCH` time — so the measured matchable phase still shrinks.)
    let mut found = false;
    accel.idx.for_each_candidate(name, pol, r, |(i, j)| {
        if found {
            return;
        }
        let ray = phi[i][j];
        if ray_polarity(ray) == Polarity::Neutral {
            return;
        }
        let tm = std::time::Instant::now();
        let m = fp_unifiable(r, ray) && matchable_fast(r, ray);
        ks_add(&T_MATCH, tm.elapsed());
        if m {
            found = true;
        }
    });
    found
}

/// Sound one-level argument-discrimination pre-filter for `matchable`.
///
/// Returns `false` **only** when `r` and `s` are *provably* non-unifiable
/// (different arity, or some argument position holds two distinct ground
/// functors — variables are never rejected). Therefore
/// `fp_unifiable(r,s) == false  ⇒  matchable(r,s) == false`, so gating
/// `fp_unifiable(..) && matchable(..)` is **identical** to `matchable(..)`
/// (N-KS byte-faithful) while skipping full α-unification on the candidates
/// it rejects — the proven 95%-of-`find` hotspot.
#[inline]
fn fp_unifiable(r: Term, s: Term) -> bool {
    match (get(r), get(s)) {
        (TermData::App(_, ar), TermData::App(_, br)) => {
            if ar.len() != br.len() {
                return false;
            }
            for (&a, &b) in ar.iter().zip(br.iter()) {
                if let (TermData::App(fa, _), TermData::App(fb, _)) = (get(a), get(b)) {
                    if fa.name != fb.name {
                        return false; // two distinct ground functors — unfixable
                    }
                }
            }
            true
        }
        _ => true, // rays are App; be conservative (never wrongly reject)
    }
}

/// Existence-only self-interaction check — early-exit analogue of
/// `!mat_self(star, j).is_empty()` (no `Vec`).
fn any_self(star: &Star, j: usize) -> bool {
    let r = star[j];
    star.iter()
        .enumerate()
        .any(|(jk, &ray)| jk != j && matchable_fast(r, ray))
}

/// Ψ colours as an interned-`Sym` set (allocation-free analogue of
/// `all_colours(&psi)`), computed **once per step**.
fn psi_csyms(psi: &[Star]) -> FxHashSet<crate::term::Sym> {
    let mut s = FxHashSet::default();
    for star in psi {
        for &ray in star {
            if let Some(c) = ray_csym(ray) {
                s.insert(c);
            }
        }
    }
    s
}

/// Incrementally-maintained analogue of [`psi_csyms`] — WIN 1
/// (docs/explore/perf-audit.md §3): `iex_fast_inner` used to call
/// `psi_csyms(&psi)` every step, an `O(|Ψ|)` rebuild over a *growing* Ψ ⇒
/// `O(steps·|Ψ|)` ≈ quadratic (the largest single phase measured anywhere:
/// binarith `add 999999 888888`, psics = 0.3204 s = 81 % of `iex_fast`
/// wall). The colour set changes by tiny per-step deltas only: one star is
/// `remove`d and a few `produced` stars are appended. So we keep a **colour
/// multiset** — `counts[c]` = number of *ray occurrences* in Ψ whose
/// `ray_csym` is `c` — and a derived `set` of the keys with `counts > 0`.
///
/// Multiset (not a plain set) is load-bearing: a star removal can drop the
/// *last* bearer of a colour (the audit's explicit colour-*shrinking* hazard,
/// §WIN1 "Faithfulness"). A union-only set would keep that colour forever and
/// silently change the colour gate; the count makes the disappearance exact.
///
/// Faithfulness: `set` is, element-for-element, exactly
/// `psi_csyms(&psi)` after each delta — it is a pure reindexing of the same
/// per-ray `ray_csym` fold, just amortised. The debug-gated invariant
/// [`PsiCS::assert_eq_full`] proves this by oracle every step (see
/// `iex_fast_inner`). The consumer is the colour-subset gate
/// `mat_phi_c_accel`/`any_match_accel`, already proven identical to reference
/// `mat_phi_c`; identical set in ⇒ byte-identical redex selection out.
struct PsiCS {
    counts: FxHashMap<crate::term::Sym, u32>,
    set: FxHashSet<crate::term::Sym>,
}

impl PsiCS {
    /// Seed from the initial Ψ (one `O(|Ψ_init|)` fold — paid once, not per step).
    fn from_psi(psi: &[Star]) -> Self {
        let mut me = PsiCS {
            counts: FxHashMap::default(),
            set: FxHashSet::default(),
        };
        for star in psi {
            me.add_star(star);
        }
        me
    }

    /// Account every coloured ray of `star` (+1 each occurrence; key enters
    /// `set` on its 0→1 transition).
    fn add_star(&mut self, star: &Star) {
        for &ray in star {
            if let Some(c) = ray_csym(ray) {
                let n = self.counts.entry(c).or_insert(0);
                *n += 1;
                if *n == 1 {
                    self.set.insert(c);
                }
            }
        }
    }

    /// Un-account every coloured ray of `star` (−1 each occurrence; key
    /// leaves `set` *exactly* when its count reaches 0 — this is the
    /// colour-shrinking correctness point). `debug_assert`s guard against an
    /// underflow that would mean the delta diverged from Ψ.
    fn remove_star(&mut self, star: &Star) {
        for &ray in star {
            if let Some(c) = ray_csym(ray) {
                match self.counts.get_mut(&c) {
                    Some(n) => {
                        debug_assert!(*n > 0, "PsiCS: count underflow for a colour");
                        *n -= 1;
                        if *n == 0 {
                            self.counts.remove(&c);
                            self.set.remove(&c);
                        }
                    }
                    None => debug_assert!(false, "PsiCS: removing an unaccounted colour"),
                }
            }
        }
    }

    /// The set view consumed by the colour gate (== `psi_csyms(&psi)`).
    fn set(&self) -> &FxHashSet<crate::term::Sym> {
        &self.set
    }

    /// Debug-only faithfulness oracle: the incremental `set` MUST equal the
    /// full rebuild `psi_csyms(psi)` on *every* step. Compiled out of release
    /// (`debug_assertions`), exercised by the test corpora so byte-identity
    /// is *proven*, not argued (task gate #2).
    #[inline]
    fn assert_eq_full(&self, psi: &[Star]) {
        if cfg!(debug_assertions) {
            let full = psi_csyms(psi);
            debug_assert!(
                self.set == full,
                "PsiCS divergence: incremental != psi_csyms full rebuild \
                 (incremental={:?}, full={:?})",
                self.set,
                full
            );
        }
    }
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
    fuse_theta(phi1, j, phi2_renamed, j_prime).map(|(s, _)| s)
}

/// The unifier strategy: a function pointer with the shared
/// `Vec<Equation> -> Option<Substitution>` signature. `unify` (reference,
/// the spec oracle) for every `iex`/`step_at`/diagnostic path;
/// `unify_fast` (near-linear, result-equivalent — `unify_fast.rs`) ONLY for
/// the accelerated `produce_stars_fast` path. Statically un-contaminable:
/// the reference functions hard-code `unify` (docs/09 §C).
type Solve = fn(Vec<Equation>) -> Option<Substitution>;

/// Fusion that also returns the **exact** unifier `θ` it applied — the
/// authoritative MGU of this summand (no post-hoc reconstruction).
/// `solve` selects the unifier (see [`Solve`]); the rest is identical for
/// reference and fast — only the MGU shape differs (α-equal), which
/// `faithfulness::psi_compatible` tolerates and the old byte-identity gate
/// could not.
fn fuse_theta_with(
    phi1: &Star,
    j: usize,
    phi2_renamed: &Star,
    j_prime: usize,
    solve: Solve,
) -> Option<(Star, Substitution)> {
    let r1 = underlying_term(phi1[j]);
    let r2 = underlying_term(phi2_renamed[j_prime]);
    let tun = std::time::Instant::now();
    let theta = solve(vec![Equation::new(r1, r2)]);
    ks_add(&T_UNIFY, tun.elapsed());
    let theta = theta?;

    let tsb = std::time::Instant::now();
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
    ks_add(&T_SUBST, tsb.elapsed());
    Some((result, theta))
}

/// Reference fusion-with-θ — the spec-oracle unifier. Every `iex`/`step_at`/
/// diagnostic caller uses this; byte-for-byte unchanged.
fn fuse_theta(
    phi1: &Star,
    j: usize,
    phi2_renamed: &Star,
    j_prime: usize,
) -> Option<(Star, Substitution)> {
    fuse_theta_with(phi1, j, phi2_renamed, j_prime, unify)
}

/// Accelerated fusion-with-θ — near-linear `unify_fast`. ONLY reached from
/// `produce_stars_fast` (the `iex_fast`/`iex_tabled` tier). Result-equivalent
/// to `fuse_theta` under the same `Compatible` (MGU α-equal); gated by
/// `faithfulness::psi_compatible` + reference `iex`.
fn fuse_theta_fast(
    phi1: &Star,
    j: usize,
    phi2_renamed: &Star,
    j_prime: usize,
) -> Option<(Star, Substitution)> {
    fuse_theta_with(phi1, j, phi2_renamed, j_prime, crate::unify_fast::unify_fast)
}

fn fuse_fast(phi1: &Star, j: usize, phi2_renamed: &Star, j_prime: usize) -> Option<Star> {
    fuse_theta_fast(phi1, j, phi2_renamed, j_prime).map(|(s, _)| s)
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
    self_interact_theta(star, j, j_prime).map(|(s, _)| s)
}

/// Self-interaction that also returns the exact `θ` it applied. `solve`
/// selects the unifier ([`Solve`]); reference vs fast differ only in MGU
/// shape (α-equal).
fn self_interact_theta_with(
    star: &Star,
    j: usize,
    j_prime: usize,
    solve: Solve,
) -> Option<(Star, Substitution)> {
    let r1 = underlying_term(star[j]);
    let r2 = underlying_term(star[j_prime]);
    let theta = solve(vec![Equation::new(r1, r2)])?;

    let result: Star = star
        .iter()
        .enumerate()
        .filter(|&(idx, _)| idx != j && idx != j_prime)
        .map(|(_, &r)| theta.apply(r))
        .collect();
    Some((result, theta))
}

/// Reference self-interaction-with-θ (spec-oracle unifier). Unchanged for
/// every `iex`/`step_at`/diagnostic caller.
fn self_interact_theta(star: &Star, j: usize, j_prime: usize) -> Option<(Star, Substitution)> {
    self_interact_theta_with(star, j, j_prime, unify)
}

/// Accelerated self-interaction-with-θ — `unify_fast`, ONLY from
/// `produce_stars_fast`.
fn self_interact_fast(star: &Star, j: usize, j_prime: usize) -> Option<Star> {
    self_interact_theta_with(star, j, j_prime, crate::unify_fast::unify_fast).map(|(s, _)| s)
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
// Exact step detail (§51.9) — the authoritative decomposition of one step.
// ─────────────────────────────────────────────────────────────────────────────

/// Render θ as `(variable, term)` pairs. When `alpha_inv` is given (the
/// inverse of the α-renaming applied to the Φ star before fusion), the
/// bindings are converted back into Φ's *own* variable names — so a
/// logician sees `W ↦ cons(0,…)`, exactly as on paper, not the engine's
/// internal `ext0_…W…` scaffolding. Still the same unifier, α-converted.
fn render_theta(theta: &Substitution, alpha_inv: Option<&Substitution>) -> Vec<(String, String)> {
    let key_name = |v: Var| -> String {
        if let Some(inv) = alpha_inv {
            if let Some(&t) = inv.0.get(&v) {
                if let TermData::Var(orig) = get(t) {
                    return orig.as_str().to_string();
                }
            }
        }
        v.as_str().to_string()
    };
    let val_str = |t: Term| -> String {
        match alpha_inv {
            Some(inv) => format!("{}", inv.apply(t)),
            None => format!("{t}"),
        }
    };
    let mut v: Vec<(String, String)> = theta
        .0
        .iter()
        .map(|(&var, &t)| (key_name(var), val_str(t)))
        .collect();
    v.sort();
    v
}

/// Invert an α-renaming `Substitution` (origVar → freshVar-term) into
/// (freshVar → origVar-term), for converting θ back to readable names.
fn invert_alpha(alpha: &Substitution) -> Substitution {
    let pairs: Vec<(Var, Term)> = alpha
        .0
        .iter()
        .filter_map(|(&orig, &t)| match get(t) {
            TermData::Var(fresh) => Some((fresh, mk_var_interned(orig))),
            _ => None,
        })
        .collect();
    Substitution::from_var_pairs(pairs)
}

/// One summand of a §51.9 interaction step: a fusion against a specific
/// `Φ[iₖ][jₖ]` (external) or a self-interaction within the star, together
/// with the **exact** unifier `θ` the engine applied and the star produced.
#[derive(Debug, Clone)]
pub struct Summand {
    /// `true` = external fusion against Φ; `false` = self-interaction.
    pub external: bool,
    /// For external: `Some((iₖ, jₖ))` the Φ ray fused against.
    pub phi_target: Option<(usize, usize)>,
    /// For self: `Some(jₖ)` the other ray in the star.
    pub self_ray: Option<usize>,
    /// The MGU actually applied (engine-authoritative, not reconstructed),
    /// as `(variable, term)` display pairs.
    pub theta: Vec<(String, String)>,
    /// The resulting star (this summand's contribution to Ψ').
    pub result: Star,
}

/// The full, exact decomposition of one IEx step at the chosen ray `Ψ[i][j]`:
/// the §51.9 *sum* of summands (each with its real θ) and the successor Ψ.
/// `psi_after` is identical to what `interaction_step`/`iex` would produce,
/// so a UI built on this is faithful, not an approximation.
#[derive(Debug, Clone)]
pub struct StepDetail {
    pub star: usize,
    pub ray: usize,
    pub summands: Vec<Summand>,
    pub psi_after: Vec<Star>,
}

/// Apply one IEx step at the explicitly chosen ray `Ψ[star_idx][ray_idx]`
/// and return its exact decomposition (every summand's real θ) plus the
/// successor interaction space. `counter` must persist across a run so
/// freshly-renamed Φ variables never collide (same scheme as `iex`).
///
/// Returns `None` if `(i, j)` is out of range, neutral, or not a redex.
pub fn step_detail(
    phi: &Constellation,
    psi: &[Star],
    star_idx: usize,
    ray_idx: usize,
    counter: &mut u32,
) -> Option<StepDetail> {
    let selected_star = psi.get(star_idx)?.clone();
    let r = *selected_star.get(ray_idx)?;
    if ray_polarity(r) == Polarity::Neutral {
        return None;
    }
    let psi_colours = all_colours(&psi.to_vec());

    let mut psi_prime: Vec<Star> = psi
        .iter()
        .enumerate()
        .filter(|(idx, _)| *idx != star_idx)
        .map(|(_, s)| s.clone())
        .collect();
    let mut summands: Vec<Summand> = Vec::new();

    // First sum: external fusions (same order/counter scheme as interaction_step).
    let ext_matches = mat_phi_c(phi, r, &psi_colours);
    for (ik, jk) in ext_matches {
        let (phi_star_renamed, alpha) = {
            let prefix = format!("ext{ik}_{counter}");
            *counter += 1;
            alpha_rename_star(&phi[ik], &prefix, counter)
        };
        if let Some((fused, theta)) =
            fuse_theta(&selected_star, ray_idx, &phi_star_renamed, jk)
        {
            let alpha_inv = invert_alpha(&alpha);
            summands.push(Summand {
                external: true,
                phi_target: Some((ik, jk)),
                self_ray: None,
                theta: render_theta(&theta, Some(&alpha_inv)),
                result: fused.clone(),
            });
            psi_prime.push(fused);
        }
    }

    // Second sum: self-interactions within Ψ[i].
    for jk in mat_self(&selected_star, ray_idx) {
        if let Some((si, theta)) = self_interact_theta(&selected_star, ray_idx, jk) {
            summands.push(Summand {
                external: false,
                phi_target: None,
                self_ray: Some(jk),
                theta: render_theta(&theta, None),
                result: si.clone(),
            });
            psi_prime.push(si);
        }
    }

    if summands.is_empty() {
        return None;
    }
    Some(StepDetail {
        star: star_idx,
        ray: ray_idx,
        summands,
        psi_after: psi_prime,
    })
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

// ─────────────────────────────────────────────────────────────────────────────
// KS phase profiler — env-gated (`STELLA_KS_PROF=1`), zero overhead when off
// (one relaxed bool load per phase). Diagnostic only; never changes results.
// ─────────────────────────────────────────────────────────────────────────────

static KS_PROF: std::sync::LazyLock<bool> =
    std::sync::LazyLock::new(|| std::env::var("STELLA_KS_PROF").as_deref() == Ok("1"));

thread_local! {
    static T_PSICS: std::cell::Cell<f64> = const { std::cell::Cell::new(0.0) };
    static T_FIND: std::cell::Cell<f64> = const { std::cell::Cell::new(0.0) };
    static T_MATCH: std::cell::Cell<f64> = const { std::cell::Cell::new(0.0) };
    static T_FRESH: std::cell::Cell<f64> = const { std::cell::Cell::new(0.0) };
    static T_FUSE: std::cell::Cell<f64> = const { std::cell::Cell::new(0.0) };
    // Sub-split of T_FUSE to find the real per-fuse cost (unify vs subst).
    static T_UNIFY: std::cell::Cell<f64> = const { std::cell::Cell::new(0.0) };
    static T_SUBST: std::cell::Cell<f64> = const { std::cell::Cell::new(0.0) };
    /// docs/16 §3.2 / docs/12 §C.2 H1 tap — redex-FAMILY duplication probe.
    /// **Pure observation, behaviour-preserving.** At every committed
    /// resolution step `iex_fast_inner` pushes `(head_sym, canonical_redex)`
    /// of the *selected* redex here *iff a measurement harness installed a
    /// sink* (`h1_tap_begin`). The pair is `(spine_head(focus), canonical of
    /// the whole selected star)`: the head names the resolvable rule (the
    /// harness classifies it Splice `s/b/c/…` vs Delta `:N` vs other against
    /// Φ); the canonical `TermId` is the α-equivalence key for the
    /// distinct-vs-duplicated redex-family count. Production and the test
    /// suite never install one ⇒ `None` ⇒ a single branch, byte-identical to
    /// the un-instrumented `iex_fast`. The reference `iex` path is untouched.
    static H1_TAP: std::cell::RefCell<Option<H1Sink>> =
        const { std::cell::RefCell::new(None) };
}

/// H1 redex-family tap sink: a capped log of `(resolved-head,
/// α-canonical-redex)` pairs. The `cap` keeps the harness self-bounding —
/// recording becomes a cheap no-op once `cap` redexes are seen, so the
/// measurement is over a *bounded prefix* of the reduction (the H1
/// duplicated/distinct ratio is a property of that prefix at increasing
/// depth — exactly the docs/16 §3.2 metric — and does not require running
/// the divergent `data[0]` reduction to completion).
pub struct H1Sink {
    log: Vec<(crate::term::SymName, crate::term::TermId)>,
    cap: usize,
}

/// Install a fresh H1 redex-family tap sink (docs/16 §3.2), capped at `cap`
/// recorded redexes (after which recording is a cheap no-op — the harness's
/// self-bounding mechanism). Measurement harnesses only — see [`H1_TAP`].
/// The reference/`iex_fast`/production paths never call this ⇒ the tap
/// stays `None` ⇒ behaviour-identical.
pub fn h1_tap_begin(cap: usize) {
    H1_TAP.with(|t| {
        *t.borrow_mut() = Some(H1Sink {
            log: Vec::new(),
            cap,
        })
    });
}
/// Take the accumulated `(resolved-head, canonical-redex)` log (in
/// resolution order, truncated at the cap) and clear the sink.
pub fn h1_tap_take() -> Vec<(crate::term::SymName, crate::term::TermId)> {
    H1_TAP.with(|t| t.borrow_mut().take().map(|s| s.log).unwrap_or_default())
}
/// Has the installed sink reached its cap? (`false` if no sink.) Lets a
/// harness stop a rung's `eval_forced` early once enough redexes are
/// observed — keeping each rung wall-bounded without touching the engine.
pub fn h1_tap_capped() -> bool {
    H1_TAP.with(|t| {
        t.borrow()
            .as_ref()
            .map(|s| s.log.len() >= s.cap)
            .unwrap_or(false)
    })
}

/// `M` inside a `±P(st(M, π))` ray, then its KAM spine head atom (the
/// resolvable head — exactly `galaxy::spine_head`'s leftmost atom). Pure
/// read; used only by the H1 tap. `None` if the ray is not a process ray
/// or the focus has no atom head (a var/strict shape).
fn h1_resolved_head(ray: crate::term::TermId) -> Option<crate::term::SymName> {
    use crate::term::{get, TermData};
    let TermData::App(p, pa) = get(ray) else { return None };
    if p.name.as_str() != "P" || pa.len() != 1 {
        return None;
    }
    let TermData::App(s2, sa) = get(pa[0]) else { return None };
    if s2.name.as_str() != "st" || sa.len() != 2 {
        return None;
    }
    // Leftmost spine atom of the focus `M` (KAM head; mirrors
    // `galaxy::spine_head` exactly — `a(_,_)` left-descent to an atom).
    let mut t = sa[0];
    loop {
        match get(t) {
            TermData::App(s, args) if s.name.as_str() == "a" && args.len() == 2 => t = args[0],
            TermData::App(s, args) if args.is_empty() => return Some(s.name),
            _ => return None,
        }
    }
}

#[inline(always)]
fn ks_add(slot: &'static std::thread::LocalKey<std::cell::Cell<f64>>, dt: std::time::Duration) {
    if *KS_PROF {
        slot.with(|c| c.set(c.get() + dt.as_secs_f64()));
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// KS fast path — `iex_fast` (spec §8). Byte-for-byte mirror of `iex`/
// `interaction_step`/`is_normal_form` with `mat_phi_c` → `mat_phi_c_accel`
// (provably identical output). The reference path above is the differential
// oracle; `iex_eq_iex_fast` (tests) is the N-KS gate.
// ─────────────────────────────────────────────────────────────────────────────

/// Produce **only the new stars** from one interaction step on `selected_star`
/// at `ray_idx` (ext fusions in `mat_phi_c_accel` order, then
/// self-interactions). The caller mutates Ψ in place — order-preserving
/// `remove(star_idx)` + `extend(produced)` — so there is no per-step
/// `Vec<Star>` realloc. Same Ψ as the reference's filter-collect+push.
/// Σ(Φ) in-loop realiser — the closed [`SpecTr`] applied to *iex_fast's
/// own* chosen redex `(selected_star, ray_idx)` against the matched Φ-star
/// `phi_star` (negative pattern ray `neg_idx`). Returns the SAME resolvent
/// the generic α-rename + `unify_fast` + θ-apply would build for this
/// `(ik,jk)` — but with no α-rename / no general unify / no whole-star
/// apply (the Futamura residual). Result-equivalent on the δ/Push skeleton:
/// the Φ pattern is linear in fresh-equiv vars ⇒ its MGU is the one-sided
/// match read positionally off the Ψ focus; the generic path α-renames Φ so
/// its θ is identity on the Ψ remainder ⇒ those rays pass through verbatim
/// (up to the α-naming of fresh vars, which `psi_compatible`'s canonical
/// form absorbs — the sibling-tier gate, exactly like `iex_tabled`).
/// `None` ⇒ delegate (Σ1 Splice, contractum-side match, or any shape
/// mismatch — `psi_compatible` + reference `iex` are the backstop).
#[cfg(test)]
pub(crate) static SPEC_HITS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

/// `±P(st(M, π))` → `(pol_sym, st_sym, M, π)`, structurally (the same
/// polarity-agnostic shape `spec_phi::unwrap_st` classifies on — head is the
/// bare polarity symbol `P`/`+P`/`-P`, **not** stripped by
/// `underlying_term`). `None` if not that shape.
fn split_pol_st(
    ray: crate::term::TermId,
) -> Option<(
    crate::term::Sym,
    crate::term::Sym,
    crate::term::TermId,
    crate::term::TermId,
)> {
    let TermData::App(pol, a) = get(ray) else {
        return None;
    };
    if a.len() != 1 {
        return None;
    }
    let TermData::App(sts, sa) = get(a[0]) else {
        return None;
    };
    if sts.name.as_str() != "st" || sa.len() != 2 {
        return None;
    }
    Some((pol, sts, sa[0], sa[1]))
}

fn spec_realise(
    selected_star: &Star,
    ray_idx: usize,
    phi_star: &Star,
    neg_idx: usize,
    tr: &SpecTr,
) -> Option<Star> {
    if phi_star.len() != 2 {
        return None;
    }
    let contractum_ray = phi_star[1 - neg_idx];
    let r = selected_star[ray_idx];
    let (_pol_r, st_sym, focus_m, focus_pi) = split_pol_st(r)?;
    // The contractum ray's polarity head (e.g. `+P`) + its stack slot — reuse
    // them verbatim so the minted ray is shape-identical to the generic
    // resolvent, and read the `·` Sym structurally (no name literal).
    let (pos_sym, c_st_sym, _c_m, c_pi) = split_pol_st(contractum_ray)?;

    let new_inner = match tr {
        // -P(st(:N,π)), +P(st(body,π)) ; θ = {π ↦ focus_pi} ; body closed.
        SpecTr::Delta(body) => mk_app(c_st_sym, vec![*body, focus_pi]),
        // -P(st(a(M,N),π)), +P(st(M, N·π)). Read M,N off the focus app; the
        // `·` Sym is the head of the contractum's stack slot.
        SpecTr::Unwind => {
            let TermData::App(a_sym, a_args) = get(focus_m) else {
                return None;
            };
            if a_sym.name.as_str() != "a" || a_args.len() != 2 {
                return None;
            }
            let (am, an) = (a_args[0], a_args[1]);
            let TermData::App(dot_sym, _) = get(c_pi) else {
                return None;
            };
            let _ = st_sym;
            mk_app(c_st_sym, vec![am, mk_app(dot_sym, vec![an, focus_pi])])
        }
        // Σ2: combinator/lazy-prim Splice. -P(st(H, p1·…·pk·π)),
        // +P(st(body,π)). Pop k `dot`-frames off the focus stack, bind them
        // positionally into the fixed contractum `body` (the closed Σ(Φ)
        // template), continue on the residual stack. θ = {p_i↦f_i} is the
        // literal MGU of the linear pattern ⇒ structurally = the generic
        // α-rename+unify+apply (the Σ1 α-gate is the backstop). Strict ops
        // carry no SpecTr at all (they delegate, unchanged).
        SpecTr::Splice { params, body } => {
            let k = params.len();
            let mut frames: Vec<crate::term::TermId> = Vec::with_capacity(k);
            let mut cur = focus_pi;
            for _ in 0..k {
                let TermData::App(d, da) = get(cur) else {
                    return None;
                };
                if d.name.as_str() != "dot" || da.len() != 2 {
                    return None;
                }
                frames.push(da[0]);
                cur = da[1];
            }
            let rest_pi = cur;
            let theta = Substitution::from_var_pairs(params.iter().copied().zip(frames));
            mk_app(c_st_sym, vec![theta.apply(*body), rest_pi])
        }
    };
    let new_ray = mk_app(pos_sym, vec![new_inner]);

    let mut result: Star = Vec::with_capacity(selected_star.len());
    for (idx, &ray) in selected_star.iter().enumerate() {
        if idx != ray_idx {
            result.push(ray);
        }
    }
    result.push(new_ray);
    #[cfg(test)]
    SPEC_HITS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    Some(result)
}

fn produce_stars_fast(
    accel: &IexAccel,
    phi: &Constellation,
    selected_star: &Star,
    ray_idx: usize,
    counter: &mut u32,
    psi_cs: &FxHashSet<crate::term::Sym>,
    spec: bool,
) -> Vec<Star> {
    let mut produced: Vec<Star> = Vec::new();
    let r = selected_star[ray_idx];

    for (ik, jk) in mat_phi_c_accel(accel, phi, r, psi_cs) {
        // Reference parity: the old scheme consumed one `counter` slot for
        // the (now-unused) per-fusion prefix before the per-var slots. Keep
        // it on BOTH paths so the generic fast path's `Var::Idx` numbering
        // stays byte-identical to the reference engine's (N-KS gate).
        *counter += 1;
        // Σ(Φ) tier: at iex_fast's OWN chosen `(ik,jk)`, if Φ-star `ik` is
        // specialisable and the Ψ focus matched its pattern ray, realise the
        // resolvent from the closed Transition instead of α-rename+unify+
        // apply. iex_fast/iex_tabled/iex pass `spec=false` ⇒ untouched.
        if spec {
            if let Some((neg_idx, tr)) = &accel.spec[ik] {
                if jk == *neg_idx {
                    if let Some(res) =
                        spec_realise(selected_star, ray_idx, &phi[ik], *neg_idx, tr)
                    {
                        produced.push(res);
                        continue;
                    }
                }
            }
        }
        let tf = std::time::Instant::now();
        let phi_star_renamed = alpha_rename_star_fast(&phi[ik], counter);
        ks_add(&T_FRESH, tf.elapsed());
        let tu = std::time::Instant::now();
        // Fast tier (iex_fast/iex_tabled): the near-linear unifier. The
        // reference iex path keeps `fuse`/`unify` — this is the entire
        // accelerated-vs-reference seam (docs/09 §C, exactly 2 call sites).
        let fused = fuse_fast(selected_star, ray_idx, &phi_star_renamed, jk);
        ks_add(&T_FUSE, tu.elapsed());
        if let Some(fused) = fused {
            produced.push(fused);
        }
    }

    for jk in mat_self(selected_star, ray_idx) {
        if let Some(si) = self_interact_fast(selected_star, ray_idx, jk) {
            produced.push(si);
        }
    }

    produced
}

fn is_normal_form_accel(accel: &IexAccel, phi: &Constellation, psi: &[Star]) -> bool {
    let psi_cs = psi_csyms(psi);
    for star in psi.iter() {
        for (j, &r) in star.iter().enumerate() {
            if ray_polarity(r) == Polarity::Neutral {
                continue;
            }
            if any_match_accel(accel, phi, r, &psi_cs) {
                return false;
            }
            if any_self(star, j) {
                return false;
            }
        }
    }
    true
}

/// `IEx_C(Φ, Ψ)` — KS-accelerated (spec §8 Lever A). **Byte-identical** to the
/// reference [`iex`] (N-KS gate), via two faithful structural changes:
///
/// * **In-place Ψ**: `remove(star_idx)` (order-preserving) + `extend` of only
///   the produced stars — no per-step `Vec<Star>` realloc.
/// * **Resume cursor**: the reference rescans Ψ from star 0 every step. When
///   `psi_csyms` is unchanged from the previous step, every star in
///   `[0, resume_from)` is *physically untouched* by `remove`/`extend` **and**
///   was already proven non-matchable under the *same* colour set — so the
///   global first match necessarily has `i ≥ resume_from`. Scanning from
///   `resume_from` therefore selects the *identical* `(i, j)` as a full scan
///   (and "nothing from `resume_from`" ⇒ genuine normal form, since the
///   skipped prefix is non-matchable). Any colour change ⇒ `start = 0`
///   (full-rescan fallback). The reference [`iex`] is the differential oracle.
pub fn iex_fast(phi: &Constellation, psi_init: Vec<Star>, fuel: usize) -> IExResult {
    iex_fast_inner(&IexAccel::build(phi), phi, psi_init, fuel, false, false)
}

/// Build the KS acceleration structure for a fixed Φ once, to be reused
/// across many [`iex_fast_with_accel`] / [`iex_tabled_with_accel`] runs.
///
/// `IexAccel` is a **pure function of Φ**: its head-index (`RayIndex`) and
/// colour-symbol set (`phi_csyms`) are derived solely from Φ's rays and carry
/// no Ψ- or run-state. For a fixed Φ, reusing one `accel` across any number
/// of runs / any Ψ is provably byte-identical to rebuilding it per call
/// (`iex_fast` = `iex_fast_with_accel(&build_accel(phi), phi, …)`). The valence
/// loop holds Φ fixed and perturbs Ψ (or applies a small Φ-delta + rebuild),
/// so this hoists the per-call `IexAccel::build` out of millions of small
/// executions. Passing an `accel` built from a *different* Φ than the `phi`
/// later supplied is a caller bug (mismatched head-index ⇒ wrong candidate
/// set); this is not — and cannot cheaply — be verified.
pub fn build_accel(phi: &Constellation) -> IexAccel {
    IexAccel::build(phi)
}

/// [`iex_fast`] (byte-identical jet) with the Φ-derived [`IexAccel`] supplied
/// by the caller instead of rebuilt per call. See [`build_accel`] for the
/// reuse contract: result is provably identical to `iex_fast(phi, …)` when
/// `accel == build_accel(phi)`.
pub fn iex_fast_with_accel(
    accel: &IexAccel,
    phi: &Constellation,
    psi_init: Vec<Star>,
    fuel: usize,
) -> IExResult {
    iex_fast_inner(accel, phi, psi_init, fuel, false, false)
}

/// [`iex_tabled`] (KA1 variant-deletion) with a caller-supplied [`IexAccel`].
/// Composes the two valence-critical reuse paths: KA1 tabling **and**
/// per-Φ accel hoisting, for the variant-dense valence search loop.
pub fn iex_tabled_with_accel(
    accel: &IexAccel,
    phi: &Constellation,
    psi_init: Vec<Star>,
    fuel: usize,
) -> IExResult {
    iex_fast_inner(accel, phi, psi_init, fuel, true, false)
}

/// KA1 — `iex_fast` + **variant-deletion tabling** (spec §9). A produced star
/// that is an α-variant of one already seen (initial or earlier-produced) is
/// redundant — on the confluent objective/Horn fragment its consequences are
/// α-variants of already-reachable ones — so it is dropped. This turns
/// fuel-truncation into a genuine **fixpoint**: when a step yields only
/// variants, nothing new accumulates and execution reaches a true normal
/// form instead of looping. The SLG/tabling "exact reuse by variant
/// checking" layer the survey mandates *first*; sound for the membership-
/// based result extraction the codebase uses, differential-gated
/// (result-equivalence vs reference `iex`), not byte-identical — that trade
/// (fixpoint termination for step-identity) is the reframed N-KS.
/// `iex_fast` (the byte-identical jet) is left untouched.
pub fn iex_tabled(phi: &Constellation, psi_init: Vec<Star>, fuel: usize) -> IExResult {
    iex_fast_inner(&IexAccel::build(phi), phi, psi_init, fuel, true, false)
}

/// Σ(Φ) — the first Futamura projection as a **sibling fast tier** (docs/14,
/// docs/17). Identical redex selection to [`iex_fast`] (same `iex_fast_inner`
/// scan), but at iex_fast's own chosen `(ik,jk)` a specialisable Φ-star's
/// resolvent is built from the closed [`SpecTr`] residual instead of
/// α-rename + `unify_fast` + whole-star θ-apply. Σ2 scope: δ + Push +
/// combinator/lazy-prim `Splice` all realised; only strict ops (which
/// carry no `SpecTr`) delegate to the generic `drive_strict` path.
/// Decision-equivalent to reference [`iex`] (gated by
/// `faithfulness::psi_compatible`, **step-count identical** to `iex_fast`);
/// the proven byte-identical `iex_fast`/`iex_tabled`/`iex` are untouched —
/// this is a parallel tier with the same deopt discipline as `iex_tabled`.
pub fn iex_spec(phi: &Constellation, psi_init: Vec<Star>, fuel: usize) -> IExResult {
    iex_fast_inner(&IexAccel::build(phi), phi, psi_init, fuel, false, true)
}

/// [`iex_spec`] with a caller-supplied [`IexAccel`] (carries the Σ(Φ)
/// residual; build once per fixed Φ, reuse across runs — the valence/galaxy
/// hot loop). Provably identical to `iex_spec(phi, …)` when
/// `accel == build_accel(phi)`.
pub fn iex_spec_with_accel(
    accel: &IexAccel,
    phi: &Constellation,
    psi_init: Vec<Star>,
    fuel: usize,
) -> IExResult {
    iex_fast_inner(accel, phi, psi_init, fuel, false, true)
}

/// Conservative α-variant key of a star: `canonical` of its rays as an
/// ordered tuple. Order-sensitive ⇒ may miss a ray-permuted variant
/// (under-dedup, merely less speedup) but **never** conflates two genuinely
/// different stars (sound: never drops a non-variant).
fn star_key(star: &Star) -> Term {
    crate::antiunify::canonical(crate::term::mk_app_str("\u{22c6}star", star.clone()))
}

fn iex_fast_inner(
    accel: &IexAccel,
    phi: &Constellation,
    psi_init: Vec<Star>,
    fuel: usize,
    tabling: bool,
    spec: bool,
) -> IExResult {
    let mut psi = psi_init;
    let mut counter = 0u32;
    let mut steps = 0;
    let mut prev_cs: Option<FxHashSet<crate::term::Sym>> = None;
    let mut resume_from = 0usize;
    // WIN 1 (docs/explore/perf-audit.md §3): the per-step `psi_csyms(&psi)`
    // O(|Ψ|) rebuild is replaced by an incrementally-maintained colour
    // multiset, seeded once here and updated by the per-step Ψ delta
    // (`remove`d `selected` − , appended `produced` +). `pcs.set()` is, by
    // the debug-gated oracle below, *exactly* `psi_csyms(&psi)` every step.
    let mut pcs = PsiCS::from_psi(&psi);
    // KA1 table: α-variant keys of every star ever present (seed with the
    // initial Ψ so a re-derived copy of a starting subgoal is reused).
    let mut seen: FxHashSet<Term> = FxHashSet::default();
    if tabling {
        for s in &psi {
            seen.insert(star_key(s));
        }
    }

    while steps < fuel {
        let tp = std::time::Instant::now();
        // Faithfulness oracle (debug-only; compiled out of release): the
        // incrementally-maintained set MUST equal the full `psi_csyms`
        // rebuild on *every* step — proven, not argued (task gate #2).
        pcs.assert_eq_full(&psi);
        let psi_cs = pcs.set();
        ks_add(&T_PSICS, tp.elapsed());

        // Resume invariant: identical colour set ⇒ the untouched prefix
        // [0, resume_from) is still non-matchable; else full rescan.
        let start = match &prev_cs {
            Some(p) if p == psi_cs => resume_from.min(psi.len()),
            _ => 0,
        };

        let ts = std::time::Instant::now();
        let mut found_step = None;
        'outer: for i in start..psi.len() {
            let star = &psi[i];
            for (j, &r) in star.iter().enumerate() {
                if ray_polarity(r) == Polarity::Neutral {
                    continue;
                }
                // Σ(Φ) SELECTION residual (spec tier only). `sel.decide(r)`
                // is a sound *positive-only* short-circuit: `Some(true)`
                // ⇒ `any_match_accel(accel,phi,r,psi_cs)` is provably `true`
                // (witness Φ pattern + colour-gate discharged), so the
                // `… || any_self` disjunct is `true` exactly as the generic
                // scan would short-circuit it; `None` ⇒ fall through to the
                // UNCHANGED `any_match_accel || any_self`. Hence the chosen
                // `(i,j)` — and the whole step stream / step count — is
                // bit-identical to `iex_fast`; the lever is purely the cost
                // of deciding the same boolean. `iex_fast`/`iex_tabled`/
                // reference `iex` pass `spec=false` ⇒ never consult it.
                let matched = if spec {
                    match accel.sel.decide(r) {
                        Some(true) => true,
                        // `decide` is never `Some(false)`; `None` ⇒ exact scan.
                        _ => any_match_accel(accel, phi, r, psi_cs) || any_self(star, j),
                    }
                } else {
                    any_match_accel(accel, phi, r, psi_cs) || any_self(star, j)
                };
                if matched {
                    found_step = Some((i, j));
                    break 'outer;
                }
            }
        }
        ks_add(&T_FIND, ts.elapsed());

        match found_step {
            None => {
                // Nothing from `start`; prefix [0,start) non-matchable by the
                // resume invariant (or start==0) ⇒ true normal form.
                ks_report(steps);
                return IExResult { psi, is_normal_form: true, steps };
            }
            Some((i, j)) => {
                let selected = psi.remove(i);
                // docs/16 §3.2 H1 tap: record the resolved head + the
                // α-canonical key of this redex. No-op (one `with` + `is_none`
                // branch) unless a measurement harness installed the sink ⇒
                // byte-identical to un-instrumented `iex_fast`. Observation
                // only; never alters `selected`, `psi`, or the step.
                H1_TAP.with(|t| {
                    let mut b = t.borrow_mut();
                    if let Some(sink) = b.as_mut() {
                        if sink.log.len() < sink.cap {
                            if let Some(h) = h1_resolved_head(selected[j]) {
                                let canon = crate::antiunify::canonical(
                                    crate::term::mk_app_str("\u{22c6}redex", selected.clone()),
                                );
                                sink.log.push((h, canon));
                            }
                        }
                    }
                });
                let produced =
                    produce_stars_fast(accel, phi, &selected, j, &mut counter, psi_cs, spec);
                // Snapshot the colour set for the next step's resume check
                // *before* the delta mutates it (this also ends the immutable
                // borrow of `pcs` so the incremental update below can take
                // `&mut pcs`). Cheap: the set is over *distinct colours*, not
                // |Ψ| — and this is the exact value the old code stored.
                let cs_snapshot = psi_cs.clone();
                // Ψ delta − : the `selected` star left Ψ.
                pcs.remove_star(&selected);
                if tabling {
                    // KA1: drop α-variant redundant stars; keep + table the rest.
                    // (If a step yields only variants ⇒ no growth ⇒ fixpoint.)
                    for s in produced {
                        let k = star_key(&s);
                        if seen.insert(k) {
                            // Ψ delta + : only stars actually pushed are
                            // accounted (α-variants dropped here never enter Ψ
                            // ⇒ never contribute a colour) — keeps `pcs` an
                            // exact mirror of `psi`.
                            pcs.add_star(&s);
                            psi.push(s);
                        }
                    }
                } else {
                    for s in produced {
                        // Ψ delta + : every produced star enters Ψ.
                        pcs.add_star(&s);
                        psi.push(s);
                    }
                }
                // Prefix [0, i) was scanned non-matchable this step and is
                // physically untouched by remove/extend ⇒ safe resume point.
                resume_from = i;
                prev_cs = Some(cs_snapshot);
                steps += 1;
            }
        }
    }

    let nf = is_normal_form_accel(accel, phi, &psi);
    ks_report(steps);
    IExResult { psi, is_normal_form: nf, steps }
}

/// Print + reset the env-gated phase profile (no-op unless `STELLA_KS_PROF=1`).
fn ks_report(steps: usize) {
    if !*KS_PROF {
        return;
    }
    let p = T_PSICS.with(|c| c.replace(0.0));
    let s = T_FIND.with(|c| c.replace(0.0));
    let m = T_MATCH.with(|c| c.replace(0.0));
    let f = T_FRESH.with(|c| c.replace(0.0));
    let u = T_FUSE.with(|c| c.replace(0.0));
    let un = T_UNIFY.with(|c| c.replace(0.0));
    let sb = T_SUBST.with(|c| c.replace(0.0));
    let tot = p + s + f + u;
    let pc = |x: f64| 100.0 * x / tot.max(1e-12);
    eprintln!(
        "[KS-PROF] steps={steps} psics={p:.4}s ({:.0}%) find={s:.4}s ({:.0}%) [matchable={m:.4}s ({:.0}% of find)] freshen={f:.4}s ({:.0}%) fuse={u:.4}s ({:.0}%) [unify={un:.4}s subst={sb:.4}s] tot={tot:.4}s",
        pc(p), pc(s), 100.0 * m / s.max(1e-12), pc(f), pc(u),
    );
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

/// KS-accelerated `↨♭ IEx_C(Φ, Ψ)` — identical output to [`iex_concealed`]
/// (it delegates to [`iex_fast`], which the N-KS gate proves ≡ [`iex`]).
pub fn iex_fast_concealed(phi: &Constellation, psi: Vec<Star>, fuel: usize) -> (Vec<Star>, bool) {
    let res = iex_fast(phi, psi, fuel);
    let visible = conceal_and_filter(&res.psi);
    (visible, res.is_normal_form)
}

/// KA1 concealed run: [`iex_tabled`] + `↨♭`. Result-equivalent to
/// [`iex_fast_concealed`] on the confluent fragment (differential-gated),
/// but reaches a true fixpoint where the untabled path fuels out.
pub fn iex_tabled_concealed(phi: &Constellation, psi: Vec<Star>, fuel: usize) -> (Vec<Star>, bool) {
    let res = iex_tabled(phi, psi, fuel);
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

    /// `step_detail` must be *exactly* what `iex` does for one step (not a
    /// reconstruction): same successor Ψ, and every summand carries the real
    /// θ the engine applied.
    #[test]
    fn step_detail_is_faithful_and_exact() {
        let phi = add_prog();
        let psi = vec![query_star(2, 2)];
        // iex fires the first coloured ray (0,0) on its first step.
        let one = iex(&phi, psi.clone(), 1);
        let mut counter = 0u32;
        let det = step_detail(&phi, &psi, 0, 0, &mut counter).expect("redex");
        assert!(!det.summands.is_empty(), "step produced a non-empty sum");
        assert_eq!(
            det.psi_after.len(),
            one.psi.len(),
            "step_detail Ψ' size matches iex(fuel=1)"
        );
        for (a, b) in det.psi_after.iter().zip(one.psi.iter()) {
            assert!(
                stars_alpha_equiv(a, b),
                "step_detail Ψ' is α-equal to iex's: {a:?} vs {b:?}"
            );
        }
        // The first external summand's θ genuinely unifies the matched
        // underlying terms (applying θ makes them syntactically equal).
        let s = det.summands.iter().find(|s| s.external).expect("ext summand");
        assert!(
            !s.theta.is_empty() || s.result.len() <= 2,
            "a non-trivial fusion records a non-empty θ"
        );
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

    /// `mat_phi_c_accel` returns the *identical* match list as `mat_phi_c`.
    #[test]
    fn mat_accel_eq_mat_ref() {
        let phi = add_prog();
        let accel = IexAccel::build(&phi);
        let empty_s: HashSet<String> = HashSet::new();
        let empty_cs: FxHashSet<crate::term::Sym> = FxHashSet::default();
        for q in [nat(0), nat(1), nat(2), nat(3)] {
            let r = neg_ray("add", vec![q, nat(2), var("R")]);
            assert_eq!(
                mat_phi_c(&phi, r, &empty_s),
                mat_phi_c_accel(&accel, &phi, r, &empty_cs),
                "accel must equal reference mat_phi_c"
            );
        }
    }

    /// **N-KS gate, reframed (docs/09; spec §8 §10.5).** `iex_fast` now uses
    /// the near-linear `unify_fast`, whose MGU is α-equal — not byte-equal —
    /// to the reference `unify`'s. So the gate is proven **result-
    /// equivalence**, not byte-identity: same ɟ-concealed visible answer
    /// multiset (`faithfulness::psi_compatible`, itself bootstrap-proven —
    /// B0a/B0b) and both reach a true normal form. Reference `iex` stays the
    /// differential oracle; any `psi_compatible` failure ⇒ the fast path is
    /// unfaithful and must be reverted. (Verified-speculative-runtime model,
    /// docs/07 §H. Step counts are α-strategy-invariant in practice but no
    /// longer asserted — the contract is the answer multiset.)
    #[test]
    fn iex_fast_result_eq_iex() {
        use crate::faithfulness::psi_compatible;

        // (a) Horn arithmetic (recursive Φ reuse).
        let mut phi = add_prog();
        phi.push(vec![
            neg_ray("add", vec![nat(3), nat(2), var("R")]),
            var("R"),
        ]);
        let q = vec![phi.pop().unwrap()];
        let a = iex(&phi, q.clone(), 5000);
        let b = iex_fast(&phi, q, 5000);
        assert!(psi_compatible(&a.psi, &b.psi), "Horn: not result-equivalent");
        assert_eq!(a.is_normal_form, b.is_normal_form, "Horn: NF disagreement");

        // (b) Combinator core (K1) — SKK = I, the non-linear S star.
        let prog = crate::combinator::app_n([
            crate::combinator::a_("S"),
            crate::combinator::a_("T"),
            crate::combinator::a_("T"),
            crate::combinator::a_("x"),
        ]);
        let cphi = crate::combinator::machine_stars();
        let cpsi = vec![crate::combinator::initial_process(&prog)];
        let ca = iex(&cphi, cpsi.clone(), 3000);
        let cb = iex_fast(&cphi, cpsi, 3000);
        assert!(psi_compatible(&ca.psi, &cb.psi), "combinator: not result-equivalent");
        assert_eq!(ca.is_normal_form, cb.is_normal_form, "combinator: NF disagreement");

        // (c) Binary arithmetic module (KG1a) — add small.
        let bphi = crate::binarith::binarith_module();
        let bq = vec![vec![
            neg_ray("add", vec![crate::binarith::nat(5), crate::binarith::nat(6), var("R")]),
            var("R"),
        ]];
        let ba = iex(&bphi, bq.clone(), 8000);
        let bb = iex_fast(&bphi, bq, 8000);
        assert!(psi_compatible(&ba.psi, &bb.psi), "binarith: not result-equivalent");
        assert_eq!(ba.is_normal_form, bb.is_normal_form, "binarith: NF disagreement");

        // Falsifier (the wrong-unifier guard): the gate MUST reject an
        // unfaithful fast result, not just accept faithful ones — else it
        // proves nothing. Corrupt the Horn fast result with a spurious
        // all-neutral visible answer and assert psi_compatible is false.
        let mut corrupt = b.psi.clone();
        corrupt.push(vec![crate::term::mk_app_str(
            "BOGUS",
            vec![crate::term::mk_app_str("z", vec![])],
        )]);
        assert!(
            !psi_compatible(&a.psi, &corrupt),
            "gate must catch an unfaithful fast result (wrong-unifier falsifier)"
        );
    }

    /// **Σ(Φ) Σ1/Σ2 differential gate (docs/17 §4).** `iex_spec` = the
    /// in-loop Futamura sibling tier (δ + Push + combinator/lazy-prim
    /// `Splice` all realised from the closed `SpecTr`; only strict ops
    /// delegate). Three guarantees, all on the same corpus the
    /// `iex_fast` gate uses (incl. the combinator SKK that sank the prior
    /// prefix-loop attempt — now green because redex selection is *literally*
    /// iex_fast's):
    ///   (1) decision-equivalent to reference `iex` (`psi_compatible`);
    ///   (2) **step-count identical to `iex_fast`** — THE per-step-lever
    ///       proof: same redex stream, only the realisation is cheaper (if
    ///       steps moved, the specialisation would be *semantically* wrong,
    ///       not faster);
    ///   (3) **per-step structural equivalence to `iex_fast`** — every Ψ
    ///       star is α-equal to the one the generic α-rename+`unify_fast`+
    ///       θ-apply path builds. This is the load-bearing Σ1 gate: on the
    ///       pure-KAM δ/Push corpora the ɟ-concealed *visible* answer is
    ///       empty (the result lives inside the `+P(st …)` process scaffold
    ///       `conceal` strips), so `psi_compatible` alone is near-vacuous
    ///       there — α-equivalence of the actual process states is the
    ///       non-vacuous faithfulness evidence (honest scoping of the gate,
    ///       not a weakening of it);
    ///   (4) **non-vacuity**: the spec realiser provably *fires* (`SPEC_HITS`
    ///       advances) on combinator + galaxy — the prior prefix-loop's exact
    ///       failing corpus now in-loop-green;
    ///   (5) the gate REJECTS a corrupted `SpecTr` (defense-in-depth: the
    ///       docs/17 Σ1 `Delta(bogus)` negative — proves the realiser
    ///       consults the residual and the structural gate has teeth).
    #[test]
    fn iex_spec_result_eq_iex() {
        use crate::faithfulness::psi_compatible;
        use std::sync::atomic::Ordering::Relaxed;
        let hits = || SPEC_HITS.load(Relaxed);
        // Element-wise α-equivalence of two Ψ states (iex_spec keeps
        // iex_fast's exact redex stream + produce order ⇒ index-aligned).
        let psi_ae = |a: &[Star], b: &[Star]| -> bool {
            a.len() == b.len()
                && a.iter()
                    .zip(b.iter())
                    .all(|(x, y)| crate::execution::stars_alpha_equiv(x, y))
        };

        // (a) Horn arithmetic — no `st`/Push shape ⇒ Σ(Φ) delegates wholly
        // (0 hits): proves the delegation path is inert/correct.
        let mut phi = add_prog();
        phi.push(vec![neg_ray("add", vec![nat(3), nat(2), var("R")]), var("R")]);
        let q = vec![phi.pop().unwrap()];
        let h_ref = iex(&phi, q.clone(), 5000);
        let h_fast = iex_fast(&phi, q.clone(), 5000);
        let h_spec = iex_spec(&phi, q, 5000);
        assert!(psi_compatible(&h_ref.psi, &h_spec.psi), "Horn: spec ≢ iex");
        assert_eq!(h_spec.steps, h_fast.steps, "Horn: spec step-count ≠ iex_fast");
        assert!(psi_ae(&h_fast.psi, &h_spec.psi), "Horn: spec ≇ iex_fast (α)");
        assert_eq!(h_ref.is_normal_form, h_spec.is_normal_form, "Horn: NF");

        // (b) Combinator core SKK (S is the non-linear duplicating star —
        // the exact corpus the prior prefix-loop iex_spec failed). Push→
        // Unwind AND S/K/I→Splice are now realised (Σ2 scope).
        let prog = crate::combinator::app_n([
            crate::combinator::a_("S"),
            crate::combinator::a_("T"),
            crate::combinator::a_("T"),
            crate::combinator::a_("x"),
        ]);
        let cphi = crate::combinator::machine_stars();
        let cpsi = vec![crate::combinator::initial_process(&prog)];
        let c_ref = iex(&cphi, cpsi.clone(), 3000);
        let c_fast = iex_fast(&cphi, cpsi.clone(), 3000);
        let c0 = hits();
        let c_spec = iex_spec(&cphi, cpsi.clone(), 3000);
        assert!(hits() > c0, "combinator: Σ(Φ) realiser never fired (vacuous)");
        assert!(psi_compatible(&c_ref.psi, &c_spec.psi), "combinator: spec ≢ iex");
        assert_eq!(c_spec.steps, c_fast.steps, "combinator: spec step-count ≠ iex_fast");
        assert!(
            psi_ae(&c_fast.psi, &c_spec.psi),
            "combinator: spec ≇ iex_fast (α) — the in-loop Σ1 proof"
        );
        assert_eq!(c_ref.is_normal_form, c_spec.is_normal_form, "combinator: NF");

        // (c) Binary arithmetic module.
        let bphi = crate::binarith::binarith_module();
        let bq = vec![vec![
            neg_ray("add", vec![crate::binarith::nat(5), crate::binarith::nat(6), var("R")]),
            var("R"),
        ]];
        let b_ref = iex(&bphi, bq.clone(), 8000);
        let b_fast = iex_fast(&bphi, bq.clone(), 8000);
        let b_spec = iex_spec(&bphi, bq, 8000);
        assert!(psi_compatible(&b_ref.psi, &b_spec.psi), "binarith: spec ≢ iex");
        assert_eq!(b_spec.steps, b_fast.steps, "binarith: spec step-count ≠ iex_fast");
        assert!(psi_ae(&b_fast.psi, &b_spec.psi), "binarith: spec ≇ iex_fast (α)");

        // (d) Galaxy Φ=405 (the real δ/Push skeleton) if the artifact is
        // present — bounded fuel; identical redex stream ⇒ α-equivalence at
        // the cutoff is a valid (and here non-vacuous) faithfulness check.
        const GP: &str = "/Users/ember/dev/embershot/src/galaxy.txt";
        match std::fs::read_to_string(GP).ok().and_then(|s| crate::galaxy::parse(&s).ok()) {
            Some(g) if !g.defs.is_empty() => {
                let gphi = crate::galaxy::constellation(&g);
                let d0 = g.defs.first().unwrap();
                let gq = crate::galaxy::initial_psi(crate::galaxy::ref_atom(d0.name));
                let g_ref = iex(&gphi, gq.clone(), 4000);
                let g_fast = iex_fast(&gphi, gq.clone(), 4000);
                let g0 = hits();
                let g_spec = iex_spec(&gphi, gq, 4000);
                assert!(hits() > g0, "galaxy: Σ(Φ) realiser never fired (vacuous)");
                assert!(psi_compatible(&g_ref.psi, &g_spec.psi), "galaxy: spec ≢ iex");
                assert_eq!(g_spec.steps, g_fast.steps, "galaxy: spec step-count ≠ iex_fast");
                assert!(
                    psi_ae(&g_fast.psi, &g_spec.psi),
                    "galaxy: spec ≇ iex_fast (α) — the in-loop Σ1 proof"
                );
            }
            _ => eprintln!("SKIP galaxy slice: {GP} absent/unparsable/empty"),
        }

        // (e) Falsifier — corrupt the Σ(Φ) residual and demand the gate goes
        // RED. Overwrite the combinator Push (Unwind) entry with a bogus
        // `Delta`; the realiser MUST consult it and build a structurally
        // wrong resolvent ⇒ the per-step α-gate must reject it.
        let mut accel = IexAccel::build(&cphi);
        let push_ix = (0..cphi.len())
            .find(|&i| matches!(accel.spec[i], Some((_, SpecTr::Unwind))))
            .expect("combinator Φ must contain a Push→Unwind star");
        let neg_idx = accel.spec[push_ix].as_ref().unwrap().0;
        accel.spec[push_ix] = Some((
            neg_idx,
            SpecTr::Delta(crate::term::mk_app_str("BOGUS", vec![])),
        ));
        let bad = iex_spec_with_accel(&accel, &cphi, cpsi, 3000);
        assert!(
            !psi_ae(&c_fast.psi, &bad.psi),
            "gate MUST reject a corrupted SpecTr (Σ1 Delta(bogus) negative)"
        );
    }

    /// **KA1 differential gate (result-equivalence, the reframed N-KS).**
    /// `iex_tabled` is NOT byte-identical to reference `iex` (it drops variant
    /// stars, so `psi`/`steps` differ — by design). It MUST be observationally
    /// equivalent: same ɟ-concealed answer set (up to α) and both reach a true
    /// normal form. The reference `iex` stays the differential oracle; any
    /// answer-set divergence ⇒ tabling unfaithful ⇒ revert (no ceremony, the
    /// oracle *is* the rigor).
    #[test]
    fn iex_tabled_result_eq_iex() {
        let same_answers = |a: &[Star], b: &[Star]| -> bool {
            let av = conceal_and_filter(&a.to_vec());
            let bv = conceal_and_filter(&b.to_vec());
            let subset = |xs: &[Star], ys: &[Star]| {
                xs.iter()
                    .all(|x| ys.iter().any(|y| crate::execution::stars_alpha_equiv(x, y)))
            };
            subset(&av, &bv) && subset(&bv, &av)
        };

        // (a) Horn add(3,2) → [5̄].
        let phi = add_prog();
        let q = vec![query_star(3, 2)];
        let r = iex(&phi, q.clone(), 5000);
        let t = iex_tabled(&phi, q, 5000);
        assert!(t.is_normal_form, "tabled Horn must reach a true fixpoint");
        assert!(
            same_answers(&r.psi, &t.psi),
            "tabled Horn answer set differs from reference oracle"
        );

        // (b) Binary arith add(5,6) → [11̄].
        let bphi = crate::binarith::binarith_module();
        let bq = vec![vec![
            neg_ray("add", vec![crate::binarith::nat(5), crate::binarith::nat(6), var("R")]),
            var("R"),
        ]];
        let br = iex(&bphi, bq.clone(), 8000);
        let bt = iex_tabled(&bphi, bq, 8000);
        assert!(bt.is_normal_form, "tabled binarith must reach a true fixpoint");
        assert!(
            same_answers(&br.psi, &bt.psi),
            "tabled binarith answer set differs from reference oracle"
        );
    }

    /// **Accel-reuse faithfulness gate.** `iex_fast_with_accel` with a
    /// build-once `accel` reused across *different* Ψ must be byte-identical
    /// to per-call `iex_fast` (the contract: `IexAccel` is a pure function of
    /// Φ, no Ψ/run state). And `iex_tabled_with_accel` must match `iex_tabled`.
    #[test]
    fn iex_fast_with_accel_eq_iex_fast() {
        // (a) Horn add(3,2): one accel, two different Ψ.
        let mut phi = add_prog();
        phi.push(vec![neg_ray("add", vec![nat(3), nat(2), var("R")]), var("R")]);
        let q1 = vec![phi.pop().unwrap()];
        let accel = build_accel(&phi);
        let plain1 = iex_fast(&phi, q1.clone(), 5000);
        let reuse1 = iex_fast_with_accel(&accel, &phi, q1, 5000);
        assert_eq!(plain1.psi, reuse1.psi, "Horn: psi differs (reuse 1)");
        assert_eq!(plain1.steps, reuse1.steps, "Horn: steps differ (reuse 1)");
        assert_eq!(plain1.is_normal_form, reuse1.is_normal_form);
        // SAME accel, DIFFERENT Ψ — the valence regime.
        let q2 = vec![vec![neg_ray("add", vec![nat(4), nat(1), var("R")]), var("R")]];
        let plain2 = iex_fast(&phi, q2.clone(), 5000);
        let reuse2 = iex_fast_with_accel(&accel, &phi, q2, 5000);
        assert_eq!(plain2.psi, reuse2.psi, "Horn: psi differs (reuse 2)");
        assert_eq!(plain2.steps, reuse2.steps, "Horn: steps differ (reuse 2)");

        // (b) Binary arith add(5,6) — both reuse primitives.
        let bphi = crate::binarith::binarith_module();
        let baccel = build_accel(&bphi);
        let bq = vec![vec![
            neg_ray("add", vec![crate::binarith::nat(5), crate::binarith::nat(6), var("R")]),
            var("R"),
        ]];
        let bp = iex_fast(&bphi, bq.clone(), 8000);
        let bre = iex_fast_with_accel(&baccel, &bphi, bq.clone(), 8000);
        assert_eq!(bp.psi, bre.psi, "binarith: psi differs");
        assert_eq!(bp.steps, bre.steps, "binarith: steps differ");
        let bt = iex_tabled(&bphi, bq.clone(), 8000);
        let btre = iex_tabled_with_accel(&baccel, &bphi, bq, 8000);
        assert_eq!(bt.psi, btre.psi, "tabled binarith: psi differs w/ accel");
        assert_eq!(bt.steps, btre.steps, "tabled binarith: steps differ w/ accel");
    }

    /// Proof-of-work micro-bench (env-gated, ignored by default): per-call
    /// `IexAccel::build` vs hoisted `build_accel` over N small executions on a
    /// non-trivial fixed Φ (binarith module) — the valence regime. Not a gate;
    /// run: `cargo test -p stella-core --release ks_accel_hoist_bench -- --ignored --nocapture`.
    #[test]
    #[ignore = "bench: measurement, not a faithfulness gate"]
    fn ks_accel_hoist_bench() {
        let phi = crate::binarith::binarith_module();
        let mk = || {
            vec![vec![
                neg_ray("add", vec![crate::binarith::nat(5), crate::binarith::nat(6), var("R")]),
                var("R"),
            ]]
        };
        let n = 1000;
        let t0 = std::time::Instant::now();
        let mut s1 = 0;
        for _ in 0..n {
            s1 += iex_fast(&phi, mk(), 8000).steps;
        }
        let per_call = t0.elapsed();
        let t1 = std::time::Instant::now();
        let accel = build_accel(&phi);
        let mut s2 = 0;
        for _ in 0..n {
            s2 += iex_fast_with_accel(&accel, &phi, mk(), 8000).steps;
        }
        let hoisted = t1.elapsed();
        assert_eq!(s1, s2, "aggregate step counts must match (faithfulness)");
        eprintln!(
            "ks_accel_hoist_bench N={n} binarith-Φ: per-call={:.1}ms hoisted={:.1}ms speedup={:.2}x",
            per_call.as_secs_f64() * 1e3,
            hoisted.as_secs_f64() * 1e3,
            per_call.as_secs_f64() / hoisted.as_secs_f64()
        );
    }
}
