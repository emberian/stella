# 17 — Σ(Φ) Futamura: incremental implementation plan

Operationalises docs/14 (the design/why) against the **current** post-Stage-1b
codebase. docs/14 = what/why; this = the exact staged, faithfulness-gated
landing. Tags: [Built] in tree · [Proto] to build.

## 0. What Σ(Φ) is and is NOT (honest, up front)

Σ(Φ) = the **1st Futamura projection**: specialise the resolution
interpreter to the *fixed* galaxy Φ (405 stars) ⇒ a closed per-head
transition table; one δ-step becomes O(1) table-lookup + one node
construction instead of `psi_csyms` + O(|Φ|) scan + α-rename + unify +
`theta.apply`. It is a **per-step-cost lever** (like `unify_fast`). By
docs/11 Fact-2 it **does NOT make `data[0]` terminate** — it is the
lower-risk, multiplicatively-compounding *companion* to the
termination-crosser (KA2/H2 or interaction-net/H1, picked by the
docs/16 discriminator). Build it for: the proven-2× galaxy skeleton →
much faster, and a clean compounding base for the H-lever.

## 1. The artifact [Proto]

New module `crates/stella-core/src/spec_phi.rs`:

```rust
pub enum Transition {
    Delta(TermId),                 // δ-head :N → its closed body• ; step = st(body, π)
    Unwind,                        // a-head  → Push: M⋆π ↦ headof·(args·π)
    Splice { pop: usize, template: TermId }, // combinator (s/c/b/i/t/f/cons/car/cdr/nil)
    Jet,                           // strict op (add/mul/eq/lt/div/neg/isnil) → leave to drive_strict
}
pub struct SpecPhi { table: FxHashMap<Sym, Transition> }   // head Sym → closed Transition
impl SpecPhi { pub fn build(phi:&Constellation)->Self; pub fn get(&self,h:Sym)->Option<&Transition>; }
```

Built ONCE per fixed Φ (the partial-evaluation residual), keyed by spine
head. Derivation, all from [Built] sources:
- δ-stars: `galaxy::delta_star` shape `[-P(st(:N,π)),+P(st(body,π))]`
  ⇒ `:N ↦ Delta(body)`. body is closed/ground (`term::is_ground`) — the
  ONLY var is π, definitionally bound to the actual stack ⇒ no unify, no
  α-rename, no `theta.apply`.
- `prim_stars` (`galaxy.rs:425-468`): `a`-head ⇒ `Unwind` (the verbatim
  `galaxy.rs:423` Push rule); each combinator letter ⇒
  `Splice{pop:arity, template}` (positional instantiation of the fixed
  contractum); `add/mul/eq/lt/div/neg/isnil` ⇒ `Jet`.

## 2. The driver `iex_spec` [Proto] — minimal-blast seam (mirrors Stage-1b)

`iex_fast_inner(phi, psi, fuel, tabling)` (`interactive.rs:1086`) is the
shared fast loop; `iex_fast`/`iex_tabled` are thin wrappers;
`IexAccel`/`build_accel` (`:287/:1033`) is the existing per-Φ precompute.
Σ(Φ) extends exactly that pattern:
- `SpecPhi` rides alongside `IexAccel` (build once per Φ; `iex_fast_with_accel`-style reuse for the valence/galaxy hot loop).
- `iex_spec` = a NEW sibling tier (a `Tier::Spec`, parallel to
  Fast/Tabled). Per step: `h = spine_head(focus)`; `SpecPhi.get(h)`:
  - `Delta(body)` → `psi := st(body, π)` (consume the δ-redex; no scan/
    unify/rename/apply). O(1).
  - `Unwind` → the Push transition (already in the loop).
  - `Splice{pop,template}` → pop `pop` `dot`-frames, instantiate template.
  - `Jet` → **delegate to the existing `drive_strict`/forced path
    unchanged** (the §49.50 ray-minting boundary — Σ(Φ) specialises ONLY
    the objective δ/Push/combinator skeleton; strict dynamics stay where
    docs/08 needs them).
  - miss → fall through to the generic `produce_stars_fast` (safety).
- Reference `iex` (`:861`) is **never reachable from `iex_spec`** and
  vice-versa (static, like the Stage-1b `Solve` seam — un-contaminable).
- `eval_forced`/the galaxy path gets a tier selector to drive `iex_spec`.

## 3. Faithfulness gate (unchanged invariant)

Reference `iex` = oracle; `faithfulness::psi_compatible` = the proven
gate; `iex_spec` is two-tier with **deopt** to reference `iex` on any
red `psi_compatible` (mirrors the `unify_fast` story). Sound *by
construction* on the δ/Push/combinator fragment (a δ-`Transition` is the
literal denotation of its δ-star; combinator `Splice` is the positional
instantiation of the fixed contractum; `Unwind` is the verbatim Push
rule) — `psi_compatible` is defense-in-depth catching a *builder* bug.

## 4. Staged, falsifiable increments (each its own commit; gate per stage)

- **Σ0** `spec_phi.rs`: `Transition`/`SpecPhi`/`build` + unit tests that
  the table for the galaxy/combinator/Horn Φ has the expected
  per-head Transitions (δ count = #defs; `a`→Unwind; each prim mapped).
  NO driver. Zero engine risk (new disjoint module, like `unify_fast`
  Stage 1a). Falsifier: a Φ whose built table disagrees with hand
  enumeration ⇒ red.
- **Σ1** `iex_spec` driver, δ/Push only; combinator + strict **delegate**
  to the existing `produce_stars_fast`/`drive_strict`. Gate:
  `psi_compatible(iex, iex_spec)` green on Horn/combinator/binarith/
  galaxy-entry + a deliberately-wrong `Delta(bogus)` negative the gate
  MUST flag + **KS-PROF: step count UNCHANGED vs iex_fast** (THE
  per-step-lever proof — if steps change, the specialisation is
  semantically wrong, not faster).
- **Σ2** combinator `Splice` (remove that delegation). Re-gate (same).
- **Σ3** wire `iex_spec` as the galaxy `eval_forced` tier; **KS-PROF
  galaxy Φ=405 before/after**: steps identical, wall ↓ (the
  find+freshen+fuse+unify+apply envelope collapses on the 392 δ-heads —
  expected well above the 2× `unify_fast` delta). Faithfulness:
  full gate suite green; reference `iex` untouched.

## 5. Sequencing & risks

- **Sequence (docs/16):** Σ(Φ) lands AFTER the in-flight `unify`/`find`/
  Stage-2-3 attribution work (so its KS-PROF delta is cleanly
  attributable, not confounded), and is **parallel-safe with the H-lever
  build** (KA2/interaction-net) — different files, both two-tier-gated.
  It is NOT a substitute for the H-lever and NOT on the
  galaxy-termination critical path; it is the compounding accelerator.
- **Risks:** (a) builder bug → `psi_compatible` deopt (defense-in-depth);
  (b) specialising past the strict/§49.50 boundary would be unfaithful →
  strict heads stay `Jet`→`drive_strict`, scoped to the objective
  confluent skeleton, `psi_compatible` catches a violation; (c)
  over-selling → §0 states plainly it does not make `data[0]` terminate;
  (d) GRIN native codegen explicitly rejected (breaks the trusted/deopt
  boundary for a per-step constant) — Σ(Φ) is an *interpreted closed
  table*, pure data, no binary/compile-time cost.

The honest one-liner: Σ(Φ) is the GraalVM/Truffle "interpreter-is-spec,
compiled-tier-is-the-specialisation" move (docs/07 §H), built on the
already-[Built] `build_accel`/`RayIndex` substrate, gated by the
already-proven `psi_compatible`, staged so every increment is
independently faithful and measured — and honestly scoped as the
companion, never the cure.
