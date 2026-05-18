# Engine perf audit — measured hot-path bottlenecks + top-3 wins

READ-ONLY, data-driven. Every number below is measured on this machine
(release build, `STELLA_KS_PROF=1`), darwin/Apple-Silicon, 2026-05-17.
Harness: `crates/stella-core/examples/perf_audit.rs` (added; pure
measurement, mutates no engine source) + the existing
`examples/galaxy_data_probe.rs`. Reference `iex` is the differential
oracle and is left untouched by every proposed win.

## 1. Measured phase tables (real numbers)

`[KS-PROF]` line = the env-gated `ks_report` (`interactive.rs:1446`).
`tot` = psics+find+freshen+fuse (the *instrumented* per-step kernel).
`wall` = end-to-end `Instant` around the `iex*` call.

### Galaxy `[triple]` entry, Φ = **405** stars (the canonical bench)

| tier | steps | wall | KS tot | psics | find (matchable of find) | freshen | fuse (unify / subst) |
|---|---|---|---|---|---|---|---|
| `iex_fast`   | 371 | **0.0674s** | 0.0181s | 0% | 29% (98%) | 5% | **66%** (9% / 7%) |
| `iex_spec` Σ(Φ) | 371 | **0.0517s** | 0.0016s | 2% | **98%** (94%) | 0% | **0%** |
| `iex_tabled` | 371 | 0.0757s | 0.0175s | 0% | 31% (98%) | 6% | 63% |

One full `eval_forced` of the same entry (`galaxy_data_probe`):
**106 `iex_fast` calls**, **42 of them do ≤2 steps**; sum of profiled
`tot` across all 106 = 0.1642s.

### Combinator SKK

| workload | tier | steps | wall | KS tot | find (matchable) | freshen | fuse |
|---|---|---|---|---|---|---|---|
| SKKx     | `iex` (ref) | 7 | 0.0003s | — | — | — | — |
| SKKx     | `iex_fast`  | 7 | 0.0001s | ~0 | 28% (87%) | 15% | 56% |
| SKK¹⁰x   | `iex_fast`  | 70 | 0.0010s | 0.0007s | 25% (93%) | 16% | 59% |
| SKK¹⁰x   | `iex_spec`  | 70 | 0.0004s | 0.0001s | **96%** (85%) | 0% | **0%** |

### binarith `add 999999 888888` (6594 steps)

| tier | wall | KS tot | **psics** | find (matchable) | freshen | fuse (unify/subst) |
|---|---|---|---|---|---|---|
| `iex` (ref) | **27.97s** | — | — | — | — | — |
| `iex_fast`  | 0.4058s | 0.3934s | **0.3204s = 81%** | 8% | 2% | 8% (6%/7%) |
| `iex_spec`  | 0.3907s | 0.3786s | **0.3060s = 81%** | 9% | 2% | 8% |

binarith `add 3 5` (23 steps, tiny): fuse 61%, find 24% — fuse-bound
when Ψ is small; psics-bound (81%) once Ψ grows.

`build_accel(Φ=405)` measured in isolation: **0.000393 s / build**.

## 2. Diagnosed bottlenecks (where time *actually* goes)

**A. `psi_csyms` is quadratic and dominates large runs (81%).**
`iex_fast_inner` (`interactive.rs:1372`) calls `psi_csyms(&psi)`
(`interactive.rs:439`) at the top of *every* step. It walks **every ray
of every star in the entire Ψ**, calling `ray_csym → term::get` per ray,
allocating a fresh `FxHashSet`. binarith `add` grows Ψ to thousands of
stars over 6594 steps ⇒ O(steps·|Ψ|) ≈ O(steps²) ⇒ **0.3204 s = 81 %**
of wall, dwarfing find+fuse+freshen combined. The resume-invariant
right below it (`prev_cs == psi_cs`, `:1378`) already proves the colour
set is *stable across most steps* — yet it is recomputed from scratch
every step before that check can use it.

**B. Galaxy pays `IexAccel::build(Φ=405)` 106× per `eval_forced`.**
`galaxy::eval_forced` (`galaxy.rs:945`) calls
`crate::interactive::iex_fast` inside a `loop`; `drive_strict`
(`galaxy.rs:761`) → `force_value` (`galaxy.rs:685`) → `eval_forced`
recurse, each calling plain `iex_fast`, and `iex_fast`
(`interactive.rs:1242`) rebuilds `IexAccel::build` (full Φ ray-walk +
per-ray `ray_colours` `HashSet<String>` alloc + `spec_star`) **every
call**. Measured: 106 calls × 0.393 ms = **~0.042 s of pure accel
rebuild ≈ 25 % of the 0.164 s total**, and 42 calls do ≤2 reduction
steps yet still pay the full Φ=405 rebuild. This is the exact
"per-call O(|Φ|) RayIndex rebuild" docs/07 (`308189f`, lines 79-81) and
docs/11 §B already identified — `build_accel`/`iex_fast_with_accel`
were *built and proven byte-identical* for precisely this, but the
galaxy host loop never adopted them.

**C. The profiled kernel is NOT where galaxy wall goes — `term::get`
lock+clone is.** Galaxy `iex_fast`: wall 0.0674 s but KS `tot` only
0.0181 s — **73 % of wall (0.049 s) is unattributed** to any phase.
Σ(Φ) collapses the profiled kernel 0.0181→0.0016 s (11×) yet wall only
0.0674→0.0517 s (1.3×): the real cost is *outside* the instrumented
psics/find/freshen/fuse boundaries. It is the pervasive
`term::get(id)` (`term.rs:306`): **one `TERM_STORE.read().unwrap()`
RwLock acquire + a full `TermData` clone (Arc<[TermId]> refcount
bump)** on *every* term-node inspection — 60 call sites across
unify/matchable/fp_unifiable/ray_polarity/subst.apply/collect_remap.
`Substitution::apply` (`subst.rs:47`, the galaxy fuse=66 % phase) does
`is_ground` (`term.rs:313`, another RwLock read) **plus** `get` per
node of galaxy's huge δ-bodies. The append-only store needs no
per-call lock for reads.

Within the profiled kernel, `matchable` is **93–98 % of `find`** on
galaxy/combinator — the discrimination index gets candidates down but
the per-candidate `matchable_fast` still walks terms via `get`.

Cross-ref: docs/07 (post-Stage-1b: unify 53→9 %, "`find` now dominant
~30 %"), docs/11 §A Fact-1 (galaxy ≈0.018 s, find ~5 ms) — consistent
with the **profiled** numbers here; this audit's new result is that the
**profiled kernel is no longer the wall** for galaxy (C) and that
**`psi_csyms` (A) is the true large-run dominator**, neither of which
the prior threads isolated.

## 3. Prioritized top-3 optimization plan

### WIN 1 — Incrementally maintain `psi_csyms` instead of O(|Ψ|)/step rebuild
- **Data:** binarith `add`: psics = **0.3204 s = 81 %** of 0.4058 s
  wall (largest single phase measured anywhere); galaxy 0 % only
  because Ψ stays tiny — the cost is purely Ψ-size driven and hits
  every accumulating-Ψ corpus (Horn, binarith, any non-trivial run).
- **Site:** `interactive.rs:1372` (`let psi_cs = psi_csyms(&psi);`) +
  `psi_csyms` `interactive.rs:439`; the consumer colour-gate is
  `mat_phi_c_accel`/`any_match_accel` (`:331`,`:367`).
- **Change:** maintain the `FxHashSet<Sym>` incrementally — seed once
  from initial Ψ, union the csyms of `produced` stars after
  `produce_stars_fast`, and (since stars are only removed/appended)
  the set is monotone within a stable-colour region. The existing
  `prev_cs == psi_cs` resume check (`:1378`) already assumes
  near-stability; this just stops recomputing the witness.
- **Expected:** removes ~81 % of binarith/Horn wall ⇒ **~4–5× on
  Ψ-growing corpora**; O(steps²)→O(steps) asymptotic. Galaxy
  unaffected (already 0 %) — no regression.
- **Faithfulness:** `psi_csyms` is pure observation of Ψ feeding only
  the colour-subset gate that `mat_phi_c_accel` *already proves
  identical* to reference `mat_phi_c`. Incremental set = same set ⇒
  byte-identical; stays behind `iex_fast_result_eq_iex` /
  `psi_compatible` + reference-`iex` oracle. Honest: the monotone
  argument must be checked against colour-*shrinking* (a star's only
  bearer of a colour being consumed) — if not provably monotone,
  fall back to recompute when the resume-invariant breaks (still
  O(steps) amortised, still identical set).

### WIN 2 — Galaxy: build accel once, drive with `iex_fast_with_accel`
- **Data:** 106 `iex_fast` calls per `[triple]` `eval_forced`;
  `build_accel(Φ=405)` = 0.393 ms ⇒ **~0.042 s ≈ 25 %** of the
  0.164 s total spent *only* rebuilding a pure-function-of-Φ
  structure; 42/106 calls do ≤2 steps (rebuild ≫ reduction).
- **Site:** `galaxy.rs:945` (`eval_forced` loop), `galaxy.rs:770/781`
  (`drive_strict`→`force_value`), `force_value` `galaxy.rs:685`.
  Target API already exists & is proven: `build_accel`
  (`interactive.rs:1262`), `iex_fast_with_accel`
  (`interactive.rs:1290`).
- **Change:** build `accel` once at the outermost `eval_forced`
  (where `TR_DEPTH==0`, alongside the existing `FORCE_MEMO` clear,
  `galaxy.rs:934`), thread it through `drive_strict`/`force_value`,
  call `iex_fast_with_accel(&accel, …)` everywhere.
- **Expected:** removes ~25 % of galaxy `eval_forced` wall directly;
  larger for image-payload forcing where the iex_fast-call count is
  far higher (the docs/11 KG6c blocker path) — strictly multiplies
  every galaxy throughput downstream.
- **Faithfulness:** `IexAccel` is a **pure function of Φ**;
  `iex_fast_with_accel(build_accel(phi),…)` is *proven byte-identical*
  to `iex_fast(phi,…)` (`iex_fast_with_accel_eq_iex_fast` test,
  `interactive.rs:2043`; the documented `308189f` reuse contract).
  Zero faithfulness risk — pure hoist. (Note: Σ(Φ) `iex_spec` already
  beats `iex_fast` on galaxy wall, 0.0517 < 0.0674 — Win 2 stacks
  with adopting `iex_spec_with_accel` on the same seam.)

### WIN 3 — Lock-free term reads: borrow/snapshot store, kill per-`get` RwLock+clone
- **Data:** galaxy `iex_fast` wall 0.0674 s vs profiled `tot`
  0.0181 s ⇒ **0.049 s (73 %) unattributed**; Σ(Φ) zeroes the
  profiled kernel but wall stays 0.0517 s — the residue is the
  cross-cutting `term::get` RwLock+`TermData`-clone (60 call sites)
  and `is_ground`'s second RwLock in `Substitution::apply` (galaxy
  fuse = 66 % of kernel; `matchable` = 93–98 % of `find`).
- **Site:** `term.rs:306` `get`, `term.rs:313` `is_ground`,
  `term.rs:284` `TERM_STORE` (`LazyLock<RwLock<TermStore>>`); hot
  consumers `subst.rs:47/52`, `polarised.rs` `matchable_fast`,
  `interactive.rs` `fp_unifiable`/`ray_polarity`/`collect_remap`.
- **Change:** the store is **append-only after intern** (`term.rs`
  module doc + `intern` only pushes). Provide a read path that does
  not take the global lock per node and does not clone `TermData`:
  e.g. a `with_term(id, |&TermData| …)` borrowing accessor, or a
  per-thread `Arc<TermStore>`-style epoch snapshot for the read-heavy
  engine loops (writers swap a new generation). Eliminates one
  atomic-lock + one Arc refcount round-trip per node walked.
- **Expected:** attacks the **73 % of galaxy wall** the profiler
  can't see and the `is_ground+get` double-lock in the fuse hot
  path; `[hypothesis]` ~1.5–2.5× galaxy wall (the unprofiled gap is
  measured at 73 %; the *fraction* of it that is lock/clone vs other
  unprofiled work — `psi.remove` O(|Ψ|), `mat` sort/alloc — is not
  yet isolated, so the multiplier is a hypothesis, the *gap itself*
  is measured). Recommend a cheap confirming probe first: wrap
  `term::get` body in a `T_GET` `ks_add` slot and re-run galaxy
  `[triple]` (one-line instrumentation, same pattern as `T_UNIFY`).
- **Faithfulness:** read semantics must be **identical** — same
  `TermData` for the same `TermId` (store is immutable post-intern,
  so a borrow/snapshot is value-identical). Pure mechanical access
  change, no algorithm/result change; gated by the full existing
  test battery + reference-`iex` oracle (no `psi_compatible`
  relaxation needed — this is byte-identical, not α-slack).

## Priority rationale
1. **Win 1** — largest single measured phase (81 %), removes a
   quadratic, byte-identical, ~5 lines, biggest leverage on the
   broadest corpus class.
2. **Win 2** — 25 % of galaxy measured, *zero* faithfulness risk
   (proven-identical API already exists), small wiring change,
   compounds with Σ(Φ).
3. **Win 3** — attacks the 73 % the profiler cannot see (the real
   galaxy wall); highest ceiling but the multiplier is `[hypothesis]`
   pending the one-line `T_GET` probe, and it is the largest
   mechanical change — so third.
