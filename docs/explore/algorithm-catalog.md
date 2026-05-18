# Algorithm Catalog — concrete techniques NOT yet in tree, prioritized

READ-ONLY mining of the Eng papers + cited literature + the live codebase.
Goal: techniques that could improve **speed**, **expressiveness**, or
**theory**, each with a precise plug-in point and an honest verdict.

## Closed-arc guardrails (do NOT relitigate)

- **Galaxy faithful-reproduction as an N-KA-cover negative is CLOSED**
  (docs/16 §7). `data[0]` exhibits, on every faithfully-instrumented axis,
  no exploitable redundancy and no foldable recurrence; the AEx-faithful
  diagnosis is provably intractable.
- **docs/12 interaction-net** and **docs/13 KA2** are EVIDENCE-NEGATIVE
  *as galaxy termination-crossers* (`c8cb09e` H1 ratio≡1.00; calibrated
  `detect_recurrence` H2 `distinct≡len`). They must NOT be re-proposed as
  such. A technique may still earn a verdict on **other** merit (raw
  throughput on the combinator/binarith fragments; expressiveness; the
  past-Eng χ track) — that framing is stated explicitly per row below.
- **Lever C** (closed-`TermId` NF memo) shipped + proven (`b6c65d5`),
  measured-negative on `data[0]`. **Σ(Φ)** Σ0/1/2 shipped + proven
  (`016e8ee`/`224d602`/`90f34c0`) — the per-step companion, never the
  cure. `unify_fast` shipped (Stage 1b `f5e845c`, galaxy Φ=405 ≈2.0×,
  unify 53%→9%).
- Faithfulness invariant is fixed: every fast tier is a sibling of
  reference `iex`/`eval_forced`, gated by `faithfulness::psi_compatible`
  (`faithfulness.rs:115`) + (for pure-KAM corpora where conceal is
  near-vacuous) per-step `stars_alpha_equiv` vs `iex_fast`, with deopt to
  reference on a red gate. No new trusted code on the faithfulness path.

Tags: **[Built]** in tree · **[Lit]** paper/literature · **[Proto]** our
construction. Faithfulness-risk column: *behind-gate* = sits behind
psi_compatible+deopt, semantics unchanged; *semantic* = changes what is
computed (needs its own proof).

---

## Group 1 — Per-step speed (bounded by docs/11 Fact-1; ≤ ~|Φ|-shaped)

| # | Technique | What it buys | Plug-in point (file:line) | Cost | Faith-risk | Verdict |
|---|---|---|---|---|---|---|
| 1.1 | **Discrimination / substitution tree index** over Φ negative rays (replace the `(SymName,Polarity)` first-symbol bucket + per-candidate `fp_unifiable`) | `find` is the measured dominant phase (~30%, docs/07 §D after unify_fast). First-symbol index returns a bucket then does O(bucket) `fp_unifiable`+`matchable_fast`; a depth-k discrimination tree (Graf/McCune; the standard ATP index) prunes on nested functor path, not just head — on galaxy Φ=405's 392 δ-heads keyed by `:N` atoms it collapses the bucket to ~1. Removes most of the `fp_unifiable`+`matchable_fast` calls inside `mat_phi_c_accel`/`any_match_accel`. | `index.rs:68` `RayIndex` (add a `DiscTree` variant); consumed at `interactive.rs:341` (`mat_phi_c_accel`) and `:376` (`any_match_accel`); built in `IexAccel::build` `interactive.rs:295` (pure fn of Φ, same lifetime as `RayIndex`) | medium (a correct discrimination tree + oracle-equivalence test mirroring `index.rs` `assert_oracle_equiv`) | behind-gate — pure speed, "same matchable set as the O(n²) scan" is exactly the existing `RayIndex` oracle contract; `fp_unifiable` stays the soundness backstop | **do-now** — the single highest-leverage *bounded* lever; it is the named "next KS lever" (docs/07 §D, docs/09 §E) and has a ready oracle harness. Capped at the §A Fact-1 wall (≤~1.05× of *galaxy* total alone) but it is the largest unclaimed per-step win and compounds with Σ(Φ). |
| 1.2 | **Imperative union-find with rank + in-place path-halving** in `unify_fast` (replace `FxHashMap<Var,Bound>` resolve/compress) | `unify_fast` already triangular+deferred-occurs (near-linear) but every `resolve` does `FxHashMap` probes and rebuilds a `path: Vec`. A dense `Vec`-indexed UF over a per-solve `Var→u32` densifier with union-by-rank gives true α(n) amortized + kills the per-resolve `Vec` alloc and hashmap hashing. Pure constant-factor on the (now 9%) unify phase. | `unify_fast.rs:38` `Solver`/`resolve`/`bind` | low–medium | behind-gate — result-equivalence is the existing 3000-fuzz vs `unify` oracle (`unify_fast.rs:392`) | **staged** — real but the phase is already 9%; do *after* 1.1 to keep KS-PROF attribution clean (docs/09 staged-falsifier discipline). Honest ceiling: a fraction of 9%. |
| 1.3 | **Two-finger / Paterson–Wegman-style linear unification** as the unify kernel | Paterson–Wegman 1978 is true O(n+m) (vs almost-linear triangular+deferred-occurs). | `unify_fast.rs` whole module | medium | behind-gate (same fuzz oracle) | **rejected-for-now** — `unify_fast` is *already* almost-linear with DAG memo; PW's constant factors are worse on the small terms the engine actually unifies (galaxy rays are shallow). No measured headroom; 1.2 captures the realistic win. |
| 1.4 | **Lock-free / append-only term store** (replace `RwLock<TermStore>`; `get` takes a global read lock per node visit — every `term::get` in the hot loop) | Removes `RwLock` acquire on the read-mostly `get`/`is_ground`/`mk` hot path. This is docs/07 §D "lock-free get / append-only stable store (B3)". | `term.rs:284` `TERM_STORE`, `get` `:306`, `mk` `:291` | medium (arena + atomic publish; or `boxcar`/`elsa` append-only vec) | behind-gate — representation only, `TermId` semantics unchanged | **staged** — docs/07 §D / docs/10 RE-HOMED this as the OHG array substrate, sequenced strictly AFTER KS Stage-1 attribution; do it *as* the docs/10 array refactor, not a standalone lock swap (else the Φ=405 attribution is destroyed). Constant-factor (docs/16 §1: cannot cross a termination boundary) — single-thread engine sees modest win; real payoff is enabling 1.5. |
| 1.5 | **Data-parallel layered rewriting** (Wilson–Zanasi/open-hypergraph: `kahn`-layer the independent redex fan, rayon over a layer) | docs/10 constant-factor multiplier on the post-unifier profile; amplifies Lever-C's deduped independent forces. | `interactive.rs:1376` the `'outer` redex-selection scan + `produce_stars_fast` `:1153` | large (OHG array substrate + the kahn/semaphore-adjacency question) | behind-gate, but the **§49.50 semaphore-edge-as-adjacency** encoding is the open ceiling question (docs/07 §D) | **research** — explicitly a constant-factor lever (docs/11 §G, docs/16 §1); composes *after* the structural levers, never subsumes. Ceiling unknown pre-Stage-0; restricted to the objective/Horn+δ fragment if the semaphore edge can't be cheaply made adjacency. |

---

## Group 2 — Algorithmic / asymptotic (the only class that can change a complexity class)

| # | Technique | What it buys | Plug-in point | Cost | Faith-risk | Verdict |
|---|---|---|---|---|---|---|
| 2.1 | **Incremental / online whistle: replace the O(n²) `detect_recurrence` double loop with an embedding-indexed scan** (e.g. bucket trace states by `canonical` head+size signature; only compare candidates that can embed) | `accel_detect.rs:94` is `for j in 1..n { for i in 0..j { embeds(t[i],t[j]) } }` — O(n²) `embeds` calls, each itself a tree walk. The χ-track Stage-1 trace and any future long trajectory pay this. An online signature bucket (size/head-multiset is monotone under `⊴`) prunes the inner loop to embedding-plausible predecessors. `detect_in_window` already trades precision for O(window); this keeps full precision at ~O(n·b). | `accel_detect.rs:94` `detect_recurrence` | low–medium | behind-gate — observational by construction (module doc); a test pins identical whistle vs the O(n²) reference | **staged** — pure speed on an *already-built, calibrated* instrument; matters only once a trace is long (χ Stage-1/2). Not on a galaxy critical path (galaxy arc closed). Do it when the χ trajectory length forces it; cheap and self-oracling. |
| 2.2 | **E-graph / congruence-closure equality saturation (egg-style) for the observational-equivalence corpus** the differential oracle accumulates | docs/07 §G: synthesize HOL/KA2 lemmas later from the obs corpus via *directed lemma synthesis* (CCLemma). An e-graph over the `ObsRecord` corpus (`faithfulness.rs`, the §G substrate) gives canonical-form clustering + rewrite-rule discovery feeding the deferred verified substrate. | `faithfulness.rs` `ObsRecord` (delivered inert per docs/07 §J2); offline analysis harness, not the engine | medium (pull `egg`; offline only) | none (offline; never on the engine path) — *semantic only if* a discovered rule were promoted to a jet, which would then go through the existing KA2 differential gate | **research** — the literature-endorsed defer-and-accumulate strategy (docs/07 §G). Zero engine-merit *now*; legitimate once the obs corpus is large. Not a present lever. |
| 2.3 | **Supercompilation / distillation (Hamilton) as a whole-Φ optimizer** producing a residual constellation | Superlinear speedup *in principle*. | offline Φ→Φ′ transformer feeding `iex` | large | semantic (changes Φ) — would need full psi_compatible certification of Φ′≡Φ | **rejected-and-why** — docs/13 + docs/16 §7: KA2 (the tractable fold fragment of this) is evidence-negative on the only heavy workload (galaxy); full distillation is a far larger build for a workload measured non-recurrent. No evidence of a real recurrence to distill. Closed by measurement, not omission. |
| 2.4 | **Interaction-combinator (Lafont/HVM2) net runtime** for the binder-free combinator/binarith fragment | Eng §53.6 explicitly conjectures stellar resolution ≈ Lafont nets on the *objective polarised fragment*; HVM2-style net reduction shares **redexes** not just subterms — genuine asymptotic win where fan-out duplicates work. | a new sibling runtime over `combinator::machine_stars` / `binarith` | large (new net runtime) | semantic — own simulation proof + psi_compatible | **research (NOT as galaxy crosser)** — docs/16 §7 forbids re-proposing this as a galaxy termination-crosser (H1 ratio≡1.00). *Legitimate* open question on raw throughput of the S/B/C combinator fragment and as the Eng §53.6 "interesting to connect" theory contribution — but only if a *measured* duplicated-redex-family signal appears on a non-galaxy workload first (measure-don't-guess; the H1 probe is reusable, `c8cb09e`). |

---

## Group 3 — Past-Eng / χ track (engine-merit-justified; docs/08, the live frontier)

| # | Technique | What it buys (theory) | Plug-in point | Cost | Faith-risk | Verdict |
|---|---|---|---|---|---|---|
| 3.1 | **Mazurkiewicz trace-monoid quotient + Foata normal form** over the §4.1 event alphabet `Σ = {R(c)} ∪ {F(op,ℓ)}` with the §4.2 independence relation `I` | docs/08 §4: makes §49.55 idempotence *expressible* (a free monoid cannot: `w·w≠w`) and preserves §49.50 semaphore dependency. The Foata height per layer is the structural carrier of χ (§4.4). This is the theory closure the χ programme needs at Stage-2. | new module consuming Stage-0's event log; `χ` computed from the dependency DAG using `antiunify::{canonical,embeds,occurs_alpha}` (already built); χ-locus is the `subjective::subjective_stream` trajectory (docs/08 §4.7 MEASURED), NOT `eval_forced`'s `final_ray` | medium (a trace-monoid/Foata implementation — but small per docs/08 §5: "no monoid library until a stage demands it") | behind-gate / observational until docs/08 Stage-4; Stage-4 acceleration is differential-certified vs unrolled `iex` | **staged** — gated on docs/08 Stage-1 confirming idempotence-loss⟺whistle. Apparatus exists + is θ-calibrated; Stage-0 holds; open target is a *sustained-non-idempotent faithful fixture* (docs/08 §4.8). The thesis-nearest deep track; do *not* build the monoid before Stage-1 (docs/08 §7). |
| 3.2 | **§67.10 theorem-certified cut-elimination as the ground-truth differential oracle** for the whistle/χ machinery | docs/thesis-audit/00 step 5 / docs/16 §7 step 4: §67 has a *theorem-certified* normal form — the one place a true SN trajectory exists to calibrate `detect_recurrence` specificity (already done: zero false-positive whistle, `f634f61`). Extending it to *sensitivity* (a certified *non*-SN family) is the missing calibration half. | `mll.rs` cut-elim (`cut_elim`) → `accel_detect` trajectory tap | low–medium | observational | **do-now (theory)** — specificity is established; the catalog's recommendation is to add the **sensitivity** anchor (a certified divergent cut family) so the χ instrument is two-sided-calibrated before Stage-2 trusts it. Cheap, self-contained, unblocks 3.1. |
| 3.3 | **GoI token-machine χ readout: instrument `σu` nilpotency-degree directly** (docs/15 §1–4 / docs/08 §4.6) | Eng §49.57 *verbatim* equates hyperexec idempotence with GoI nilpotency. χ ≡ count of token transitions on non-cancelling feedback paths = distance of `σu` from nilpotent. Gives χ an Eng-grounded *meaning* (not just a postulated functional) and *derives* the two boundary conditions §4.5 had to assume. | `mll2i.rs` (the MLL→interaction / GoI substrate) + the subjective_stream tap | medium | observational | **staged** — the theory side is already folded (docs/08 §4.6, `b42c290`); the *measurement* (read χ as σu non-nilpotency on the calibrated subjective_stream) is the sharpened Stage-2. Sequenced with 3.1; same gate. Strongest theory contribution to Eng (operationalizes §49.57). |

---

## Group 4 — Expressiveness

| # | Technique | What it buys | Plug-in point | Cost | Faith-risk | Verdict |
|---|---|---|---|---|---|---|
| 4.1 | **Genuinely-stellar fully-general signed arithmetic** (replace the disclosed host-i128 signed layer in `sbinarith`) | `sbinarith` magnitude is stellar but the **signed** layer is host i128 with a hard 128-bit ceiling (`neg` 100% host; galaxy-scale magnitudes silently `None`). A stellar signed kernel removes the disclosed ceiling → galaxy-scale arithmetic stops silently bottoming out. | `sbinarith.rs` signed layer (per-site `// HOST:`/`// CEILING:` markers); consumed by `galaxy.rs:drive_strict` | medium | behind-gate — the native kernel is a *legitimate disclosed intrinsic* (docs/07 §B KG4b, user-locked: NOT a violation). This is a planned *generalization*, not a correctness fix | **staged** — the "KS stream" (docs/07 §D / NEXT-4). Explicitly NOT a blocker; real expressiveness gain (unbounded magnitudes) and removes a disclosed ceiling. Engine-merit-justified independent of galaxy. |
| 4.2 | **KAM call/cc (Save/Restore) stars** — Eng §57.19's full encoding incl. continuations | Eng §57.19 defines Push + Grab + **Save/Restore for cc**; the built galaxy KAM uses Push/δ/combinator only. Adding Save/Restore makes the engine able to run the *full* KAM Eng specifies (call/cc programs), closing a faithfulness-completeness gap vs §57. | `combinator.rs:147` `machine_stars` / `galaxy.rs` prim stars | medium | semantic (new stars) but additive — psi_compatible-gated, reference `iex` runs them too | **rejected-for-now** — docs/thesis-audit/00 "out of scope: KAM call/cc (binder-free galaxy.txt doesn't need it)". No driving workload needs it; would be expressiveness for its own sake. Record as a known §57-completeness gap, do not build. |
| 4.3 | **Generalised structural rules / n-ary contraction** (Eng §29.26, Danos–Regnier) to recover canonicity lost by binary contraction trees in the MLL infra | Eng §29.26: binary contraction links build non-canonical trees; an n-ary `?`-link merging recovers canonicity. Would make `mll.rs` proof-net normal forms canonical (fewer spurious distinct NFs → tighter psi_compatible classes). | `mll.rs` structural-rule handling | medium | semantic (changes proof-net NF) — needs its own equivalence proof vs current `cut_elim` | **research** — a genuine theory/expressiveness improvement Eng explicitly names, but `mll.rs` is not on a current critical path; the cut-elim oracle (3.2) is the load-bearing use of that module. Worth recording; not now. |

---

## Cross-cutting notes

- The **only** asymptotic levers are Group 2; Groups 1/3/4 are bounded
  per-step / theory / expressiveness. Group 2 is almost entirely
  rejected-or-research **by prior measurement** (galaxy arc closed) — the
  honest state is that there is *no* known unexploited asymptotic lever on
  the measured workload. New asymptotic claims require a *new measured*
  redundancy/recurrence signal first (the H1/H2 probes are reusable).
- Sequencing constraint (docs/09/10 staged-falsifier): land one per-step
  lever at a time with its own KS-PROF Φ=405 before/after attribution.
  **1.1 first** (largest unclaimed bounded win, has an oracle harness),
  then 1.2, then the docs/10 substrate (1.4/1.5 together).
- The χ track (Group 3) is the genuinely-open frontier and is
  engine-merit-justified (docs/16 §7 pivot); 3.2-sensitivity is the
  cheapest unblocking move there.

---

## TOP 5 highest-leverage (technique · buy · plug-in)

1. **Discrimination/substitution-tree index over Φ negative rays**
   (#1.1) · collapses the measured ~30%-dominant `find` phase: on galaxy
   Φ=405's 392 δ-heads it cuts candidate buckets to ~1, removing most
   `fp_unifiable`+`matchable_fast` calls · `index.rs:68` `RayIndex` (new
   `DiscTree`), consumed at `interactive.rs:341`/`:376`, built in
   `IexAccel::build` `interactive.rs:295`; reuse `index.rs`
   `assert_oracle_equiv` as the gate.

2. **§67.10 cut-elim sensitivity calibration anchor** (#3.2) · adds the
   missing *sensitivity* half (a theorem-certified *divergent* family) to
   the already specificity-calibrated `detect_recurrence`, two-sided-
   calibrating the χ instrument before Stage-2 trusts it · `mll.rs`
   `cut_elim` → `accel_detect` trajectory tap.

3. **Mazurkiewicz trace-monoid + Foata-height χ** (#3.1) · the theory
   closure that makes §49.55 idempotence expressible and carries χ;
   the thesis-nearest deep track · new module over docs/08 Stage-0
   event log on the `subjective::subjective_stream` χ-locus, using
   already-built `antiunify::{canonical,embeds,occurs_alpha}`.

4. **Imperative dense union-find (rank + path-halving) in `unify_fast`**
   (#1.2) · true α(n) + removes per-`resolve` `FxHashMap` probes and the
   `path: Vec` alloc on the (now 9%) unify phase · `unify_fast.rs:38`
   `Solver`; gated by the existing 3000-fuzz vs `unify`
   (`unify_fast.rs:392`).

5. **Genuinely-stellar fully-general signed arithmetic** (#4.1) ·
   removes the disclosed host-i128 128-bit ceiling so galaxy-scale
   magnitudes stop silently `None`-ing — real expressiveness, the
   "KS stream" · `sbinarith.rs` signed layer (the `// HOST:`/`// CEILING:`
   marked sites), consumed by `galaxy.rs:drive_strict`.
