# explore — data-parallel / batched reformulation of the hot loops

Read-only exploration. No code changed. Scope per the brief: throughput on
the things that *run*. Out of scope (settled): galaxy `data[0]` is the
closed N-KA-cover negative (docs/16 §7) — not a termination question.
Faithfulness invariant assumed throughout: reference `iex`/`unify` =
oracle; any fast path sits behind `faithfulness::psi_compatible` + deopt
(`interactive.rs:1527` `iex_fast_concealed`, the existing two-tier seam);
honest negatives first-class.

Profile anchor (docs/09:13-17, docs/10:163-166, `STELLA_KS_PROF` on the
galaxy Φ=405 reduction): `fuse ≈ 82%` of wall, of which `unify ≈ 53%` of
total and `subst ≈ 5%`; `find ≈ 15%`; `freshen ≈ 3%`. The instrumentation
is live in-tree (`interactive.rs:1446-1463` `ks_report`, the `T_UNIFY` /
`T_SUBST` / `T_FIND` / `T_FRESH` counters).

A prior design doc already covers most of this ground honestly:
`docs/10-open-hypergraph-data-parallel-reframe.md`. This exploration
verifies its claims against current source (and the unpacked
`open-hypergraphs 0.3.1` crate) and adds the per-loop verdict table the
brief asks for. docs/10's conclusions hold; nothing here relitigates them.

---

## Per-loop verdict

### 1. `unify` — `unify.rs` reference / `unify_fast.rs` union-find

`unify_fast_with` (`unify_fast.rs:110-194`): worklist `Vec<(TermId,TermId)>`
+ `Solver{parent: FxHashMap<Var,Bound>}` triangular union-find with path
compression (`unify_fast.rs:53-86`), a `(TermId,TermId)` visited memo
(`unify_fast.rs:130-148`), one deferred acyclicity DFS
(`store_has_cycle`, `unify_fast.rs:239-286`), one materialise pass
(`deep_resolve`, `unify_fast.rs:205-231`).

- **Data-parallelisable: NO.** This is the real serial wall. A single
  Martelli–Montanari / union-find unification is P-complete (the
  unification problem is log-space-complete for P — Dwork–Kanellakis–
  Mitchell). The worklist loop at `unify_fast.rs:132-169` carries a true
  data dependency: each `s.bind` (`:154,:157,:158`) mutates the UF store
  that the *next* iteration's `s.resolve` (`:138-139`) reads. Path
  compression (`:74-75`) is the textbook serial-bottleneck of union-find;
  parallel union-find (concurrent wait-free UF, Jayanti–Tarjan) exists but
  its lower bounds and constant factors make it a loss at the term sizes
  here, and it would not be the *same* MGU traversal the oracle expects.
- Reformulation: none faithful. SIMD-decomposing one `App`/`App` arg
  vector (`:163-165`) is theoretically vectorisable but the arg fan is
  tiny (galaxy KAM rays are low-arity `st`/`P`/`dot`) — no payoff.
- Speedup class: none.
- Faithfulness risk: high if attempted (different MGU traversal, occurs
  semantics); the existing differential fuzz (`unify_fast.rs:392-449`)
  would catch divergence but a parallel UF is unlikely to pass it
  cleanly.
- Build cost: large; verdict **NO — fundamentally serial.** This is the
  53%-of-wall hottest kernel and it does not parallelise *internally*.
  docs/10:170-174 says exactly this and is correct. The only lever on
  `unify` is *across independent unifications*, not inside one (see #3).

### 2. `find` — `any_match_accel` candidate scan

`iex_fast_inner`'s selection scan (`interactive.rs:1376-1387`) →
`any_match_accel` (`interactive.rs:361-389`) over
`accel.idx.candidates(name,pol)` (`index.rs:100-103`, a `&[RayId]`
bucket), each candidate gated `fp_unifiable && matchable_fast`
(`interactive.rs:382`).

- **Data-parallelisable: PARTIAL (per-redex, embarrassingly so).** The
  candidate loop `for &(i,j) in accel.idx.candidates(...)`
  (`interactive.rs:376-387`) is a read-only filter over a flat slice with
  no inter-candidate dependency — a textbook `gather` + predicate-filter,
  exactly the array shape `kahn`/`bincount` express
  (docs/10:184-187). `fp_unifiable` (`interactive.rs:401-418`) is a
  branch-heavy one-level arity/functor check — SIMD-hostile per element
  but trivially rayon-`par_iter().any()`-able across the bucket.
- Reformulation: `par_iter` over the candidate bucket (existence:
  `.any()`; enumeration in `mat_phi_c_accel:341-350`: `par_iter` +
  `.collect()` then `sort_unstable` — sort already present, so order
  faithful). SIMD form: pack head-name/polarity/arity into a struct-of-
  arrays per bucket and vector-compare the `fp_unifiable` prefilter.
- Speedup class: ≤ #cores on the ~15%-of-wall `find` slice, only when
  buckets are wide (galaxy ~400 δ-stars ⇒ wide head buckets — favorable;
  Horn add ⇒ 1-2 per bucket ⇒ negative/noise). Amdahl ceiling on `find`
  alone ≈ 15% → realistically a few % of total.
- Faithfulness risk: LOW. The scan is pure; `mat_phi_c_accel` already
  `sort_unstable`s its result (`interactive.rs:350`) so output order is
  deterministic regardless of evaluation order; the *selection* (first
  `(i,j)`, `interactive.rs:1382-1385`) is a `break 'outer` that must
  still pick the leftmost — so parallelism is *within* a star's ray scan
  / *within* a bucket, not across the `i` loop that defines leftmost.
  Gated by the existing `psi_compatible` either way.
- Build cost: small (add `rayon`, one `par_iter`). Verdict **PARTIAL —
  real but secondary; modest, galaxy-shape-dependent.**

### 3. The step summand-fan — `produce_stars_fast` / `interaction_step`

`produce_stars_fast` (`interactive.rs:1153-1208`): for each matched
`(ik,jk)` from `mat_phi_c_accel`, do `alpha_rename_star_fast` + `fuse_fast`
(α-rename + one unify + `theta.apply`), `produced.push`. Then the
self-interaction loop (`:1201-1205`). `interaction_step`
(`interactive.rs:626-650`) is the reference analogue.

- **Data-parallelisable: YES (the genuine lever).** Each summand is an
  *independent* fusion: distinct fresh α-renaming (the `*counter`
  increments are the only shared mutation, `interactive.rs:1170,1188`,
  and are pure-counter — trivially privatisable by pre-assigning disjoint
  counter ranges per candidate), independent `unify`, independent
  `theta.apply` over disjoint residual rays, independent
  `produced.push`. This is precisely docs/10:177-191's claim and it
  checks out: the summand fan is one Wilson–Zanasi independent layer.
  Each summand *contains* a serial unify (#1) but the summands *across*
  the fan run in parallel — this is the only place the 53% `unify` cost
  gets any parallel relief at all (N independent unifies on N cores), and
  it folds in the 5% `subst` and 3% `freshen` slices for free (they are
  per-summand, embarrassingly parallel — `theta.apply` over residual
  rays, `interactive.rs:493-507`).
- Reformulation: `mat_phi_c_accel(...).into_par_iter().filter_map(|(ik,jk)|
  fuse_fast(...))` with per-summand private counter ranges; collect to
  `produced`. The OHG framing (docs/10 §2.1) is the same thing viewed as
  one layered-rewrite batch; the practical Rust form is `rayon` over the
  match vector — no library dependency needed.
- Speedup class: up to min(#cores, fan width) on the *whole step body*
  (`fuse` = 82% of wall), gated by fan width. Galaxy: ~400 δ-stars but
  the per-step *matched* fan is what matters — needs measurement (docs/10
  Stage 0's second falsifier), but this is the only loop where the
  dominant cost is actually exposed to parallelism.
- Faithfulness risk: MEDIUM, fully containable. Reordering summands
  changes `psi.extend` order (`interactive.rs:1429`) and the per-summand
  fresh-variable names (the `counter`, `interactive.rs:1170`). The
  existing gate is built for exactly this: `psi_compatible`
  (`faithfulness.rs`) is an α-canonical *multiset* result-equivalence
  validator (docs/10:258-301, P-OHG), and `iex_fast` is already only
  result-equivalent (not byte-identical) to reference `iex` —
  `iex_fast_result_eq_iex` (`interactive.rs:1803`) is the existing
  oracle test. Counter ranges must be pre-partitioned per candidate to
  keep fresh names collision-free and the multiset stable; with that, the
  reorder is a confluent-fragment reordering the existing instrument
  already certifies (and deopts to reference `iex` where it goes red —
  the non-confluent subjective/forcing corpora, docs/10:278-289).
- Build cost: small-to-medium (rayon, counter-range partition,
  thread-safe `produced` collect; the term store is `Arc`-shared
  immutable hash-cons `term.rs:218-221` so reads are safe, but
  `mk_app_interned` interning under contention needs checking — the
  store is currently behind a `RwLock`, docs/10:215). Verdict **YES —
  the single most promising loop.**

### 4. `iex_fast_inner` outer step loop

`interactive.rs:1362-1438`: `while steps < fuel { scan → select (i,j) →
psi.remove(i) → produce → psi.extend → resume_from = i }`.

- **Data-parallelisable: NO.** Hard sequential recurrence: step k+1's
  selection scan (`interactive.rs:1376`) reads the `psi` that step k
  mutated via `psi.remove(i)` (`:1398`) + `psi.extend(produced)`
  (`:1429`), and the `resume_from` cursor (`:1433`) + `prev_cs` colour
  set (`:1434`) are loop-carried optimisation state. This is the
  Mazurkiewicz-trace *dependency* relation, not the independence relation
  (docs/10:110-119, §3(c)) — it is a reduction *strategy*, not a
  representation, and OHG layering *consumes* it as input, does not
  generate it. Speculative multi-step (HVM2-style) would reorder
  reductions across the leftmost-selection that defines the reference
  result and is not faithful outside the confluent fragment.
- Verdict **NO — sequential rewrite-dependency wall.** (Parallelism lives
  one level down, inside the step body — loop #3 — not across steps.)

### 5. `saturated_diagrams_with_strategy` — the docs/16 §7 explosion

`execution.rs:158-295`: DFS over a `stack: Vec<DiagBuilder>`
(`:169-177`), each pop expands every free ray × every adjacency neighbour
× every existing/new vertex (`:183-245`), cloning a `DiagBuilder` per
candidate (`:201,:224`), gated by a *global shared* `visited:
HashSet<String>` (`:204,:228`) and `saturated_keys` (`:250`).

- **Data-parallelisable: PARTIAL, but it is the WRONG computation.** The
  stack-of-builders DFS is structurally a parallel tree/work-stealing
  search (rayon `Scope` / a Treiber-style concurrent worklist); the
  per-builder candidate-generation loop (`:183-245`) is independent
  per-builder. *But* docs/16 §7.3 (`f96b452`) **measured** reference
  saturated-diagram AEx (`aex_full`, `aex_seminaive_full`, copy-free
  `aex`) to be intractable on `machine_stars + [+P(st(x,ε))]`: the 7 KAM
  stars are mutually matchable ⇒ the enumeration explodes with *zero*
  reduction. The explosion is not embarrassingly parallel work worth
  doing faster — it is super-exponential in the saturation closure with
  the answer already known to be intractable; parallelising it buys a
  constant on a doubly-exponential, and docs/16's own verdict
  (`combinator.rs` doc + Eng §57.13) is that this path is not
  dischargeable via reference AEx at all. The global `visited`/
  `saturated_keys` `HashSet` also serialises the dedup that is doing the
  pruning — making it concurrent (DashMap) would change the visitation
  order and the dedup outcome, a faithfulness hazard for a computation
  that is not on any live hot path.
- Faithfulness risk: HIGH (shared `visited` dedup order is semantically
  load-bearing for which saturated set is produced) for ~zero benefit.
- Verdict **NO (do not) — embarrassingly parallel in form, but the
  wrong computation (measured-intractable, docs/16 §7.3); parallelism
  here accelerates a known dead end.**

### 6. `RayIndex` / `DepGraph::build_indexed` build

`index.rs:76-93` (`RayIndex::build`: one pass over `id_rays`, bucket
push) and `index.rs:116-154` (`build_indexed`: per-ray candidate scan +
`matchable`, dedup via `seen: FxHashSet`).

- **Data-parallelisable: PARTIAL.** `RayIndex::build` is a classic
  parallel bucket-by-key (map then merge / `bincount`-shaped). Build
  itself is one-shot, *not* in the per-step hot path (built once per
  fixed Φ, `IexAccel::new` region near `interactive.rs:300-310`); it
  does not appear in the `STELLA_KS_PROF` envelope at all.
- Speedup class: irrelevant — not hot. Verdict **PARTIAL but NOT WORTH
  IT — not on the measured hot path; the per-step `candidates()` slice
  read is O(1) already.**

### 7. Σ(Φ) — `spec_phi.rs`

`spec_phi.rs` builds a closed head-keyed `FxHashMap<String,Transition>`
(`:54-57`) once per fixed Φ; a step becomes an O(1) head lookup + one
node splice (`:1-28`). This is the *per-step constant-factor* lever
(docs/14, shipped per docs/16 §7). It is a serial-cost *eliminator*, not
a parallel reformulation: it removes scan/rename/unify/apply for δ/Push/
Splice heads rather than parallelising them. Orthogonal to and
compounds with #3. **N/A as a data-parallel target — it is the better
move on the per-step axis and is already in tree.**

---

## The open-hypergraph angle — honest take

- The path the brief pointed at, `~/hellas/open-hypergraph`, **does not
  exist** on this machine. But `open-hypergraphs = "=0.3.1"` *is* a real
  dependency (`crates/stella-core/Cargo.toml:7`) and is exercised by a
  smoke test only (`lib.rs:55,61`, lax `OpenHypergraph`/`Hyperedge`).
- I verified docs/10's library claims against the unpacked crate source
  (`~/.cache/lcrio/unpacked/open-hypergraphs/0.3.1/`). They hold:
  `strict::layer::layer` is a data-parallel Coffman-Graham/Kahn layering
  (`src/strict/layer.rs:20-31`); `graph::kahn`
  (`src/strict/graph.rs:54-129`) is genuinely array-parallel —
  `scatter_assign_constant` / `scatter_sub_assign` / `gather` / `filter`
  over flat integer arrays, BFS-by-indegree with no pointer chasing, the
  executable Foata-normal-form of the trace monoid. The `Hypergraph` is
  four parallel arrays + CSR `IndexedCoproduct` as docs/10:32-50 states.
- **Confirmed blocker docs/10:412-424:** the rewrite machinery a real
  reframe needs — `apply_smc_rewrite`
  (`src/strict/open_hypergraph/rewrite.rs:175`), `pushout_along_span`
  (`src/strict/hypergraph/object.rs:166`) — is `#[cfg(feature =
  "experimental")]` (`src/strict/open_hypergraph/mod.rs:3-10`,
  `object.rs:7,166`). The stable surface is layering + eval + lax
  construction only.
- Faithful fit, but bounded: OHG models the **objective/Horn confluent
  fragment as a static diagram** and a **per-AEx-layer snapshot of the
  subjective fragment** — it does **not** model §49.50 ray-minting /
  semaphore order (docs/10:84-126, §3(c)); those are a reduction
  *strategy* the OHG algebra consumes as input, not generates. `mll.rs`
  itself flags OHG-SMC rewriting as the *deferred* §67 cut-elim home
  (`mll.rs:44-54`: "deferred because the lax representation does not
  expose a full SMC category … `matches`/`rewrite` absent from 0.3.x") —
  consistent with the experimental-gating finding.
- **Verdict: interesting-but-not-here as a *substrate reframe*; the
  genuinely useful kernel of it is just "the summand fan is one
  independent layer", which needs no library — plain `rayon` over the
  match vector (loop #3) realises the entire data-parallel payoff
  without depending on an experimental API or rebuilding the term store
  on flat `Vec<usize>` incidence (which would *lose* the hash-cons
  structural sharing `term.rs:218-221` already exploits — docs/10:402-411,
  a real risk).** The OHG library is the right *mental model* (Wilson–
  Zanasi layering = the independence relation) and the wrong
  *implementation vehicle* at 0.3.1 maturity for the trusted-adjacent
  fast tier.

---

## Single most promising opportunity

**Parallelise the per-step summand fan in `produce_stars_fast`
(`interactive.rs:1153-1208`) with rayon over the
`mat_phi_c_accel` match vector — `rayon`, not the open-hypergraph
crate.**

Why: it is the *only* hot loop where the dominant measured cost is
actually exposed to parallelism. `fuse` is ≈82% of wall; each summand in
a step is a fully independent `alpha_rename + unify + theta.apply +
push` (the `*counter` mutations at `interactive.rs:1170,1188` are the
sole shared state and are trivially privatisable by pre-partitioning
disjoint counter ranges per candidate). A single `unify` is a hard
serial wall (P-complete union-find, `unify_fast.rs:132-169` — do not
attempt to crack it internally), but the fan runs N independent unifies
that today execute sequentially; spreading them across cores is the one
place the 53% `unify` + 5% `subst` + 3% `freshen` cost gets real
parallel relief, with speedup ≈ min(#cores, fan width) on the whole step
body. It is faithful by the *existing* gate: reordering summands and
fresh-name counters only perturbs the result up to the α-canonical
multiset that `faithfulness::psi_compatible` already certifies and
`iex_fast` is already only result-equivalent under
(`interactive.rs:1803` `iex_fast_result_eq_iex`); non-confluent
subjective/forcing corpora deopt to reference `iex` exactly as today —
no new trusted code, the non-negotiable gate is reused. Build cost is
small (add `rayon`, partition counter ranges, audit `mk_app_interned`/
`RwLock<TermStore>` contention — the docs/10 §3 B3 array-store work is
the natural follow-on but not a prerequisite). The honest caveat,
inherited from docs/10:196-200 and unchanged: the win scales with fan
width — favorable on galaxy's wide δ-fans, negligible on narrow Horn,
and the realistic envelope is the *post-`unify_fast`* profile, so this
is sequenced **after** docs/09 Stage 1 so its delta stays attributable.
Everywhere else the answer is the serial wall: a single unification
(#1) and the step-to-step recurrence (#4) are fundamentally serial, and
the saturated-diagram explosion (#5) is embarrassingly parallel in form
but a measured dead computation (docs/16 §7.3) not worth accelerating.

---

## MEASURED-NEGATIVE — per-step summand-fan rayon (#5, honest-negative, NOT shipped)

The report's single lever ("rayon over the produce_stars_fast summand
fan") was built with the HARD constraint of deterministic byte-identity
(parallel-compute, ordered-commit, prefix-sum-disjoint Var::Idx counter
bases mirroring the exact sequential progression). **The deterministic
design SUCCEEDED** — all gates green incl. galaxy Φ=405 steps=371
BIT-identical before↔after, a new double-run in-process determinism
test, WIN-1's per-step PsiCS oracle, spec_phi 5/5, Σ(Φ) step-identity.

But the SPEED GOAL FAILED, measured: the per-step candidate fan is
1–3 cheap `unify_fast`+θ-apply calls; `par_iter` dispatch+join cost
PER STEP × 10⁵–10⁶ steps dominates the independent work ~10×.
KS-PROF (steps strictly identical): galaxy/triple fuse 0.0113s →
0.0155–0.022s; binarith/mul fuse 7.39s → 70.1s, wall 50.5s → 181.3s
(≈3.6× WORSE). Revert-class even though correct → reverted, nothing
committed, dev untouched (ae49cae).

⇒ **The data-parallel lever is measured-negative AT THIS GRANULARITY.**
The serial wall the report itself flagged (per-step dependency,
sub-rayon-granularity work items) is the binding reality. A profitable
data-parallel design would need COARSER work items — cross-step /
batched-region parallelism (a different algorithm, e.g. speculative
multi-step or whole-subtree parallel reduction), not the per-step fan.
Recorded so future-us does not re-attempt the per-step form. The
deterministic-counter-pre-partition technique itself is sound and
reusable if a coarser parallel site is ever found.
