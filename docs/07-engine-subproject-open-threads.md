# Engine subproject — OPEN THREADS LEDGER (pre-compaction snapshot 2026-05-17)

Durable state of the stella-combinator / KS / KG / KA engine arc, so nothing
is lost across compaction. Canonical subproject spec = `docs/05` (§1–7 LOCKED;
§8 KS architecture; §9 Axis-2-reborn). This file = the live thread list.

## Commits this session (engine/galaxy/KA arc; interleaved w/ user's parallel commits)
ca5731d K1 combinator core · 880cb84 K2a arith · caf3531 K2b strict-prim
trichotomy · 33dfcee KG1a binary arith + KS Tier-0 + measurement infra ·
2615d42 KS LeverA+discrimination (binarith x8) · c575bfa KS B1 matchable_fast
(binarith x12 / combinator x4) · f07ec49 KS B2-store Arc+RwLock · 1a3c259
de Bruijn Var=Named|Idx · 9fc8987 docs/05 §9 spec · 82b4b63 KA0 substrate
(canonical/lgg/affine_recurrence) · 539d6eb KG2+KT harvest (galaxy loader +
combinator fuzz) · ce8ee55 KG3a probe · 4e66adf KG3b lazy prim layer (galaxy
→371-step NF) · 3901671 KG3c isnil measured · cf28558 KA1 tabling (retained
infra, NOT default) · d549387 KA0 rigid-AU+Kruskal-embedding · 73091f1 KG1b
signed binary arith · 614476c KG3c slice2 arith-forcing + reprioritization.

Measured KS speedups (release, faithful, vs original reference): binarith/Horn
~12×, combinator ~3–4×. All differential-gated (reference `iex` = oracle;
`iex_eq_iex_fast` byte-identical, `iex_tabled_result_eq_iex` result-equiv,
20k `matchable_fast` fuzz, antiunify 6/6).

## A0. HARVESTED — wider-workstreams write-swarm CLOSED
- **Front 0** → `cdf9a9c` (KG7) `evaluate.rs`: evaluate()/evaluate_many
  + EvalReport/ViabilityReadout + LIVE differential oracle. Forensic-
  verified 4/4 incl. the Goodhart-guard catch test (oracle provably
  flags an unfaithful fast path). The valence-search contract + the
  experiment-validity gate (§D) now exist.
- **Front 1** → `244871c` (KG8) `accel_detect.rs`: Kruskal-whistle
  `detect_recurrence`/`detect_in_window` + sound generalizer on the
  antiunify KA0 substrate. Forensic-verified 6/6. **Substantive correct
  spec deviation (verified, not trusted):** soundness uses one-
  directional α-subsumption (`∃θ. canonical(g)·θ ≡ canonical(x)`), NOT
  `embeds` — Kruskal identity-keys variables so a generalization var
  doesn't embed the term it abstracts (`f(Z)⋬f(a)`); the agent caught
  this and implemented the textbook subsumption order. LESSON: a capable
  worktree agent + parent forensic-read-of-the-deviation can yield
  substantive correctness improvements over the spec — read the
  deviation, don't just trust the green.
Both NEW disjoint files ⇒ `cp`-safe (no stale-base hazard); one-writer
discipline held; engine unmodified.

## A0-orig. IN FLIGHT — wider-workstreams coordinated write-swarm (2 agents)
User opened Fronts 0+1 concurrently (coordinated write-swarm; one-writer
per file, disjoint NEW files, stable base = HEAD d112520, parent
forensic-verifies + harvests — never trust self-report, the 2 stale-base
burns this session are why). Both branched from the clean post-KG6 base.
- **Front 0** `ad405b51f7c6a8ed8` → NEW `crates/stella-core/src/evaluate.rs`:
  `evaluate()`/`evaluate_many` + `EvalReport`/`ViabilityReadout` + LIVE
  differential oracle (`OracleMode`/`OracleStatus`) = the contract the
  valence search drives millions of times + the Goodhart guard
  (experiment-validity-critical, §D). Verify: `evaluate::` green incl.
  the deliberately-unfaithful-fast-path "Divergent" catch test; reads
  valence/reafference/subjective read-only to align the readout; must
  NOT modify the engine.
- **Front 1** `a7e84901442d90098` → NEW
  `crates/stella-core/src/accel_detect.rs`: Kruskal-whistle recurrence
  detector + generalizer over a trace (`detect_recurrence`,
  `is_sound_generalization`, `detect_in_window`, `Whistle`) on the
  EXISTING `antiunify` KA0 substrate. Foundation for KA2 speculative
  accel (NOT built here). Verify: `accel_detect::` green incl.
  positive/negative whistle + soundness + one-unital-NULLARY caution.
Harvest recipe: read report → `cp` the ONE new file (disjoint ⇒ safe,
no shared-file stale-base hazard) → add its `pub mod` line to lib.rs
(parent) → forensic-verify in main tree → clean worktree+branch+prune
→ commit. Both disjoint ⇒ order-independent.

## A. BOTH subagents HARVESTED — thread A CLOSED
- **galaxy_decode** → `490168f` (KG3d). Forensic-verified in main tree.
  Result fed thread B (below).
- **IexAccel-caching** → `308189f`. **PORTED, not cp'd** — its worktree
  was branched from a stale base (f06730f, merge-base 445af70) predating
  the whole KA1 arc (`cf28558`); a blind `cp` of its interactive.rs
  would have OBLITERATED committed KA1 tabling. Hand-ported the additive
  delta onto the live file; KA1 byte-preserved (`iex_tabled_result_eq_iex`
  still green). New valence-loop API: `build_accel`, `iex_fast_with_accel`,
  `iex_tabled_with_accel` (composes KA1 + accel-hoist). Honest bench:
  1.50× on real binarith Φ (agent's 7.32× was a synthetic wide-Φ
  worst-case); win scales with |Φ|, kills the per-call O(|Φ|) RayIndex
  rebuild the valence search does millions of times. Both worktrees
  removed + branches deleted + pruned.

**HARDENED PROCESS LEARNING (bit BOTH agents):** worktree subagents
branch from whatever base they were spawned at, which can be ARBITRARILY
STALE (here: a user-parallel commit predating the engine arc). Their
self-reports will then truthfully-but-misleadingly claim current modules
"don't exist." Mandatory: parent forensic-verifies in the LIVE main tree
and DIFF-AND-PORTS shared/long-lived files (interactive.rs, galaxy.rs,
lib.rs) — **never blind-`cp`** a shared file from a worktree. `cp` is
only safe for genuinely-new disjoint files (galaxy_decode.rs). 4 stale
prior-session worktrees (a00225d4/a12156a8/a3d0a69f/af5325dc, bases
f06730f/9fc8987) remain locked+orphaned — not in any in-flight set;
left intact (unknown provenance; clean only on user confirm).

## A-orig. IN FLIGHT — TWO subagents, harvest BOTH (worktree-harvest model)
For each: read its final report (self-describing) → `cp` its new/changed
file(s) from `.claude/worktrees/agent-<id>/...` into the main tree → add any
`pub mod` line it specifies to `lib.rs` (parent owns lib.rs) → forensic-verify
in main tree (DON'T trust self-report) → `git worktree remove --force` +
`git branch -D worktree-agent-<id>` + `git worktree prune` → commit. Disjoint
files ⇒ order doesn't matter; both safe.

- **IexAccel-caching** `a253857384cc7bd43`, on `interactive.rs`. Adds
  `iex_fast_with_accel`/`iex_tabled_with_accel` + pub accel build so the
  valence loop builds the head-index ONCE per fixed Φ (kills per-call
  `IexAccel::build` for millions-of-small-execs). Verify: `iex_eq_iex_fast`,
  `iex_tabled_result_eq_iex`, `mat_accel_eq_mat_ref`, `combinator::`,
  `arith::` green + paste its micro-bench numbers.
- **galaxy_decode** `ae872cb047e1025c6`, NEW file
  `crates/stella-core/src/galaxy_decode.rs` (disjoint from interactive.rs).
  Faithful GValue decoder of galaxy's NF (kills the lossy focus/π
  extraction) + `dump_galaxy_nf` diagnostic. Verify: `galaxy_decode::` green;
  **the most valuable artifact = the pasted `dump_galaxy_nf` output** (galaxy's
  actual decoded normal form — tells the next session whether the 371-step NF
  is a clean list (correct-ish) or Opaque-dominated (the honest "NF may be
  wrong" risk realized). Feeds thread B directly.

## B. GALAXY SPINE — DIAGNOSED + partially fixed (KG3e/KG3f)
**The earlier "371-step true NF, fully_reduced=true, 0 arith" was a
STRUCTURAL FALSE NEGATIVE, now overturned.** KG3e (`galaxy_dump.rs`,
commit 6baff61): the terminal state is `+P(st(eq, A·B·π))` — galaxy's
first interaction Push-uncurries `eq` onto the KAM stack and stalls
because `prim_stars()` omits strict ops. `find_blocked_arith`/`eval_forced`
only scanned the *curried* `a(a(op,A),B)` form; the KAM **always**
uncurries operators onto π, so the live redex (`st(op,…·π)`) was in a
shape the detector never matched. The decoder's `[0,[]]` was an
unrelated tiny island in the 702-node frozen continuation. (Inverse of
the census-artifact lesson: here the precise detector itself was
incomplete.) KG3f (commit 3696dff): added `find_blocked_pushform` +
recursive Push-form forcing in `eval_forced` (force operands via the
forced evaluator itself, compute via stellar (s)binarith, tt/ff→t/f,
`st(result,π_resid)`, continue). **Measured curve now:** galaxy
genuinely executes strict arithmetic — one `eq` operand forces cleanly
to numeral `0`; the other resolves **13 nested strict ops** then stalls
on a *deeper* Push-form `lt`. Residual = arithmetic DEPTH (and/or the
known `div` frontier), an honest measured stop — NOT a dead end, NOT
faked. `div` still NOT auto-forced (KG1b: stellar div past KS frontier).
**KG3g (commit 3b5551b) — galaxy's first interaction FULLY EXECUTES.**
User decisions applied: host-force `div` (disclosed) + drive to first
render. Root causes (found via env-gated `STELLA_GALAXY_TRACE`): (1)
`div` excluded everywhere; (2) curried arith branch used non-recursive
`force_whnf`; (3) THE stall — curried branch spliced raw sbinarith
`tt`/`ff` into the galaxy term (galaxy consumes booleans as church
`t`/`f`, no `tt`/`ff` rule ⇒ false NF). All fixed; `sub_fuel` 20k→2M;
`Forced` gained `final_ray` (result is on π); KAM readback added
(`st(M,a·b·…)` ≡ `a(a(M,a),b)…`). Measured: `steps=5227 arith_ops=16
fully_reduced=TRUE`, `decode(readback) = [0 | <a/2>]` ⇒ **protocol
FLAG = 0** (valid result head). Gates green (galaxy 7 / decode 9 /
interactive 14 / sbinarith 11). New examples: `galaxy_drive` (driver +
readback), `galaxy_chase` (operand-tree diag). **Next B = deep
recursive readback/force of the `<a/2>` tail** = the `(newState,data)`
payload still in Push/lazy form ⇒ full `(0,newState,[images])` =
rasterisable first frame.

**KG3h/KG4 — review swarm + architectural unification.** Whack-a-mole
(KG3e–h) hit the SAME bug class 3× ⇒ ran a 3-agent parallel review
(forcing-arch / ICFP-faithfulness / decoder). Findings → user decisions
→ acted:
- **KG4 (commit f735d20):** replaced 8 per-prim curried+Push detectors +
  2 duplicated branches + `replace_subterm` with ONE detector
  (`strict_redex_on_pi`, Push-form only — the KAM always uncurries), ONE
  forcer (`force_value`, budget-1 ⇒ well-founded), ONE driver
  (`drive_strict`), `galaxy_bool` at the single tt/ff point. ~250→~120
  lines. Fixes review defects D1 (tt/ff escape), D2/D3 (eval-order: only
  the leftmost Push redex is forced — arith_ops 16→10, fully_reduced
  still TRUE, flag=0 preserved), D6 (well-foundedness), D7 (Nil/Cons
  committed only when sub-eval fully_reduced). galaxy_chase deleted.
- **KG4b (commit fb67b92):** sbinarith honest-marking (user:
  accept-as-disclosed). The magnitude layer (`umag_*`) is genuinely
  stellar; the **signed layer is host i128 with a hard 128-bit ceiling**
  (sign/order/zero/division decided on host; `neg` 100% host;
  galaxy-scale magnitudes silently `None` via `i128::try_from`). Doc
  rewritten from the "complete and faithful" overclaim to a plain
  "Faithfulness boundary"; per-site `// HOST:`/`// CEILING:` markers.
  **FRAMING (user-corrected — do not re-litigate):** the native signed
  kernel behind the differential oracle is a legitimate *intrinsic*
  (jet), the exact GraalVM/verified-speculative-runtime model of §H —
  NOT a "violation"/"smuggling"/moral debt (the adversarial review
  over-rotated). Keep the honest-marking (disclose the i128 ceiling so
  nobody mistakes it for unbounded). All 13 prim rules verified faithful
  (review Agent B); galaxy's combinator/control skeleton executes
  faithfully; its arithmetic is a disclosed oracle-gated native
  intrinsic. Genuinely-stellar fully-general signed arithmetic is a
  *planned generalization* (the KS stream — still worth doing), NOT a
  correctness blocker.
- Review Agent B also found: NO `modulate`/`demodulate`/`multipledraw`/
  `interact` loop exists ⇒ `[0,…,…]` is the raw single-application
  `(flag,newState,data)`, not a rendered frame; real rendering needs
  that protocol layer (Track below).

**ALL THREE TRACKS DONE (user: do all three):**
1. ✅ KG4 (f735d20) architectural unification + D1/D2/D3/D6/D7.
2. ✅ KG4c (81b1b6a) decoder onto KAM readback: `decode` readback-aware,
   `decode_ray`, `decode_forced(phi,&Forced,fuel,maxf)` recursive
   force+readback, deleted `best_list_subterm`/`list_score`,
   `dsint`/`sint`→`sbinarith` (nested-neg/neg-zero correct). Tests
   migrated (the old test asserted the deleted heuristic's lie).
3. ✅ KG5 (cb96158) harvested modulation codec (modulate/demodulate,
   9 tests; agent corrected my Int(1) spec typo). ✅ KG6 (ee8a0e8)
   `interact.rs`: encode (Opaque⇒None), GValue↔MVal, modem=demod∘mod,
   parse_triple, multipledraw, interact loop, galaxy_first_frame; 4
   tests.

**MEASURED END-TO-END (KG6, honest, not faked):** galaxy's first
interaction now reaches the **protocol triple `(flag=0, newState,
data)`** via galaxy→eval_forced→decode_forced→interact. The pipeline is
correct and refuses to fabricate: `data`'s image-list elements are still
unforced (`Opaque "unforced:…"`) so `multipledraw` honestly returns
`None` (0.9 s — a clean early stop, NOT slow/explosive). So the engine +
protocol + decoder + codec are all wired and faithful; ONE gap remains
to a rasterised frame.

**NEXT THREAD = deep-force the image-data payload.** `decode_forced`'s
`deep_decode` calls `eval_forced` per cons field but the `data` list
elements don't reduce to cons/nil/num under the current bound (depth
4096 / budget 50k) — they read back to a non-cons `a/2` (galaxy_dump
earlier: `data[0]` = an `isnil`-guarded `c/b/s` expr). Post-KG4 the
Push-form `isnil` IS handled by `strict_redex_on_pi`, so the residual is
either deeper structure or a decode_forced bound/shape issue — same
investigate-don't-guess discipline, now with the trustworthy
readback/decoder as the oracle and the protocol layer ready to consume a
real frame the moment the data forces. (Perf of deep payload forcing =
the KS-throughput thread D.) Planned generalization (NOT a blocker):
genuinely-stellar fully-general signed arithmetic = the KS stream;
the native intrinsic is legitimate and disclosed (see §B KG4b framing).

(Pre-KG3e text, retained for the measured arc:)
Measured arc: blocked@5 → KG3b lazy prims → 371-step "NF" → KG3e found
it was a Push-form `eq` stall, not a true NF. Forcing driver
(`galaxy::eval_forced`, disclosed §60) now Push-form aware (KG3f).
**NEXT = faithful FULL-RESULT DECODER (= rendering path = validation oracle):**
decode the whole process ray (NOT `focus`/`st_inner` — output lives on the
continuation π), decode ICFP cons/nil list-of-(x,y), check vs the known
`(nil,(0,0))` reference vector, rasterize.

**DECODER BUILT + HARVESTED + FORENSIC-VERIFIED (490168f, KG3d).** The
honest open risk is now RESOLVED in the informative direction:
galaxy's 371-step NF decodes to a CLEAN proper 2-list `[0, []]` —
**ZERO Opaque nodes** (independently reproduced in main tree release,
not self-reported). So: the decoder is NOT papering over a garbage NF
(no Opaque domination), the engine genuinely reaches a true NF — BUT
`[0,[]]` is **shallow**: NOT galaxy's real ICFP `(flag,newState,data)`
protocol result (371 steps is tiny for a real galaxy interaction). The
"degenerate non-redex state" horn of the old risk is the live one.
**NEXT galaxy deliverable is no longer "build the decoder" (done,
faithful, now the trustworthy oracle) — it is "WHY does the entry
interaction reduce only shallowly":** suspect entry/click encoding
(`ap ap :1338 nil (ap ap cons 0 0)` shape), the interaction-loop
driver, or galaxy's neg/div placeholders stalling deep eval early.
Decode it with `galaxy_decode::decode_result` as the oracle each step.

## C. KA TRACK
- KA0 substrate done + rigid-AU/Kruskal-embedding + one-unital-NULLARY caution
  (antiunify.rs). KA1 = retained infra, NOT a default: net-negative on
  non-variant single runs (per-star canonical-key tax); **its true home is
  the valence evolutionary loop** (variant-dense) — needs (a) cheap
  incremental key, (b) cross-run/persistent table. Serialized after the
  IexAccel agent (both touch interactive.rs; one-writer rule).
- KA2 NOT started. Z3-reshaped: Z3 = solve-for-k + guard discharge on exact
  LIA fragment + **lemma validator** (Cᵏ ≡ k-unroll via induction/SMT —
  symbolic, stronger than per-instance oracle; feeds deferred HOL). z3 crate
  = Cargo.toml = PARENT when KA2 starts. Z3 stays oracle/validator OUTSIDE
  trusted core (yes⇒accept jet; unknown/timeout⇒fallback; ref engine=truth).
  KA2 speculation during a valence search must be **certified-only** (see D).

## D. PARKED ENGINE ITEMS (several re-homed as VALENCE-CRITICAL)
- per-call IexAccel caching = the in-flight agent (A).
- KA1 cheap-key + cross-run table — valence-critical; after A.
- rayon over constellation populations — valence-critical (was "capstone").
- **Differential oracle wired LIVE into any search-driven jit path** —
  experiment-validity-critical: an evolutionary search maximizing viability
  WILL find & amplify any unfaithful fast path (Goodhart at substrate level)
  → evolve fake-viable agents. Faithfulness IS part of experiment validity.
- lock-free `get` / append-only stable store (B3) — deepest residual constant
  factor (per-node RwLock), pure-perf, pervasive.
- triangular/union-find substitution in `fuse` — biggest per-fuse factor.
- deeper term indexing (discrimination/fingerprint beyond fp_unifiable) —
  matters at galaxy Φ scale (~400 δ-stars).
- a clean fast `evaluate(constellation)→{NF, closure/viability readout}` API
  the valence search drives millions of times (subjective/reafference/valence
  modules are the fitness side).

## E. FORCING → §49.50 POLARITY INTERNALISATION (nearest the valence thesis)
The elegant deep redesign: forcing = negative/test/demand pole, value =
positive/supply pole, strict dynamics = their orthogonal fusion = Krivine
pole / §49.50 subjective-ray semaphore / interaction-net annihilation; one
subsystem unifies with the KA recurrence detector. Parked behind the
pragmatic disclosed driver (built). **Right theory here = trace /
partial-commutation monoids**, NOT words. This track is the one CLOSEST to
the make-or-break valence/conscious-machine bet (§49.50 = where idempotence
is lost = where the "charge" is claimed to live).
**STATUS: design DONE → `docs/08-forcing-polarity-design.md` (KG9
`667ebd2`), forensic-reviewed.** The §3.1 checkable Proposition:
constellation non-idempotent at AEx-layer n ⟺
`accel_detect::detect_recurrence` whistles on the per-layer trace
(`readback_ray(final_ray)` per layer) — falsifiable, wqo-justified,
honestly necessary-not-sufficient for the §49.59–60 termination open
problem. Polarity map onto BUILT code: `force_value`=demand pole,
`ForcedValue`=supply, `drive_strict`=fusion/annihilation + sole
ray-minting site, `eval_forced` loop = iterated AEx. Charge χ =
non-idempotence surplus (trace/partial-commutation monoid, §F-compliant).
**Implementation = parent-sequenced, NOT a swarm:** Stage 0
`is_subjective` + event tap (cheap kill-switch) → Stage 1 per-layer
trace → `detect_recurrence` (THE single load-bearing experiment) →
**review gate** → Stage 2 χ → Stage 3 the make-or-break differential
test (does χ separate valence classes better than a step/size
baseline?) → Stage 4 certified acceleration (differential-gated). Each
stage has an explicit falsifier. **Concrete open question to resolve
FIRST (doc §7):** is `eval_forced`'s per-loop `final_ray` a faithful
AEx-layer-boundary proxy? (`galaxy.rs:864–893` suggestive, unproven —
Stage 1 must instrument or the whistle result is untrustworthy.)

## F. THEORY-MODULO CONCLUSION
NOT finite words/strings (over-fit the prompt seed; SKIP Z3-Noodler/OSTRICH/
SeCo string tooling). Engine should be modulo: α (have), associativity/unit
of `a`/`dot` spine-stack constructors (rigid AU, **ONE-unital only** —
AU-modulo-≥2-units is NULLARY; caution baked into antiunify.rs), linear
arithmetic in the KA2 summarizer (Z3 does Presburger/affine — do NOT
hand-roll), trace-monoid later for the §49.50 frontier (E).

## G. HOL4 / VERIFIED SUBSTRATE
Deferred to next-quarter (user's call). Deferral VINDICATED: synthesize
lemmas later from the observational-equivalence corpus the differential
oracle is accumulating (CCLemma / directed-lemma-synthesis); Z3-validated
KA2 lemmas feed it. Defer-and-accumulate is the literature-endorsed strategy.

## H. STRATEGIC FRAME (load-bearing for next session)
**⚠ VALENCE FRAMING DISCIPLINE (recalibrated — read first):** there is
NO running valence search/evolution; it does not exist. It is a
LONG-TERM THESIS GOAL ONLY. Do NOT use "the valence search drives this
millions of times" as the operative justification for concrete engine or
galaxy work — that is phantom justification (it confused the user). The
engine, galaxy execution, the differential oracle, and the
recurrence/embedding detector all stand on their OWN engineering merit
(heavy execution, not-fooling-ourselves, termination analysis, the
galaxy demo). Valence is load-bearing ONLY in the §49.50 track, where
Eng's thesis itself *defines* §49.50 as the locus of the "charge" — and
even there it is a future, staged, falsifiable Stage-3 bet, never a
present driver. The valence-tagged engine items below (D/§253-281) are
phrased as "valence loop" for HISTORICAL continuity; read them as
"high-throughput-search workload generally" — their merit is engine
throughput, not a running valence experiment.

- Engine is a first-class artifact — world's only/foremost stellar
  resolution engine; GraalVM-caliber ambition; **Eng is in a Signal
  group chat with the user** ⇒ external/publishable; faithfulness-as-
  feature is what makes it credible to Eng. (Secondary, FUTURE: if/when
  a valence experiment is built it would be a heavy-execution consumer —
  but that is not a present workload and does not justify present work.)
- Driving workload NOW: **galaxy** (maturity/credibility; deep single
  run, end-to-end). A future high-throughput-search workload would
  stress the engine differently (millions of small mutated executions,
  faithfulness-under-adversarial-search) — relevant to roadmap *shape*,
  not a present justification.
- GraalVM/Truffle map: ref `iex`="interpreter is spec"/oracle; `iex_fast`=
  optimizing tier; KA1/KA2=self-opt/OSR; verified-jet+differential+deopt =
  Graal speculation/deopt BUT we additionally *validate* ⇒ a **verified
  speculative runtime** (the novel, Eng-relevant contribution; operationalizes
  Eng §49.59-60 hyperexec-termination & §87.2 subjective-rays open problems).
- Maturity gaps = first-class roadmap (not afterthoughts): runs flagship
  end-to-end (galaxy), perf methodology + bench corpus, designed tiering +
  deopt boundaries, observability/tooling, the interactive+rendered galaxy
  demo.

## I. DISCIPLINE REGIME (agreed, lighter)
Beyond-Eng = prototype-IS-spec (legitimate; mark which side of Eng's
pavement). Rigor = differential oracle + measurement + honest negatives
(mostly mechanized — not ceremony). DROP pre-registered-null larp for routine
engine work. KEEP heavy pre-registration ONLY for the valence/agency thesis
claims (there it's existential, the project's whole credibility — not larp).
Z3 allowed where it helps. Process learnings: NEVER put `git stash` cycles in
killable bg jobs (caused a scare); never two write-agents same file; ≤2
concurrent write-agents (RAM); worktree-harvest + parent forensic-verify
(never trust self-report); **subagent worktrees can be spawned on an
arbitrarily stale base ⇒ DIFF-AND-PORT shared files, never blind-`cp`;
`cp` only for new disjoint files** (bit both A agents — now hardened in
§A); "blockers" keep turning out to be census artifacts — always confirm
via precise-redex detection, not head-census.

## J. OUTSTANDING DOC TODO
`docs/05` needs a strengthen-only §10/§11 addendum folding in: the
valence-workload reprioritization (H), the two-workloads frame, the lighter
regime (I), the Z3 affordance (C), the galaxy reprioritization (B: decoder=
rendering=oracle), the §49.50-polarity track (E), the theory-modulo
conclusion (F). (Was deferred "to next checkpoint" — still owed.)

## NEXT ACTIONS (priority order)
1. ~~Harvest both A agents~~ DONE (490168f galaxy_decode, 308189f
   IexAccel). Thread A CLOSED.
2. ~~Diagnose/drive/unify/decoder/protocol~~ DONE: KG3e–h drove galaxy
   to flag=0; KG4 unified the evaluator (+D1/D2/D3/D6/D7); KG4b
   honest-marked sbinarith; KG4c decoder→readback; KG5 modulation codec;
   KG6 interact/multipledraw wired end-to-end. **Measured: galaxy
   reaches the (flag=0,newState,data) triple; data images still unforced
   ⇒ no rasterised frame yet (honest stop).**
   **(NOW TOP)** Deep-force the image-data payload (investigate why the
   `data` list elements don't reduce to cons/nil/num in `deep_decode` —
   bound vs deeper structure; the readback/decoder is the oracle).
   Planned generalization (not a blocker): genuinely-stellar
   fully-general signed arithmetic = part of the KS stream.
3. Fold this into `docs/05` §10 (J) — include the KG3d shallow-NF
   finding (decoder faithful; galaxy NF clean-but-shallow, not Opaque).
4. Then: KA1 cheap-key+cross-run table (D, valence) → rayon (D) → KA2
   (C, Z3) with certified-only-during-search; §49.50-polarity (E) as the
   thesis-nearest deep track.
