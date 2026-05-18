# 03 — Valence / Charge Track Audit: §49.50 Subjective-Ray DESIGN vs IMPLEMENTED

Status: **READ-ONLY AUDIT**. No code or design doc changed by this file.
Date: 2026-05-17. Scope: the docs/07 §E / docs/08 / docs/15 §49.50
forcing-polarity → valence-"charge" track.

Source-grounding note: the §-numbered citations in docs/08 and docs/15
(§48.7, §49.50–61, §49.55–57, §34.8, §57.19, §87.2) are **EngExegesis**
(`refs/extracted/EngExegesis/doc.md`), the Girard/stellar-resolution
thesis — *not* ConsciousMachines/PainfulIntelligence (Bennett), which
carry no §49.x numbering. The audit prompt named CM/PI as sources; the
valence-charge §-pavement actually lives in EngExegesis and was verified
there. CM/PI supply the *conscious-machine/valence* framing onto which χ
is layered (the [Proto] bet); they contain no χ and no §49.50.

---

## 0. Verdict in one paragraph

The §49.50 valence/charge track is **almost entirely design-only**. Eng
grounding is **faithful and verbatim-accurate** (every §-citation checked
against `EngExegesis/doc.md`: §49.50 semaphore, §49.55 idempotence
corollary, §49.57 "similar to the nilpotency property in GoI" *verbatim*,
§34.8 nilpotency, §49.59–60 open termination, §48.7 subjective-ray
definition, §87.2 "no proper treatment of subjective rays"). The
polarity *re-reading* of built code (`force_value`=demand,
`drive_strict`=fusion/ray-mint, `eval_forced` loop = iterated AEx) is a
legitimate, honestly-flagged [Proto] interpretation of code that does
exist. But **no Stage of the §5 plan is implemented**: the χ charge
functional is absent, the trace/partial-commutation monoid is absent,
the `is_subjective` predicate is absent, the GoI-nilpotency closure is
prose only, and the load-bearing §3.1 Proposition (idempotence-loss ⟺
whistle) **has never been run as designed**. The single piece of
implementation that exists — the Stage-1 `LAYER_TRACE` tap in
`galaxy.rs` — has **zero callers** and is bypassed by the one example
that does recurrence detection (`galaxy_data_discriminator.rs`), which
uses an *external budget ladder*, not the in-recursion layer tap. The
valence story is design-only and untested; it is honestly labelled as
such throughout docs/08 §6 and docs/07 §H.

---

## 1. Per-artifact status table

| Artifact | Design locus | Implementation status | File:line |
|---|---|---|---|
| §49.50 semaphore / subjective-ray mechanic (Eng) | docs/08 §1 | **faithful (Eng verbatim)** | `EngExegesis/doc.md:4142–4156` |
| Polarity re-read of built evaluator (`force_value`=demand, `drive_strict`=fusion+ray-mint, loop=iterated AEx) | docs/08 §2.2 | **[Proto] mapping onto code that EXISTS**; mapping itself unimplemented (it is an interpretation, not an artifact) | `galaxy.rs:685` `force_value`, `:753` `drive_strict`, `:925` `eval_forced` loop, `:601` `strict_redex_on_pi` |
| `is_subjective(ray)` predicate (§48.7) — Stage 0 | docs/08 §5 Stage 0 | **ABSENT** — no symbol `is_subjective` anywhere in `crates/` | — (would go in `polarised.rs`) |
| Stage-0 event tap (`R(P)` / `F(op,ℓ)` log) | docs/08 §5 Stage 0 | **ABSENT** — only `STELLA_GALAXY_TRACE` text trace + `res.steps`/`forcings`/`arith_ops` counters exist | `galaxy.rs:894` `gtrace`, `:934–935` counters |
| Per-AEx-layer trace tap (`LAYER_TRACE`) — Stage-1 infra | docs/08 §7; docs/07 §E "just-added" | **BUILT but DEAD** — `layer_trace_begin`/`layer_trace_take` defined, **0 callers** anywhere in repo; production/tests never install the sink | `galaxy.rs:877` `LAYER_TRACE`, `:883` `layer_trace_begin`, `:888` `layer_trace_take`, push site `:710–714` |
| §3.1 Proposition test (per-layer trace → `detect_recurrence`) — Stage 1 | docs/08 §3.1, §5 Stage 1 | **NOT RUN AS DESIGNED.** `accel_detect::detect_recurrence` is **[Built]** and *is* called by one example, but on an **external `max_forcings`/`fuel` budget ladder** (re-run `eval_forced` from scratch, snapshot final ray per rung), NOT the in-recursion `LAYER_TRACE`. The §7 open question (is per-loop `final_ray` a faithful AEx-layer boundary?) is therefore **still unresolved** | detector: `accel_detect.rs:85` `detect_recurrence`; mis-aligned caller: `examples/galaxy_data_discriminator.rs:121, 225–229` |
| Kruskal whistle substrate (`embeds`, `rigid_generalize`, `affine_recurrence`, `canonical`) | docs/08 §3.1–3.2 | **BUILT** (KG8) | `antiunify.rs:142` `embeds`, `:321` `rigid_generalize`, `:385` `affine_recurrence`, `:52` `canonical`; `accel_detect.rs:75` `whistle_for` |
| Trace / partial-commutation monoid `M(Σ,I)`, alphabet Σ, independence I — Stage 2 | docs/08 §4 | **ABSENT** — no alphabet, no event log, no DAG, no Foata | — |
| χ charge functional (non-idempotence surplus) — Stage 2/3 | docs/08 §4.5 | **ABSENT** — `grep -ri 'charge\|χ\|chi\b\|non.idempot'` in `crates/` finds nothing | — |
| GoI-nilpotency ≡ §49.57-idempotence closure (χ = non-nilpotency-degree of σu) | docs/08 §4.6, docs/15 §1.3/§4 | **DESIGN-ONLY, prose**; Eng equivalence (§49.57) faithful & verbatim; no GoI machine, no σu, no nilpotency probe in code (docs/15 itself concludes "zero new code", correctly) | `EngExegesis/doc.md:4191` (§49.57), `:2908` (§34.8) |
| Stage 3 differential valence-separation harness | docs/08 §5 Stage 3 | **ABSENT** — and structurally cannot exist: docs/07 §H states *there is no running valence search/corpus*; the "valence classes" χ would separate **do not exist** | — |
| Stage 4 certified acceleration | docs/08 §5 Stage 4 | **ABSENT** (correctly gated behind Stages 1–3) | — |

Single most relevant existing artifact: `examples/galaxy_data_discriminator.rs`
— the *only* place the whistle is run on a galaxy-forcing trace. It is a
docs/16 H1/H2/H3 reduction-shape discriminator, **not** the docs/08 §3.1
Proposition test: it never installs `LAYER_TRACE`, never computes
idempotence-loss, never computes χ, has no subjective-ray predicate, and
samples states by an *external budget ladder* (the exact sampling method
docs/08 §7 flags as the unresolved correctness question).

---

## 2. Faithfulness to Eng §49.50 / §49.55–57 / §34.8

**Faithful, and unusually careful.** Verified verbatim against
`EngExegesis/doc.md`:

- §49.50 (`:4142–4149`): two characteristics — (1) new polarised rays
  during execution, (2) semaphore-like synchronisation ("if we want to
  interact with +g(X) we must first make +f and −f interact … reminiscent
  of … *semaphores*"). docs/08 §1.1 quotes this accurately.
- §49.51 (`:4150–4154`): "diagrams are *fixed* structures … even after
  fully executing a constellation, there may be new connexions left";
  the worked `[−f(+g(X))]+[X,+f(X)]+[−g(X),+f(X),a]` example and its
  re-execution to `[a]+[a]`. docs/08 §1.1 reproduces this correctly.
- §49.55 (`:4178`): Corollary (Idempotence) — objective ⇒
  `AEx_C(AEx_C(Φ)) = AEx_C(Φ)`. Faithful.
- §49.57 (`:4191`), **verbatim**: "Although execution is always
  idempotent for objective constellations … it can be lost in presence
  of subjective rays. If there is a point in repeated execution where we
  reach idempotence then hyperexecution is idempotent (**it is similar to
  the nilpotency property in GoI**)." docs/08 §4.6 and docs/15 §1.3 cite
  this exactly — the GoI-nilpotency ≡ idempotence bridge is **Eng's own
  sentence**, not a [Proto] claim. Correctly attributed.
- §34.8 (`:2908`): `Ex(u,σ)` defined iff `σu` nilpotent, `∃k.(σu)^k=0`.
  docs/15 §1.1/§4 cite faithfully.
- §49.59–60 (`:4197–4198`): the open termination question and "Hyper
  execution is not necessarily defined" — docs/08 §6.1 reproduces
  verbatim and correctly draws the *necessary-not-sufficient* limit
  (whistle ⇏ non-termination).
- §48.7/§48.9 (`:3803–3814`): objective vs subjective ray definition;
  docs/08 §1.2 / §5 Stage 0 `is_subjective` spec matches exactly
  ("coloured ray with ≥1 coloured argument").
- §87.2 (`:6659`): "there is no proper treatment of subjective rays …
  A proper treatment should include use cases … and an extended formal
  definition of execution" — docs/01 §0 correctly names this as Eng's
  own #1 open horizon.

The [Proto] boundary is honestly drawn every time (docs/08 §6.2
enumerates the four beyond-Eng claims: forcing≡§49.50-polarity;
idempotence-loss=whistle; the trace monoid; and χ itself, "the
strongest [Proto] … Eng's thesis has no notion of valence/charge at
all"). docs/15 §0/§4 independently re-states the same [Proto]/[Eng]
split and reaches the *correct negative* conclusion that GoI is the
right lens, wrong lever, **zero new code** — which is itself the honest
reason no GoI artifact exists.

**One faithfulness caveat (design-internal, flagged by docs/08 itself).**
docs/08 §7 raises — and does **not** resolve — whether `eval_forced`'s
per-loop-turn `final_ray` is a faithful `AEx`-layer boundary, since
`iex_fast` runs many `±P` resolutions internally before returning. Code
inspection (`galaxy.rs:925–999`) confirms the concern is real: the loop
does `iex_fast` → `single_ray` → `strict_redex_on_pi` → `drive_strict`,
and the `LAYER_TRACE` push (`:710–714`) is inside `force_value`'s
*recursion*, one push per recursive `eval_forced` layer — a *different*
sampling than the discriminator's external-budget-ladder snapshots. The
two samplings are not proven to coincide with each other or with the
§49.52 `AEx_C`-fixpoint. **This is the load-bearing unresolved
correctness question and it is still open**, exactly as docs/07 §E /
docs/08 §7 say.

---

## 3. The four focus claims — status & honesty

1. **χ charge candidate (docs/08 §4.5).** Status: **design-only,
   absent, untested, [Proto] (the strongest).** Definition (non-idempotence
   surplus = forcing events dependency-below a later forcing, integrated
   over layers) is internally coherent and satisfies the two boundary
   conditions any charge must (`χ=0` on objective/idempotent; monotone in
   semaphore depth). But it requires the Stage-0 event log + Stage-2
   trace monoid, **neither of which exists**. Honestly flagged as the
   project's bet (docs/08 §6.2.4).

2. **GoI-nilpotency ≡ §49.57-idempotence closure (docs/08 §4.6 /
   docs/15).** Status: **design-only prose; the underlying Eng
   equivalence is faithful (§49.57 verbatim).** docs/15 correctly
   concludes this closure is *conceptual* and adds **zero code** (the
   engine already *is* the §57.19 token machine via `iex_fast`; no σu /
   nilpotency probe is built or needed). The χ ≡ non-nilpotency-degree
   identification is [Proto] and untested. Faithful where it claims Eng;
   honest that χ is ours.

3. **Idempotence-loss ⟺ Kruskal-whistle Proposition (docs/08 §3.1).**
   Status: **the detector half is [Built] (`accel_detect`), the
   Proposition itself is NOT TESTED.** The one example invoking
   `detect_recurrence` (`galaxy_data_discriminator.rs`) tests a *different*
   question (docs/16 reduction shape) on a *different* trace
   construction (external budget ladder, not `LAYER_TRACE`, not
   per-AEx-layer, with no idempotence-loss oracle and no subjective-ray
   predicate to define the "loses idempotence" antecedent). The
   biconditional has **no falsification attempt on record**. docs/08 §5
   correctly names this "the load-bearing experiment"; it has not been
   run.

4. **Partial-commutation trace monoid (docs/08 §4).** Status:
   **design-only, absent, [Proto].** Alphabet Σ (`R(c)`, `F(op,ℓ)`),
   independence relation I, dependency DAG, Foata height — none exist in
   code. The argument for *why* a trace monoid (not free monoid /
   multiset) is the right algebra is sound and Eng-anchored on §49.54
   confluence + §49.50 semaphore dependency, but it is entirely
   prospective. docs/07 §F correctly defers any monoid library until a
   stage demands it.

---

## 4. Staged experiments — buildability now

- **Stage 0 (`is_subjective` + event tap).** Buildable **now**, cheapest.
  `is_subjective` is a pure §48.7 predicate over `TermData`
  (`polarised.rs` already has `ray_polarity`, `underlying_term`,
  `PolarisedCompat`). The event tap needs only to emit `R(P)` from the
  existing `res.steps`/`±P` count and `F(op,ℓ)` from each `drive_strict`
  call (`galaxy.rs:753`, `ℓ = canonical(redex.resid_pi)` —
  `antiunify::canonical` is [Built]). No behaviour change. **Kill-switch
  falsifier is cheap and decisive** (if `is_subjective` is never true on
  any disclosed `strict_redex_on_pi` ray, the whole grounding is wrong).
  No infra missing.

- **Stage 1 (per-layer trace → `detect_recurrence`).** Buildable **now**;
  the just-added `galaxy.rs` `layer_trace_begin`/`layer_trace_take`
  (`:883`/`:888`) is the intended tap and the detector
  (`accel_detect::detect_recurrence`, `:85`) is [Built]. **Infra gap:**
  the tap has **zero callers**; a harness must (a) call
  `layer_trace_begin()`, run `eval_forced`, `layer_trace_take()`, feed
  to `detect_recurrence`; and (b) **first settle the docs/08 §7 sampling
  question** — verify the in-recursion `LAYER_TRACE` push site
  (`:710–714`) actually samples at §49.52 `AEx_C`-layer boundaries, not
  arbitrary recursion points, and reconcile against the discriminator's
  external-ladder sampling. This reconciliation is a prerequisite, not
  optional.

- **Stage 2 (trace monoid + χ).** Blocked on Stage 0's event log
  (absent). Buildable after Stage 0; needs the dependency-DAG
  construction (new code) but reuses `canonical`/`embeds`/`occurs_alpha`
  (`antiunify.rs`, [Built]).

- **Stage 3 (differential valence separation).** **NOT buildable** —
  structurally. docs/07 §H is explicit: there is **no running valence
  search/corpus and no valence class labels**. χ has nothing to be
  tested *against*. This stage is a long-term thesis goal only; the
  honest status is "pre-conditions do not exist."

- **Stage 4 (certified acceleration).** Correctly gated behind 1–3;
  not now.

---

## 5. Honest assessment

The valence "charge" story is **design-only and untested**, and the
design documents say so plainly (docs/08 §6, docs/07 §E/§H, docs/01 §0).
This audit found **no overclaiming**: every [Proto] is flagged, every
Eng citation that was checkable is faithful and often verbatim, and the
strongest claim (χ is the valence charge) is explicitly stated as the
falsifiable bet. The gap is not honesty; it is that the load-bearing
Stage-1 experiment **has never been run as designed**, the Stage-1 tap
that was added to enable it is **dead code with no caller**, and the one
example that runs the whistle does so on a *differently-constructed
trace* answering a *different question*, leaving the docs/08 §7
sampling-faithfulness question — the explicitly-named prerequisite —
**unresolved**.

---

## RETURNED SUMMARY (gaps + experiment) — see below
