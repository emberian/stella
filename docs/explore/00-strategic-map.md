# 00 — Strategic map (synthesis: 6-agent swarm + the session arc)

Authoritative "charting" deliverable. Synthesises the exploration swarm
(A χ-theory · B tractable-AEx · C algorithm-catalog · D perf-audit ·
F data-parallel · E Σ(Φ)-deepen) with the measured results of the arc.
Tags: [Proven] [Measured] [Open] [Dead]. Cite commit/file:line.

## 1. PROVEN / BANKED (do not re-litigate)

- **Galaxy faithful-reproduction arc — CLOSED, now PROVEN-closed.**
  N-KA-cover negative (docs/16 §7, `0e7c279`): data[0]'s blocker is the
  nested `isnil`/`force_value` recursion (not docs/16 §1's premise —
  retracted `d6e584b`); H1 redex-family (`c8cb09e`) and H2 recurrence
  both measured-negative; closed-subterm negative (`b6c65d5`). Agent B
  upgrades this from *measured*-closed to **proven**-closed: no
  tractable faithful AEx exists (KAM clique welds into the query
  component; prune-to-answer *is* the different IEx operator; §62.4
  black-hole counterexample). docs/08 §7 is settled, not pending.
- **χ EXISTS and is EXHIBITED — the first measured charge** (`a3fd4aa`,
  docs/08 §4.9). Agent A: Eng §49.59–61 *establishes* χ-existence and
  §49.61 *constructs* the faithful witness. Run verbatim: subjective
  rays 1→34, ψ 3→58 monotone, NF never; Eng's §49.53 control stays
  idempotent (specificity upheld — signal, not artifact). Honest scope:
  growth-form χ at the `subjective_stream` (IEx) χ-locus.
- **Platform, all faithfulness-gated:** faithful §48.7 colour-nesting
  classifier (`de71654`); idempotence metatheorem executable
  (`1bf21ac`, §49.55 ✓ / §49.57 boundary measured); §67.10-cut-elim
  CALIBRATED `detect_recurrence` (`f634f61`, specificity) + the §49.53
  divergent anchor (sensitivity side, `a3fd4aa`); Σ(Φ) Σ0/1/2 +
  **redex-selection deepened** (E, `ca31d63`, ~1.3–2.6× step-identical,
  hard-gate green, forensic-verified live).
- **Discipline held throughout:** isnil over-conclusion retracted
  mid-stream; χ verdict-wiring bug caught & fixed before any claim;
  every Eng §-citation verified verbatim by audit 03. The property
  that makes this not "slop": it retracts itself.

## 2. HIGHEST-LEVERAGE NEXT (prioritized; all reference-`iex`-gated)

| # | Win | Source | Measured/expected | Risk | Verdict |
|---|---|---|---|---|---|
| 1 | **Incremental `psi_csyms`** — kill the O(steps²) full-Ψ rebuild | D-W1 | **81%** of binarith large-run wall; ~4–5× on Ψ-growing corpora | byte-identical (feeds only the colour gate already proven identical) | **DO-NOW (biggest single win)** |
| 2 | **Galaxy `IexAccel` hoist** — `build_accel`/`iex_fast_with_accel` (exist, proven) instead of 106× rebuild/[triple] | D-W2 | **~25%** of galaxy `eval_forced` | zero (pure hoist of a pure-fn-of-Φ) | **DO-NOW (trivial, stacks w/ Σ(Φ))** |
| 3 | **Lock-free `term::get` snapshot read path** | D-W3 | **73%** of galaxy wall is here (kernel residualised away; ceiling moved to the store RwLock+clone) | value-identical (append-only post-intern) | do-now-ish; bigger build; [hyp] 1.5–2.5× — add a `T_GET` probe first |
| 4 | **Discrimination/substitution-tree index** on Φ-neg rays | C-#1 | collapses the ~30% `find` phase / 392 δ-heads | gated by `index.rs::assert_oracle_equiv` | staged (complements #1; the named KS lever) |
| 5 | **rayon over the `produce_stars_fast` summand fan** | F | fuse ≈82% galaxy wall; N independent unifies/step | faithful by the *existing* `psi_compatible` gate (α-multiset) | staged (the one real data-parallel lever; serial union-find is the wall) |
| 6 | **χ Stage-2/3: the χ FUNCTIONAL** — quantify the charge; recurrence-form χ (span≥2) | A + docs/08 §4.5/§4.6 | the past-Eng research frontier, now on *measured* ground | new module, differential-gated; the make-or-break valence claim | research (the thesis-nearest deep track) |

Compounding note (docs/11 Fact-1): #1–#5 are bounded per-step levers;
they multiply with Σ(Φ) and each other but **cannot** cross a
termination boundary — by-design, the galaxy negative is closed, this
is throughput on what runs.

## 3. DEAD ENDS — proven/measured-negative, do NOT revisit

- **Termination-crossers for galaxy data[0]** — interaction-net (H1)
  and KA2 (H2): both evidence-negative (`c8cb09e` + the calibrated
  recurrence run). docs/16 §7.
- **Tractable faithful AEx** — *proven* impossible (Agent B,
  `docs/explore/tractable-aex.md`). The §57.13/§74.11 obligation is
  not dischargeable by execution; IEx-grounded + theorem-calibrated is
  the only sound path.
- **open-hypergraphs as implementation vehicle** — corroborated
  wrong-here (Agent F; local path absent, crate rewrite machinery is
  `experimental`-gated); useful only as a mental model. docs/10 holds.
- **GRIN native codegen** — rejected (docs/16; breaks the trusted/
  deopt boundary for a per-step constant).
- **2nd/3rd Futamura projection** — zero engine merit, expository only
  (audit 04); `SpecPhi::build` is a legit 1st-projection residual,
  "cogen-of-one" is a category error.

## 4. OPEN — genuine, recorded

- **χ functional quantification** (Stage-2/3): the integrated surplus
  / GoI non-nilpotency-degree (§4.5/§4.6), and the *recurrence-form* χ
  (a span≥2 sound non-trivial whistle — not yet exhibited; F3's was
  span-1). The valence make-or-break, now on solid measured ground.
- **User's KG6c `force_value` memo-ordering edit** (uncommitted in
  `galaxy.rs`): consult `FORCE_MEMO` before the `budget==0→Residual`
  bail. Plausibly sound + valuable, but an unverified engine hot-path
  change — must pass the galaxy/iex faithfulness gate as its own
  scrutinised commit before it lands. Not reverted (intentional).
- **Website divergent-site line** (`c16bde9`): reconciling two
  divergent `site/` histories — deferred, a branch-management call.

## 5. Honest headline + immediate sequence

The arc graduated: galaxy-execution is a closed (now *proven*-closed)
honest negative; the engine became a fast, faithful, **calibrated
platform**; and the past-Eng frontier delivered its first measured
result — χ exhibited on Eng's own §49.61 witness. The work survives
the thesis author poking it precisely because the faithfulness gates
are load-bearing, not ceremony.

Recommended immediate order: **#2 (trivial, zero-risk, stacks)** →
**#1 (biggest measured win, byte-identical)** → gate the user's KG6c
edit → **#6 χ functional** (the research frontier) in parallel with
**#3/#4/#5** (throughput). No termination-crosser; no AEx; no OHG.
