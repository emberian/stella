# Thesis Audit 02 — Execution Machinery: §57 Push/Krivine Machine, AEx, §49.52–49.60 Iterated Execution & Idempotence

**Status:** READ-ONLY audit. No code or other docs edited.
**Scope:** Eng's *execution* apparatus vs this codebase. Sources cross-checked:
`docs/eng-digest-ch8.md` (§56–60 machines, §57 KAM), `docs/eng-digest-ch10.md`
(§66–72 AEx for MLL), `docs/eng-digest-ch11.md` (§74 AEx for MLL2I),
`docs/eng-digest-ch12-13.md` (§87.2 KAM punt, §87.6 token machine),
`docs/05-combinator-core-and-the-kam-escape.md`,
`docs/08-forcing-polarity-design.md`. Codebase:
`crates/stella-core/src/{interactive.rs, spec_phi.rs, galaxy.rs, galaxy_decode.rs,
combinator.rs, execution.rs, subjective.rs, ch9.rs, accel_detect.rs}`.

A note on the abstraction Eng uses for *every* execution-faithfulness theorem
in Ch10–11: cut-elimination and DR-correctness are stated with **AEx** (abstract
execution / saturated-diagram enumeration), explicitly *not* IEx. §74.11 verbatim:
"The simulation uses AEx (abstract execution), not IEx (interactive execution)."
The combinator/galaxy/KAM track in this repo runs almost entirely on **IEx**
(`iex_fast`) plus a host forcing loop. That divergence is the spine of this audit.

---

## Per-concept status table

| Execution concept | Status | Primary site |
|---|---|---|
| Push unwind (§57.19 `[−P(a(M,N)⋆π),+P(M⋆N·π)]`) | **implemented** | `combinator.rs:151`; `galaxy.rs:423`; `spec_phi.rs` `Transition::Unwind` (`spec_phi.rs:129`) |
| δ-resolution (named-def rewrite `:N ↦ body`) | **implemented** | `galaxy.rs:398` `delta_star`; `spec_phi.rs:147` `Transition::Delta` |
| Combinator splice (Grab-replacement first-order rule per `{S,B,C,I,T,F}`) | **implemented** | `combinator.rs:147` `machine_stars`; `galaxy.rs:417` `prim_stars`; `spec_phi.rs:150` `Transition::Splice` |
| KAM call/cc (Save/Restore, §57.13 `[−P(cc⋆M·π),+P(M⋆k_π·π)]` …) | **absent** | nowhere — no `cc`/`k_π`/Save/Restore symbol in `combinator.rs` or `galaxy.rs` |
| AEx layer (saturated-diagram abstract execution, §49.42/§50.7) | **implemented but off the KAM path** | `execution.rs:319` `aex`, `:396` `aex_seminaive`, `concrete.rs` CEx; *not* used by `eval_forced`/galaxy |
| Idempotence §49.55–57 (objective ⇒ `AEx∘AEx=AEx`) | **partial (structural classifier only)** | `ch9.rs:235` `saturation_profile`; no runtime idempotence check on the KAM fragment |
| Iterated execution §49.52 (`AEx^{n+1}=AEx(Ψ'⊎AEx^n)`) | **partial / two disjoint instances** | `subjective.rs:287` generational rounds (animist stream); `galaxy.rs:925` `eval_forced` loop (host forcing) — *neither is AEx-based* |
| Non-termination §49.60 (hyperexecution may never normalise) | **partial (detector exists, unwired)** | `accel_detect.rs:94` `detect_recurrence` (Kruskal whistle); `eval_forced` uses an engineering `max_forcings` cap, not §49.59 |
| Strict / §58–60 forcing boundary | **implemented as a disclosed host concession** | `galaxy.rs:530–999` `strict_redex_on_pi`/`force_value`/`drive_strict`; `combinator.rs` has none (pure-lazy) |

---

## 1. Push unwind — faithful

`combinator.rs:151` and `galaxy.rs:423` both encode the Push star exactly as
§57.19: `[−P(a(M,N)⋆π), +P(M⋆N·π)]`, with `a`/`st`/`dot`/`±P` constructors shared
across `combinator.rs`, `galaxy.rs`, `spec_phi.rs` so the term universe is one.
`spec_phi.rs:129` re-derives the same rule *structurally* (`Mn = a(_,_)` ⇒
`Transition::Unwind`), and `spec_realise` (`interactive.rs:1018`) reads `M,N` off
the focus and rebuilds `M⋆(N·π)` — the verbatim KAM unwind as a Futamura residual.

**Divergence vs Eng:** none in the rule itself. The *deletion* is principled and
pre-registered (docs/05 §2): Eng's §57.16 Grab `[−P(l(X,M)⋆N·π),+P(M⋆π),+i(X,N)]`
mints a runtime `+i(n,u)` explicit-substitution star — the unscoped-binder hazard
Eng could not close (§57.15, §87.2). The codebase replaces Grab with one
first-order rewrite star per combinator (the §58 label-star pattern), so the
binder-capture failure mode is structurally absent. This is the docs/05 escape,
faithfully realised. It is *not* a faithful KAM of λ-terms — it is a faithful
machine for the binder-free combinator fragment, which is the honest claim.

## 2. δ-resolution — faithful, beyond Eng's pavement (legitimately)

`galaxy.rs:398` `delta_star` builds `[−P(st(:N,π)), +P(st(body•,π))]` per named
definition. Eng's Ch8 has no δ/named-definition machine — this is the docs/05
KG2 extension (a δ-star = a 0-arity constant head with a closed contractum). It
is sound by construction: `spec_phi.rs` proves δ bodies are `is_ground`
(`spec_phi.rs:293` test), so the MGU is definitionally `{π ↦ actual stack}` with
no α-rename/unify. **No faithfulness divergence** — it is a conservative
extension of the Push machine, correctly outside Eng's metatheory and marked so.

## 3. Combinator splice — faithful for `{S,B,C,I,T,F}`; `S` is the only non-linear star

`combinator.rs:181` `S` duplicates `Z` (`a(a(X,Z),a(Y,Z))`). Per docs/05 §2 this
is the single non-linear star and the known AEx-blowup axis (N-K4). All others are
linear. The galaxy `prim_stars` (`galaxy.rs:417`) additionally Church-encodes
`cons/car/cdr/nil` and *two value-guarded* `isnil` rules; `spec_phi.rs:284`
correctly *excludes* `isnil` from specialisation (constructor-guarded, not a bare
var frame) — that is the §49.50 boundary kept exactly where docs/08 wants it.

**Divergence vs Eng:** none for the rules; the faithfulness gap is the *execution
mode* (see §6), not the encoding.

## 4. KAM call/cc — ABSENT

Eng §57.13–57.20 gives Save `[−P(cc⋆M·π),+P(M⋆k_π·π)]` and Restore
`[−P(k_π⋆M·π'),+P(M⋆π)]`. **Nothing in the codebase implements these.** No `cc`,
`k_π`, Save, or Restore symbol exists in `combinator.rs` or `galaxy.rs`. This is
consistent with docs/eng-digest-ch8.md §57.13 ("Implement LAST / optional",
"no simulation result") and the docs/05 scope, and `galaxy.txt` is pure
`{S,B,C,I,T,F}` + list/arith with no `cc`, so the entire ICFP workload does not
need it. **Status: absent by design, correctly scoped, not a defect** — but it
*is* a genuine gap vs Eng's stated §57 machine (the continuation half of the
Krivine machine is unmodelled, so the "KAM constellation" claim is really a
"Push+δ+splice constellation" claim; call/cc-using λ-terms are out of reach).

## 5. AEx layer — implemented, but the KAM track does not use it (the central divergence)

`execution.rs` has a real, oracle-grade AEx: `saturated_diagrams` (§50.5
construction-space iteration), `aex`/`aex_with_strategy` (filter correct + 
actualise), a semi-naive worklist fixpoint `aex_seminaive` with dedup-on-insert,
and `concrete.rs` CEx invoking the same machinery per §50.7
(`CEx_C(Φ)=AEx_C(Φ)`). This is faithful to §49.42/§50.

**The divergence:** every Ch10–11 *theorem* (cut-elimination simulation §67.10,
§74.11; DR correctness §68.19) is stated for **AEx**. But the combinator/galaxy
KAM evaluator (`combinator.rs:233` `normalize`, `galaxy.rs:925` `eval_forced`)
runs **IEx** (`iex`/`iex_fast`) — a deterministic left-to-right *single-diagram*
strategy (`interactive.rs:855–911`), explicitly an SLD-style depth-first walk,
not the saturated-diagram enumeration AEx performs. The repo's own justification
(docs/05 §8, docs/08 §2.2) is that the objective combinator fragment is confluent
(§49.55) so call-by-name IEx reaches the unique normal form and "the loop *is*
`AEx^n`". **That equivalence is asserted, never demonstrated in code.** docs/08
§7 flags the exact unresolved question: "whether `eval_forced`'s per-loop-turn
`final_ray` is a faithful proxy for an `AEx`-layer boundary … not proven here."
So Push/δ/splice are individually Eng-faithful rules, but the *claim that running
them under IEx computes the AEx normal form Eng's theorems are about* is the
single largest open faithfulness obligation in the execution machinery — and it
is the obligation Eng's own §57.13 disavowal is precisely about.

## 6. Strict / §58–60 forcing boundary — a disclosed host concession; the §60 strategy punt bites

`galaxy.rs` `strict_redex_on_pi`/`force_value`/`drive_strict` (lines 530–999)
implement exactly the §58/§87.2 punt the digests flag as BROKEN/unfaithful:
strict ops (`add mul eq lt div neg`, and `isnil` on an unforced scrutinee) have
*no stellar star*; the host detects the Push-form redex, recursively forces
operands via a sub-`eval_forced`, and computes the kernel via `sbinarith`
(host-i128). The module doc is honest about this ("the only host acts are
deciding to force … and computing the numeric kernel … a disclosed §60
concession"). Eng §58 (`docs/eng-digest-ch8.md`): the criterion is **`ɟAEx(C★ ⊎
M★)`** — AEx, with label-star modules; §87.2/§88.2 say "nothing specifies this
synchronised flow of computation in constellations" and "only interactive
execution is feasible." The codebase's `drive_strict` *is* the externalised §60
strategy (embershot's `ForceArgs`), and docs/05 N-K2/N-KG1 pre-register this as
a finding-about-the-punt, not a win. **Faithfulness divergence vs Eng: the
strict-op semantics live in Rust/`sbinarith`, not in stellar resolution.** This
is correctly disclosed (not smuggled), and docs/05 §10.2 reframes the i128
kernel as a legitimate *jet/intrinsic* behind the differential oracle. The honest
characterisation: the *pure-lazy* fragment is stellar; the *strict numeric*
fragment is a host oracle wearing a §60-strategy hat.

## 7. Idempotence §49.55–57 and iterated execution §49.52 — two disjoint partial models, neither on the KAM path

Eng §49.52: `AEx^{n+1} = AEx(Ψ' ⊎ AEx^n)`; §49.55–57: objective ⇒ idempotent,
lost under subjective rays; §49.59–60: hyperexecution termination is *open*.

Three separate code regions touch this, none unified:

1. **`subjective.rs:287`** implements §49.52 as *generational rounds* over an
   animist star stream (round = "all current-gen stars consumed"). This is a
   faithful streaming reading of §49.52 *for the subjective/animist fragment* —
   but it operates on `one_step` self-interaction, **not** on the KAM/galaxy
   evaluator and **not** via `execution.rs::aex`. So §49.52 exists, but not for
   the execution track this audit targets.
2. **`galaxy.rs:925` `eval_forced`** outer loop is docs/08 §2.2's claimed
   `AEx^n` (force → `drive_strict` mints a ray → resume). docs/08 §2.3 itself
   marks the loop-stop as `[Proto]` ("Eng leaves termination open; `max_forcings`
   is an engineering cap, not a theorem"). It is *iterated execution in spirit*
   but: (a) the inner step is IEx not AEx; (b) the ray-minting is host-side
   (`drive_strict`), i.e. §49.50 characteristic (1) is externalised, not
   produced by internal polarities as Eng's mechanism requires.
3. **`ch9.rs:235`** classifies a constellation `Terminating` (objective,
   §49.55-idempotent) vs `NonTerminatingCandidate` *structurally*, without
   running saturation. It correctly cites §49.55/§49.57 but the test comments
   (`ch9.rs:317`) show it conservatively flags even `add 1+1` as
   `NonTerminatingCandidate` — so it does not actually certify the combinator
   fragment objective/idempotent. **The docs/05 K-SIM claim "objective-fragment
   properties (no `i`-rays; §49.55 idempotence) hold for `K★`" is asserted, not
   machine-checked**: there is no test that `aex(machine_stars())` is idempotent,
   nor that the galaxy Φ is `i`-ray-free and idempotent.

**Non-termination §49.60:** `accel_detect.rs:94` `detect_recurrence` is a
faithful Kruskal-whistle detector (the wqo argument is exactly §49.60's
"always pairs of matchable rays"). docs/08 §3.1 proposes the biconditional
*idempotence-loss ⟺ whistle*. **It is unwired:** `galaxy.rs:710` has the
`LAYER_TRACE` Stage-1 tap (canonical readback per force layer) but nothing
feeds it into `detect_recurrence`; `is_subjective` (docs/08 Stage 0 predicate,
the cheapest kill-switch) **does not exist** in `polarised.rs`. So §49.60 is
*detectable in principle, not connected to the KAM evaluator in practice*.

---

## Evaluation-order / strictness decisions: code vs Eng

docs/05 §10.1 names the review defects D1–D7; they live in `galaxy.rs`. What the
code decides, against what Eng mandates:

- **D-class root cause (galaxy.rs:539–547, the "CRITICAL STRUCTURAL FACT"):** the
  KAM Push rule *always* uncurries an operator's args onto π before the head is
  examined, so every strict op blocks in Push-stack form `+P(st(OP,a·b·…·π))`,
  never the curried `a(a(OP,a),b)`. The unified `strict_redex_on_pi` detector
  fixes the old per-prim curried+Push duality (D2/D3: scanning operands forced a
  **non-leftmost redex** = an evaluation-order deviation vs the reference oracle).
  This is now **leftmost/call-by-name**, which is the *correct* order for the
  confluent objective fragment (Eng §49.55: confluence ⇒ call-by-name reaches the
  normal form). Faithful decision.
- **D6 (galaxy.rs:705):** `force_value` recurses with a strictly decremented
  `budget` ⇒ well-founded by construction. Sound; no Eng mandate, an engineering
  termination guard (the §49.59 cap).
- **D7 (galaxy.rs:717–722):** a list constructor is committed only if the
  sub-evaluation `fully_reduced`. This is the faithful refusal to read a value
  off a not-yet-normal readback — aligns with Eng's "normal form" being a real
  fixpoint, not a truncation.
- **D1 (galaxy.rs:640, `galaxy_bool`):** `sbinarith` `tt`/`ff` → galaxy `t`/`f`
  at the single production point. Pragmatic host-boundary plumbing; no Eng
  analogue (these tokens don't exist in stellar resolution — part of the §6
  host-oracle boundary).
- **Strategy vs Eng:** `iex`/`iex_fast` pick the *first* coloured ray
  left-to-right (`interactive.rs:882`, `:1295`). Eng §51.20: IEx normal form is
  non-deterministic over orderings; §55.6: Horn is deterministic after query
  selection. So the chosen strategy is *one* of Eng's admissible strategies and
  is correct *only because* the fragment is confluent — exactly the assumption
  that is asserted (docs/05 §2) but never machine-verified (§7 above). The
  `iex_fast`/`iex_tabled`/`iex_spec` tier is differential-gated against reference
  `iex` (`interactive.rs:1704` `iex_fast_result_eq_iex`), which is the repo's
  N-KS discipline — sound for *engine equivalence*, silent on *AEx equivalence*.

---

## Encodable experiments + missing infra

**Missing infra (in priority order):**
1. No idempotence assertion on the KAM Φ: there is no test
   `aex(machine_stars())` ≅ `aex(aex(machine_stars()))`, nor an `is_subjective`
   predicate (docs/08 Stage 0) to certify `K★`/galaxy-Φ objective + `i`-ray-free.
2. No bridge from `eval_forced`'s `LAYER_TRACE` (galaxy.rs:710) to
   `accel_detect::detect_recurrence` — the docs/08 §3.1 load-bearing experiment
   has its tap and its detector both built but not connected.
3. No AEx-vs-IEx differential on the combinator fragment: nothing runs the same
   small combinator term through `execution::aex(machine_stars(), …)` and
   `combinator::normalize` and compares — the one check that would substantiate
   the "IEx loop = AEx^n" claim Eng's theorems require.
4. No `is_subjective` ray predicate (the cheapest kill-switch for the whole
   forcing=§49.50-polarity identification).

**Highest-value encodable experiments:**
- *(E1, the most valuable — see below.)*
- E2: docs/08 Stage 0 — add `is_subjective` to `polarised.rs`, assert it is
  true on every `strict_redex_on_pi` disclosed ray across the galaxy corpus;
  false ⇒ the forcing≠subjective-ray grounding is wrong (kills the docs/08 track
  cheaply).
- E3: wire `LAYER_TRACE` → `detect_recurrence`, run on the galaxy corpus, record
  whether the whistle blows exactly at the first `drive_strict` that re-opens a
  `±P` match (docs/08 §3.1 biconditional).
- E4: classify `machine_stars()` and the galaxy Φ with `ch9::saturation_profile`
  and *also* an idempotence run; if `ch9` returns `NonTerminatingCandidate` for
  the provably-confluent `{S,B,C,I,T,F}` core, that is a first-class finding
  about the conservativeness of the structural classifier (N-K3 territory).

---

## Return summary

### 3–5 highest-value gaps

1. **AEx-vs-IEx equivalence is asserted, never demonstrated — and it is exactly
   Eng's §57.13 disavowal.** Every Ch10–11 simulation/correctness theorem is
   AEx-stated; the combinator/galaxy KAM runs IEx + a host loop. `execution.rs`
   has a faithful AEx that the KAM path never touches. docs/08 §7 itself flags
   the unproven layer-boundary coincidence. This is the single largest
   faithfulness obligation in the execution machinery.

2. **No machine-checked idempotence / objectivity for `K★`.** docs/05 K-SIM
   *claims* "no `i`-rays; §49.55 idempotence" for the combinator Φ, but
   `ch9.rs` only does a conservative structural classification (flags even
   `1+1` non-terminating) and there is no `aex∘aex = aex` test and no
   `is_subjective` predicate. The objective-fragment property the whole escape
   rests on is unverified.

3. **Strict-op semantics are a host oracle, not stellar resolution (the §58/§60
   punt, correctly disclosed).** `drive_strict`+`sbinarith` compute
   `add/mul/eq/lt/div/neg` in Rust; this is the §87.2/§88.2 "nothing specifies
   synchronised flow in constellations" punt biting at galaxy scale. Honestly
   ledgered as a finding, but it means "galaxy executes as stellar resolution"
   is true only for the pure-lazy fragment.

4. **KAM call/cc (Save/Restore) is entirely absent.** The continuation half of
   Eng's §57 machine is unmodelled. Correctly out of scope for `galaxy.txt`, but
   the "KAM constellation" is really "Push+δ+splice"; call/cc λ-terms are
   unreachable.

5. **The §49.50/§49.52/§49.60 apparatus is built but fragmented and unwired to
   the KAM path.** `subjective.rs` §49.52 rounds (animist stream only),
   `accel_detect` whistle (unconnected to `eval_forced`), `LAYER_TRACE` tap
   (no consumer), `is_subjective` (missing). Three partial models, none on the
   evaluator the audit targets.

### Most valuable encodable experiment

**E1 — AEx/IEx differential on the combinator core (directly attacks gap #1 and
substantiates or falsifies K-SIM):** for a fixed battery of closed
`{S,B,C,I,T,F}` terms with hand-derived normal forms (docs/05 §4 battery), run
each through (a) `execution::aex` over `combinator::machine_stars()` (the
saturated-diagram AEx Eng's theorems are stated for) and (b)
`combinator::normalize` (IEx), and assert the ɟ-readout (`conceal_and_filter` /
`read_value`) agrees with the hand-derived `enc(v)` on *both*. This is small
(infra all exists: `aex`, `machine_stars`, `normalize`, the §4 battery), needs
no new theory, and is the single check that converts the repo's load-bearing
"IEx loop = AEx^n on the confluent objective fragment" *assertion* into a
falsifiable, differentially-gated *result* — exactly the simulation evidence
§57.13 says Eng never established. A divergence on any term is a first-class
negative (N-K1: "the encoding is not faithfully objective"); agreement across
the battery is the strongest available substantiation of the docs/05 escape
short of the HOL4 K-SIM proof.
