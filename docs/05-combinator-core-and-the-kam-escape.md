# 05 — The Binder-Free Combinator Core (Eng's Unbuilt KAM Escape)

**Status: CANONICAL spec for the `stella-combinator` subproject. K1–K4 frozen strengthen-only.**
Spec-grade, PDF-free for workers. All Eng citations are §-numbers verifiable in
`refs/extracted/EngExegesis/doc.md`. Companion to `docs/00` (term/unification/AEx-IEx)
and `docs/eng-digest-ch8.md` (§57 KAM digest, §58 circuits/label-stars).

---

## 1. Why this subproject exists

Eng encodes eight machine classes in Ch8 with simulation theorems. The **ninth, the
Krivine Abstract Machine (KAM), he could not close.** His own words:

- **§57.13** (verbatim): *"I had the idea to encode it into constellations but I am
  not very confident about the details. In this section, I only give the definitions
  without establishing any simulation result."*
- **§57.15** (verbatim, the precise failure): *"we consider that variables under some
  scope of a λ do not appear under another scope: there is no possible capture of
  variables… I tried to take scopes into account so that it would work for any λ-term
  but it was horrible to define and too technical to be understandable."*
- **§87.2** (verbatim, the Limits/Horizons admission + the escape): *"I tried to encode
  the Krivine Abstract Machine in Section 57 but I did not prove that the encoding is
  faithful and correctly simulates it. When I tried, I was under the impression that it
  was possible to define λ-calculus directly by encoding its term graph and using the
  mechanisms of stellar resolution (variable and constants) to simulate explicit
  substitutions."*

**Diagnosis.** The punt is *binding*, not call/cc. In §57.16–57.19 a variable
occurrence is a star `x★_α = [−i(σ(x),ν(x)), +T_α(x•)]`; the binding ray `−i(n,X)` is
an *explicit substitution waiting for a value* (§57.18 proof); β-reduction
(§57.17) is the star `[−T_α(a(l(n,X),u)), +T_α(X)] + [+i(n,u)]` which **creates a fresh
`[+i(n,u)]` star at runtime**. Because `i`-rays are global to the constellation and
**unscoped**, any re-activation of identifier `n` (recursion, fixpoint, non-linear
reuse) makes every `−i(n,·)` occurrence unify with *any* coexisting `[+i(n,·)]` — no
innermost discipline. Eng's only repair (global pre-renaming, no capture) holds solely
for terms reduced without binder re-entry. Hence no simulation theorem. The runtime
`[+i(n,u)]` creation is itself §49.50 subjective-ray behaviour, outside the Ch9
objective metatheory that certifies the other eight machines.

**The escape (Eng's own, §87.2).** Encode the *term graph* directly; let stellar
unification *be* the substitution mechanism. **Bracket-abstracted combinators have no
binders at all** — the capture problem Eng found "horrible" structurally cannot arise
(this is precisely why Turner combinators were invented: graph reduction without
environments). `~/dev/embershot` (ICFP-2020 contest runtime, eval/apply transcription
of Marlow–SPJ) is a concrete working instance of this escape: its corpus
`src/galaxy.txt` is pure `{S,B,C,I,T,F}`-combinator code, zero `λ`, zero `cc`.

**Deliverable.** The faithful simulation theorem Eng explicitly did *not* establish
(§57.13), for the binder-free fragment, dual-track (Rust prototype + HOL4 statement).
Payoff: a verified path to **compile real combinator programs into stellar resolution**.

---

## 2. The encoding (Eng §57.16/§57.19 apparatus, binder machinery deleted)

Combinator basis = embershot's primitive set: `{S, B, C, I, T, F}` (`T`=K/true,
`F`=false; `machine.rs` `Primitive`). `cons/car/cdr/nil/isnil` are **not new
primitives** — embershot itself Church-encodes them via `T`/`F`
(`machine.rs:693`: `Car => aa(args[0], T)`), so they fall out of the basis.

**Term-graph translation** — §57.16 *verbatim with the `−i` row deleted* (no
variables ⇒ no explicit-substitution rays ⇒ the entire thing Eng could not scope is
absent by construction):

```text
c•          := c                         (combinator constant)
(M N)•       := a(M•, N•)                  (verbatim §57.16)
c★_α         := [+T_α(c)]
(M N)★_α     := M★_{α·0} + N★_{α·1} + [−T_{α·0}(X), −T_{α·1}(Y), +T_α(a(X,Y))]
(M ⋆ π)★     := Ex( M★_ε + π★ + [−T_ε(X), −S(Y), +P(X⋆Y)] )     (verbatim §57.16)
ε★           := [+S(ε)]
```

**Machine constellation** `K★` — Eng's **Push verbatim §57.19**; Grab replaced by one
first-order rewrite star per combinator (the §58 label-star pattern — *not* the punted
`l`/`+i(X,N)` Grab):

```text
Push    [−P(a(M,N)⋆π),   +P(M⋆N·π)]                      (verbatim §57.19)
I       [−P(I⋆X·π),       +P(X⋆π)]
T(=K)   [−P(T⋆X·Y·π),     +P(X⋆π)]
F       [−P(F⋆X·Y·π),     +P(Y⋆π)]
B       [−P(B⋆X·Y·Z·π),   +P(a(X,a(Y,Z))⋆π)]
C       [−P(C⋆X·Y·Z·π),   +P(a(a(X,Z),Y)⋆π)]
S       [−P(S⋆X·Y·Z·π),   +P(a(a(X,Z),a(Y,Z))⋆π)]        ← Z duplicated: only non-linear star
```

Properties (to be *proved*, not assumed — see §5): each combinator star carries **zero
`i`-rays**, is a single first-order rule ⇒ lives in the **objective fragment** ⇒ §49.55
idempotent, Ch9 (non-)termination-classifiable. Combinator reduction is confluent, so
**call-by-name** here computes the correct normal form; sharing is *only* efficiency
and is deliberately excluded from the faithful core (§3 OUT).

---

## 3. Scope boundary (pre-registered, honest)

**IN — v1 faithful core (K1):**
- Pure `{S,B,C,I,T,F}` reduction + Church-encoded data (lists/booleans), call-by-name.
- Term-graph encoding §2; result read via a pre-registered `ɟ`-criterion (K1 defines it).

**IN — v1 arithmetic (K2), with disclosed risk:**
- Numbers/arithmetic via a **§58-style label-star module** `M★` (Eng's own boolean-module
  pattern, `circuits.rs`): one oracle star per `⟦op⟧`, criterion `IEx(op★,[−op(a⃗,Y⃗),Y⃗])=[b⃗]`.
- **DISCLOSED:** this re-enters Eng's §58/§87.2 *faithful-circuits* punt — "nothing
  specifies this synchronised flow of computation in constellations" — which project
  memory already tracks as **§58 BROKEN/unfaithful** (free vars not ground `val`). It is
  a *named in-scope risk*, NOT claimed clean. Strict-primitive arg-synchronisation
  (embershot's `ForceArgs`) is exactly this problem; K2 must inspect-don't-trust any
  green (the Member-6 / verify-don't-trust discipline) and ledger the synchronisation
  obligation explicitly. If arithmetic only works under hand-ordered arg evaluation,
  that is a **first-class finding about the §58 punt**, not a v1 success.

**OUT — deferred, = Eng's other two §87.2 punts (named probes, never smuggled):**
- Call-by-need **sharing** (embershot `UpdThunk`/`Blackhole`) → subjective rays
  §87.2/§49.50; this is `subjective.rs`/§74.7 territory, re-entered later as a named phase.
- Full faithful strict synchronisation beyond the K2 disclosure → §58/§87.2.

---

## 4. Faithfulness discipline (verify-don't-trust)

embershot is **fully historical** (2018 edition, removed `std::option::NoneError`) — it
is **not** built or run. Faithfulness is anchored, in priority order:

1. **Eng's own worked examples** (PDF-grounded, primary): §22.8
   `(λxy.x)z ⋆ ε ↝* λy.z ⋆ ε`; §57.20 `(λxy.x)z`; plus standard combinator identities
   (`SKK x = x`, `S K K = I`, `B`/`C`/`T`/`F` laws, Church-list `car(cons a b)=a`).
2. **Hand-derived combinator normal forms** for a fixed test battery, derived in-spec.
3. **Optional differential oracle:** a *fresh, modern, minimal* call-by-name combinator
   reducer (a clean "embershot-ish kernel" written for this purpose — NOT the historical
   crate) stood up only if K2+ needs broader coverage for the "real programs" milestone.

Standing rule (project ethos): a green from the §58-module path is *deflated by
mandatory inspection* before it is ledgered (docs/03 lesson; positives most of all).
Nothing in this subproject is canonized without principal sign-off.

---

## 5. The target theorem (what Eng did not prove — §57.13)

> **K-SIM (binder-free combinator simulation).** For every closed `{S,B,C,I,T,F}`
> term `M` with combinator normal form `v` (call-by-name), the constellation
> `Ex( (M ⋆ ε)★  +  K★ [ +  M★_arith ] )` reduces under the chosen execution mode
> so that the pre-registered `ɟ`-criterion reads out exactly `enc(v)`; and the
> objective-fragment properties (no `i`-rays; §49.55 idempotence; Ch9
> classification) hold for `K★` restricted to `{S,B,C,I,T,F}`.

K-SIM is the simulation result §57.13 disavows, for the fragment §57.15's failure
does not touch. Stated and ledgered in HOL4 `stellaCombinator`; proof closed
main-thread per the dispatch protocol (no subagent proof-closing).

---

## 6. Decomposition

- **K1 — pure combinator core (Rust).** `combinator.rs` in `stella-core`: §2 encoding
  for `{S,B,C,I,T,F}` + term-graph translation + the `ɟ`-readout criterion; oracle =
  §4(1)(2) battery. Objective-fragment claims property-tested. No arithmetic.
- **K2 — arithmetic label-star module (Rust), risk-disclosed.** §58-pattern `M★` for
  embershot's strict ops (`add/mul/div/neg/eq/lt`, `inc/dec`); explicit
  synchronisation-obligation ledger; inspect-don't-trust harness.
- **K3 — HOL4 `stellaCombinator` scaffold.** State §2 encoding + K-SIM as a labelled
  REPORTED stub (proof main-thread, later). Parallel/disjoint/non-gating.
- **K4 — "real program" milestone.** A non-trivial galaxy-shaped combinator program
  end-to-end; differential oracle (§4(3)) if needed; honest perf note (S-duplication is
  a known AEx blowup axis — project memory; characterise, don't hide).

## 7. Pre-registered failure modes (nulls)

- **N-K1:** combinator core only normalises under hand-ordered redex selection / a
  bespoke strategy ⇒ the encoding is not faithfully objective. (Mirrors the §49.27 /
  AEx-blowup history.)
- **N-K2:** the §58 arithmetic module only yields ground results under hand-synchronised
  argument evaluation ⇒ Eng's §58/§87.2 synchronisation punt bites; ledger as a finding
  about the punt, not a v1 win.
- **N-K3:** `K★` for `{S,B,C,I,T,F}` cannot be shown `i`-ray-free / objective ⇒ the
  "escape sidesteps the binding punt" claim is false; first-class negative result.
- **N-K4:** S-combinator duplication makes realistic programs infeasible under AEx ⇒
  honest scope statement (regulation/strategy = Ch9/§60.8 territory), not concealment.

Falsification of any N is a result, recorded, not retro-weakened.

---

## 8. Galaxy fitness milestone & the fast-stellar lever (extension, 2026-05-17)

Strengthen-only addition; §§1–7 unchanged. Principal ruling (user, 2026-05-17):

**Architecture ruling — NO side reducer.** "A fast reducer on the side isn't
interesting; we already have galaxy reducers." `~/dev/embershot` and the ICFP
`galaxy.txt` exist to be the **demanding lever against which we hoist plain
stellar resolution itself** to interactive speed — that *is* the fitness
evidence. So: speed work targets the **stellar IEx engine**, not a foreign
executor. A specialized fast path for the deterministic single-thread
combinator/δ/arith redex shape is permitted **iff** it is a *verified jet* in
the Nock-jet / Ethereum-precompile sense: observationally identical to the
general `interaction_step`, swappable, with the **general engine retained as
the differential oracle** for every jetted step (the project's blessed
"Eng-literal as oracle, optimized engine proptest-fuzzed against it" pattern,
applied *inside* the engine — fast path vs reference path, not stellar vs
not-stellar). Galaxy running fast *as stellar resolution* is the deliverable;
if it cannot be made interactive, the measured speed/faithfulness frontier is
itself the honest first-class result.

**Validation target — vectors first, then UI.** Headless evaluator + the
`interact` protocol + known-good test vectors (rigorous, falsifiable) is the
fitness milestone; the clickable "Galaxy of Galaxies" UI is the demo built on
top afterward.

**Galaxy is in-fragment.** `galaxy.txt` = 393 defs `:N = <prefix-ap expr>`,
entry `galaxy = :1338`; vocabulary = exactly K1's `{S,B,C,I,T,F}` +
`cons/car/cdr/nil/isnil` + `add/mul/div/neg/eq/lt` + `:N` + signed bigints.
`:N` are **top-level constants, not binders** — galaxy never leaves the
binder-free objective fragment; the KAM punt stays sidestepped at galaxy scale.

### Phases

- **KG1 — binary signed bigint arithmetic.** Replace K2a's unary `sⁿ(z)`
  (N-K4: `O(value)`, galaxy has `123229502148636`, `-3`) with a faithful Horn
  module over a **binary** numeral representation (ripple-carry add, shift-add
  mul, recursive compare, sign-magnitude for `neg`/signed `add`/`div`).
  `O(#bits)`. IEx-driven, oracle = ground arithmetic; large-value + timing
  tests are the concrete N-K4 kill. *(KG1a unsigned add/mul/eq/lt/cmp; KG1b
  signed + neg + div.)*
- **KT — combinator testing hardening.** `proptest` differential: random
  combinator terms reduced by K1 vs an in-test SKI reference oracle;
  confluence / normal-form invariants; broadened law battery. Underpins trust
  in any KS fast path.
- **KG2 — named-def environment.** `:N` as δ-rule stars
  `[−P(:N⋆π), +P(body_N⋆π)]` (objective, binder-free, shared not inlined);
  parser for `galaxy.txt`; whole galaxy loads as one constellation.
- **KS — fast stellar (the lever).** Profile the IEx hot loop on the galaxy
  workload; head-indexed Φ matching (discrimination/fingerprint index — engine
  roadmap), no Ψ rescans, efficient subst/freshen; optional **verified jet**
  for the combinator/δ/arith step (general engine = differential oracle).
  `criterion` measured. This is where galaxy-at-interactive-rates is won or
  honestly falsified.
- **KG3 — galaxy harness + vectors.** `interact` protocol; initial state +
  scripted clicks; validate against a known-good reference and the stellar
  engine itself (via KS). UI = later demo.

### Pre-registered nulls (extension)

- **N-KG1:** binary arithmetic only matches ground truth under hand-canonical
  inputs / a bespoke strategy ⇒ not a faithful module.
- **N-KS (reframed 2026-05-17 — the correct jet invariant):** a verified jet
  is **result-equivalent**, not gas/step-identical (Nock jets aren't
  bit-identical in gas). Since the objective fragment is confluent (Eng §49.55,
  unique normal form), N-KS = for every input the fast path and the reference
  `iex` **both terminate or both diverge**, and when they terminate the
  ɟ-observable normal form (`conceal_and_filter` of final Ψ) is equal. The
  reference `iex` is retained as the differential oracle; byte-identical
  step-tests are kept additionally wherever the strategy is left unchanged. If
  result-equivalence fails the jet is reverted, not kept (Goodhart-forbidden).

### KS holistic architecture (the deterministic objective fragment)

Profiler-proven cost structure (release, `STELLA_KS_PROF`): per-step `find`
55–75 % (O(steps²) Ψ-rescan-from-zero + `Vec<Star>` rebuilt every step), `fuse`
18–40 % (`theta.apply` rebuilds every ray through the global `Mutex<TermStore>`),
`freshen` ~5 % (`format!`+lasso-intern per var/step), colour ~1 %. The found
first-symbol index + interned-colour + existence-split give a *faithful but
modest* x1.3–4.4 (Tier-0). The order-of-magnitude win is the holistic redesign
of the **fast path only** (reference engine untouched = oracle):

1. **Worklist selection** — agenda of active redex rays; no full Ψ rescan.
2. **Focused machine state** — the combinator/Horn IEx *is* an abstract
   machine (KAM-shaped for δ; SLD stack for Horn); run it as one, not a
   `Vec<Star>` rebuilt per step.
3. **Triangular/union-find substitution** — bind in an environment, deref
   lazily; no per-fuse term rebuild / no global store lock storm.
4. **Generation-tagged freshening** — fresh Φ copy = bumped integer
   generation; no strings, no interner.

Each lever lands independently, measured via `examples/ks_ab.rs` +
`STELLA_KS_PROF`, gated by reframed N-KS (result-equivalence vs the `iex`
oracle) + full suite. Measurement infra is permanent (project no-fake-done).
- **N-GAL:** even fast stellar cannot run galaxy at interactive rates ⇒ the
  measured frontier is the honest result; "fitness for purpose: not yet, here
  is exactly where and why" — not concealed, not a bespoke fast-reducer escape.
