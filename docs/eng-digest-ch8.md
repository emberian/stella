# Eng Digest — Chapter 8: Illustrating Stellar Resolution

Spec-grade extraction from Boris Eng, *An Exegesis of Transcendental Syntax*.
**This file is the PDF-free source for implementation workers. Do not open the PDF; cite §§ from here.**
Companion to the Ch 7 / App B / App C definitions already in `docs/00-thesis-and-semantics.md`.

## Notation (§53.10, §54, §56.2, §56.21)

- Primary execution mode in Ch 8 is **Interactive Execution (IEx)** with **`ɟ`** (concealing `↨` + noise-filter `♭`: erase polarised residue, keep unpolarised rays). Exceptions noted per machine.
- Word encoding (§56.2): `w = c₁…cₙ` over Σ ⇒ `w★ = [+i(c₁ · … · cₙ · ε)]`, `·` binary **right-associative**, `ε` constant.
- NTM word encoding (§56.21): same but `·` replaced by `○` (right-assoc); tape uses `●` **left-associative** for the left part.
- Acceptance pattern: `[accept] ∈ ɟIEx(M★, w★)` (criterion varies per machine; see each).

## §56 NFA (baseline, already implemented — `automata.rs`)

`A=(Σ,Q,Q₀,Δ,F)`: each `q₀∈Q₀` → `[−i(W), +a(W,q₀)]`; each `q_f∈F` → `[−a(ε,q_f), accept]`;
each `q'∈Δ(q,c)` → `[−a(c·W,q), +a(W,q')]` (c≠ε) or `[−a(W,q), +a(W,q')]` (c=ε).
Accept iff `[accept] ∈ ɟIEx(A★,w★)` (Thm §56.5). Mode: IEx+ɟ.

## §56 NPDA (§56.9–56.13)

`P=(Q,Σ,Γ,Δ,Q₀,$,F)`, `Δ:Q×Σ_ε×Γ_ε→P(Q×Γ_ε)`. Encoding `P★`:
- `q₀∈Q₀` → `[−i(W), +p(W,q₀,$)]`
- `q_f∈F` → `[−p(ε,q_f,S), accept]`
- `(q',b)∈Δ(q,c,a)`, with stack top `a` replaced by `b`:
  - `a=ε,b=ε`: `[−p(c·W,q,S), +p(W,q',S)]`
  - `a=ε,b≠ε`: `[−p(c·W,q,S), +p(W,q',b·S)]`
  - `a≠ε,b=ε`: `[−p(c·W,q,a·S), +p(W,q',S)]`
  - `a≠ε,b≠ε`: `[−p(c·W,q,a·S), +p(W,q',b·S)]`
  - `c=ε`: drop the `c·` (use `W` not `ε·W`).

Input `w★=[+i(c₁·…·cₙ·ε)]`. Accept iff `[accept]∈ɟIEx(P★,w★)`; reject ⇒ `[accept]∉` (Thm §56.13). Mode: IEx+ɟ.

**Worked example (Fig 56.2), {0ⁿ1ⁿ | n≥0}:**
`P★ = [−i(W),+p(W,q₀,$)] + [−p(ε,q₃,$),accept] + [−p(0·W,q₀,S),+p(W,q₀,0·S)] + [−p(1·W,q₀,0·S),+p(W,q₁,S)] + [−p(1·W,q₁,0·S),+p(W,q₁,S)] + [−p(W,q₁,$),+p(W,q₂,$)]`
(read 0 → push 0; read 1 → pop 0; reaching `$` means equal counts.)

## §56 NFST — finite sequential transducers (§56.15–56.18)

`T=(Σ,Γ,Q,Q₀,Δ,F)`, `Δ:Q×Σ_ε→P(Q×Γ_ε)`. Encoding:
- `q₀∈Q₀` → `[−i(W), +f(W,q₀,ε)]`
- `q_f∈F` → `[−f(ε,q_f,S), S]`  (outputs the accumulated stack `S` **unpolarised**)
- `(q',c')∈Δ(q,c)` → `[−f(c·W,q,S), +f(W,q',c'·S)]`; `c=ε` ⇒ `[−f(W,q,S),+f(W,q',c'·S)]`; `c'=ε` ⇒ `S` not `ε·S`.

Result = the unpolarised `[S]` star in `ɟIEx`. Mode: IEx+ɟ.

## §56 NTM — non-deterministic Turing machine (§56.19–56.25) — HEADLINE

Two-stack tape: term `m(L,Q,X,R)`. `L` left part (`●` left-assoc), `R` right part (`○` right-assoc),
`Q` current state, `X` symbol under head. Word encoding uses `○` (§56.21). `□` = blank.

Encoding `M★` of `M=(Q,Γ,Δ,q₀,q_a,q_r)`:
- `q₀` → `[−i(C ○ W), +m(□, q₀, C, W)] + [−i(□), +m(□, q₀, □, □)]`
- `q_a` → `[−m(L, q_a, X, R), accept]`
- `q_r` → `[−m(L, q_r, X, R), reject]`
- each `(q',c',d)∈Δ(q,c)`, `c∈Γ_□`:
  - `d=l` (left):  `[−m(L ● X, q, c, R), +m(L, q', X, c' ○ R)]`
  - `d=r` (right): `[−m(L, q, c, X ○ R), +m(L ● c', q', X, R)]`
  - `d=s` (stay):  `[−m(L, q, c, R), +m(L, q', c', R)]`
- two **memory-allocation** stars (dynamic tape `malloc`):
  `[−m(□, Q, C, R), +m(□ ● □, Q, C, R)] + [−m(L, Q, C, □), +m(L, Q, C, □ ○ □)]`

Input `w★=[+i(C ○ w)]` (w in `○`-encoding); empty word `[+i(□)]`.
Criterion (Thm §56.25): `M(w)=1 ⇒ [accept]∈Ψ`; `M(w)=0 ⇒ [reject]∈Ψ`; `M(w)=∞ ⇒ neither`, where `M★⊢w★ ↝* M★⊢Ψ`. Mode: IEx.
Function-computing variant: `q_a → [−m(L,q_a,X,R), accept(L,X,R)]` to output the tape.

## §57 ATM — alternating TM (§57.1–57.6)

NTM + `class:Q→{∨,∧}`. `q₀,q_a,q_r` as NTM. `∨`-successor transitions: same star shape as NTM.
`∧`-successor with k branches `(q_i,c_i,d_i)`: one star with **k positive outputs**, e.g. (left):
`[−m(L ● X, q', c', R), +m(L,q₁,X,c₁○R), …, +m(L,qₖ,X,cₖ○R)]` (right analogously with `L●cᵢ`).
Plus the two NTM malloc stars. Criterion (Thm §57.5): `M(w)=1 ⇒ [accept,k.,accept]∈Ψ`. Mode: IEx.
(∨ = non-deterministic ray choice; ∧ = branching star with multiple matchable rays.)

## §57 NFTA — non-det finite tree automata (§57.7–57.12)

Top-down `T=(Q,F,ar,Q₀,Δ)`, rules `q(f(x₁…xₙ)) → f(q₁(x₁)…qₙ(xₙ))`.
Tree encoding `t★`: leaf `x`→`X`; node `f(t₁…tₙ)`→`f(t₁★…tₙ★)`.
Encoding:
- `q₀∈Q₀` → `[−i(T), +ta(q₀,T)]`
- each rule → `[−ta(q,f(X₁…Xₙ)), +ta(q₁,X₁)] + … + [−ta(q,f(X₁…Xₙ)), +ta(qₙ,Xₙ)]`
- each leaf → `[−ta(q,X), accept]`

Criterion (Thm §57.11): `ɟEx(T★+t★) ≠ ∅ ⟺ T(t)=1`. Mode: **Ex (abstract) + ɟ** (not IEx).
Bottom-up = same with reversed polarities + final (not initial) states.

## §57 KAM with call/cc (§57.13–57.20)

Eng explicitly: "not very confident about the details… no simulation result." **Implement LAST / optional.**
KAM stars: `[−P(a(M,N)★π),+P(M★N·π)]` (Push); `[−P(l(X,M)★N·π),+P(M★π),+i(X,N)]` (Grab);
`[−P(cc★M·π),+P(M★k_π·π)]` (Save); `[−P(k_π★M·π'),+P(M★π)]` (Restore). λ-term encoding via §57.16.

## §58 Generalised circuits (§58.1–58.14)

Module `M=(X,L,ar,⟦·⟧)`. Boolean module example: `X={0,1}`; labels `0,1,s(1→2 dup),¬,∧,∨,c`.
Gate `e`, `in(e)={i₁…iₙ}`, `out(e)={o₁…oₘ}`:
`e★ := [−i₁(X₁), …, −iₙ(Xₙ), −κ(e)(X₁…Xₙ,Y₁…Yₘ), +o₁(Y₁), …, +oₘ(Yₘ)]`.
Output gate: drop the `−κ(e)(…)` call, keep `Y`s unpolarised.
Each label `l`: a star with `IEx(l★,[−l(a⃗,Y⃗),Y⃗])=[b⃗]` iff `⟦l⟧(a⃗)=b⃗`. `C★=Σe★`, `M★=Σl★`.
Criterion (Thm §58.14): `ɟAEx(C★ ⊎ M★) = [val(C)]`. Mode: **AEx + ɟ**.
Boolean module: `[+1(1)]+[+s(X,X,X)]+[+¬(1,0)]+[+¬(0,1)]+[+∧(1,X,X)]+[+∧(0,X,0)]` etc.

## §59 Tile systems / aTAM (§59.1–59.7)

Tile `tᵢ=(g_u,g_e,g_s,g_n)` → star with `ḣ/v̇/ḣ̊/v̊` rays + glue `gl(g)(X):=g(X)·str(g)`.
Environment constellation `Φ^τ_env` carries `+temp(τ̄)`, glue-match stars, and an embedded `add`/`geq`
sub-constellation enforcing "sum of bonded sides ≥ τ". Criterion (Thm §59.6):
`CSatDiags(T★+Φ^τ_env) ≃ A_□[T]`. Mode: **AEx via CSatDiags**.
Wang tiles = non-cooperative, τ=1, all strengths 0, no environment constellation.

## §60 Discussion (flag for the post-Eng frontier — do not act now)

Shared mechanism: information flowing along a discrete (hyper)graph; stellar resolution implements it
natively via unification. Stack-type taxonomy of automata (SD/SI/A). **Apodictic** (tile systems:
self-sufficient/permissionless) vs **epidictic** (circuits/logic programs: need externally provided
*strategies*). Eng: "no idea how to implement strategies in a satisfying generic way" — explicit open
problem; another marker of where Eng's paved road ends (relevant to the deferred subjective/animist work).
