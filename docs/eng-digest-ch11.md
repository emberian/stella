# Eng Ch. 11 Digest — Interpretation of Intuitionistic Implication
*Source: Boris Eng, "An Exegesis of Transcendental Syntax" (2023/2026 v2), Chapter 11, pp. 343–357.*

---

## Overview

Chapter 11 restricts the stellar interpretation of linear logic (Chapter 10) to **MLL with intuitionistic implication (MLL2I)**, which is MELL with the exponential fragment confined to intuitionistic implication only — Girard's choice per [Gir17, §5]. This avoids defining full exponentials `!` and `?` directly; instead, new binary connectives `A ⋊ B := ?A ⅋ B` and `A ⊛ B := !A ⊗ B` are introduced. The dual `(A ⇒ B)⊥` is equivalent to `A ⊛ B⊥`. MLL2I is sufficient to interpret simply-typed λ-calculus. No soundness/completeness results are stated.

---

## §73 MLL with Intuitionistic Implication (MLL2I) (p. 343/§73)

### MLL2I Sequent Calculus (p. 343–344/§73)

**§73.1** MLL2I is simply MELL with a different notation; there is no need to define separate cut-elimination for the sequent calculus. One unfolds the notation and works in MELL.

**Definition (MLL2I pre-formulas) (p. 344/§73.3).** The set of pre-formulas F^pre_MLL2I is defined inductively by:

    C, D  ::=  X_i  |  X_i^⊥  |  C ⊗ D  |  C ⅋ D  |  C ⊛ D  |  C ⋊ D     (i ∈ ℕ)

**Definition (MLL2I formulas) (p. 344/§73.4).** The set of formulas F_MLL2I is:

    A, B  ::=  C  |  C̲

where `C̲` (underlined) represents `?C`. The notation `?A` is written `A̲`, and underlined formulas appear only as top-level conclusions of sequents, not as subformulas.

**Rules of MLL2I (p. 344, Fig. 73.1):** The system includes:
- **cut**: `⊢ Γ, Δ, A   ⊢ Γ', Δ', A⊥  /  ⊢ Γ, Γ', Δ, Δ'`
- **ax**: `⊢ A, A⊥`
- **w** (weakening): `⊢ Γ, Δ  /  ⊢ Γ, Δ̲, A̲`
- **d** (dereliction): `⊢ Γ, Δ, A  /  ⊢ Γ, Δ̲, A̲`
- **c** (contraction): `⊢ Γ, Δ, A, A  /  ⊢ Γ, Δ̲, A̲`
- **⊗**: `⊢ Γ, Δ, A   ⊢ Γ', Δ', B  /  ⊢ Γ, Γ', Δ, Δ', A ⊗ B`
- **⅋**: `⊢ Γ, Δ, A, B  /  ⊢ Γ, Δ, A ⅋ B`
- **⊛**: `⊢ Δ, A   ⊢ Γ', Δ₁', B  /  ⊢ Γ', Δ̲, Δ₁', A ⊛ B`  (the left premise `⊢ Δ, A` corresponds to `⊢ ?Δ, !A`; promotion is implicit via the ⊛ rule)
- **⋊**: `⊢ Γ, Δ, A, B  /  ⊢ Γ, Δ, A ⋊ B`

**§73.5.** The promotion rule is implicit: in the ⊛ rule, the left premise `⊢ Δ, A` corresponds to `⊢ ?Δ, !A`. A cut between `A̲^⊥ := ?B^⊥` and a formula `A` implicitly has `A := !B`.

**Definition (Translation back to MELL) (p. 344/§73.6).** A translation `⌊·⌋` of MLL2I formulas into MELL formulas:
- If `A` is a pre-formula `C`: `⌊A⌋ := ⌊C⌋_pre`
- If `A` is an underlined pre-formula `C̲`: `⌊A⌋ := ?⌊C⌋_pre`

Translation of pre-formulas:

    ⌊X_i⌋_pre := X_i
    ⌊X_i^⊥⌋_pre := X_i^⊥
    ⌊C ⊗ D⌋_pre := ⌊C⌋_pre ⊗ ⌊D⌋_pre
    ⌊C ⅋ D⌋_pre := ⌊C⌋_pre ⅋ ⌊D⌋_pre
    ⌊C ⋊ D⌋_pre := ?⌊C⌋_pre ⅋ ⌊D⌋_pre
    ⌊C ⊛ D⌋_pre := !⌊C⌋_pre ⊗ ⌊D⌋_pre

**§73.7.** Cut-elimination for MLL2I (Fig. 73.2a) is similar to standard exponential rules. To apply cut-elimination on an MLL2I sequent proof, replace all formulas `A` by `⌊A⌋` and apply standard MELL rules.

### MLL2I Proof-Structures (p. 345–347/§73)

**§73.8.** MLL2I proof-structures differ from boxed presentations in that they have **explicit dependency links** between the left premise of ⊛ hyperedges and other vertices of the proof-structure. These links represent the dependency between a box and its isolated sub-proof-structures in the context (the context Δ in `⊢ Δ, A` of the ⊛ rule). Links to vertices already reachable from the left premise of ⊛ are omitted.

**Definition (MLL2I proof-structure) (p. 347/§73.9).** An MLL2I proof-structure is defined by

    S = (V, E, in, out, ℓ_E, dep)

where `(V, E, in, out)` is an ordered directed hypergraph (Appendix C), and:
- `ℓ_E : E → {⊗, ⅋, ax, cut, ⋊, ⊛, w, d, c}` is a labelling map on hyperedges;
- `dep : V → 𝒫(V)` associates vertices with left premises of ⊛ hyperedges (dependency relation).

Constraints:
- Hyperedges satisfy arities and labelling constraints in Fig. 73.3 (constructors shown: weakening `w` is nullary, dereliction `d` is unary, contraction `c` is binary; left-exponential par `⋊` and left-exponential tensor `⊛` are binary);
- Each vertex is the target of exactly one hyperedge, and source of at most one hyperedge;
- Cut hyperedges connect either: conclusion of a `⅋` hyperedge with conclusion of a `⊗` hyperedge, OR conclusion of a `⋊` hyperedge with conclusion of a `⊛` hyperedge, OR two atoms.

**Definition (Exponential box) (p. 347/§73.10).** For an MLL2I proof-structure `S := (V, E, in, out, ℓ_E, dep)`, the *(exponential) box* of a vertex `v` is given by an injective function `box : V → 𝒫(V) × 𝒫(E)` associating to each left premise `v` of an ⊛ hyperedge the sub-proof-structure corresponding to all vertices and edges connected (by non-oriented paths) to `v` and all vertices of `dep(v)`.

**§73.11 Convention.** `⋊` and `⊛` hyperedges are structurally identical to `⅋` and `⊗` hyperedges respectively.

**Definition (MLL2I cut-elimination) (p. 347–348/§73.12).** Let `S := (V, E, in, out, ℓ_E, dep)` be an MLL2I proof-structure with a cut `e_cut ∈ E` such that `in(e_cut) = (v₁, v₂)` with both `v₁` and `v₂` being conclusions of hyperedges `e₁`, `e₂` such that `ℓ_E(e₁) = (u₁, u₂)` and `ℓ_E(e₂) = (w₁, w₂)`. Assume `u₁` is conclusion of some hyperedge `e_⋊` and `box(w₁) = (V_b, E_b)`. Three cases by `ℓ_E(e_⋊)`:

- **Weakening** (`ℓ_E(e_⋊) = w`, `in(e_⋊) = ∅`): Erase `w₁`, all its parents and dependent vertices.

      S' := (V', E', in', out, ℓ_E, dep')
      V' := V − {v₁, v₂, u₁, w₁} − V_b
      E' := (E − {e_cut, e₁, e₂, e_⋊} − E_b) ∪ {e'_cut}
      in'(e'_cut) = (v₂, w₂), in'(x) = in(x) otherwise
      dep' is dep restricted to dom(dep) − dep(w₁)

- **Dereliction** (`ℓ_E(e_⋊) = d`, `in(e_⋊) = v_d`): Remove the dependencies of `w₁`.

      S' := (V', E', in', out, ℓ_E, dep')
      V' := V − {v₁, v₂}, E' := (E − {e_cut, e₁, e₂, e_⋊}) ∪ {e¹_cut, e²_cut}
      in'(e¹_cut) = (v_d, w₁), in'(e²_cut) = (v₂, w₂)
      in'(x) = in(x) otherwise
      dep' is dep restricted to dom(dep) − dep(w₁)

- **Contraction** (`ℓ_E(e_⋊) = c`, `in(e_⋊) = (v₁¹, v₁²)`): Duplicate the dependencies.

      S' := (V', E', in', out', ℓ'_E, dep')
      V' := (V − {v₁, v₂}) ∪ σ(V_b ∪ {w₁})   (σ renames vertices with fresh names)
      E' := (E − {e_cut, e₁, e₂, e_⋊} − σ(E_b)) ∪ {e^{1,1}_cut, e^{1,2}_cut, e²_cut}
        with σ renaming edges with fresh names
      in'(e^{1,1}_cut) = (v₁¹, w₁), in'(e^{1,2}_cut) = (v₁², σ(w₁)), in'(e²_cut) = (v₂, w₂)
      in'(x) = in(x) otherwise
      dep'(σ(w₁)) = σ(dep(w₁)), dep'(x) = dep(x) otherwise

---

## §74 Simulation of Cut-Elimination (p. 348–351/§74)

**§74.1.** Mechanisms of duplication and erasure are already present in stellar resolution.

**Definition (Exponential basis of representation) (p. 348/§74.2).** The multiplicative basis of representation `𝔹 = (V, F, ar, [·])` is extended with:
- A binary function symbol `• ∈ F` with `ar(•) = 2`, considered left-associative: `t • u • v := (t • u) • v` and `t • u • v := t • (u • v)`;
- Variables `Y_i ∈ V` for `i ∈ ℕ` representing boxes;
- Three constants `w, c, d ∈ F` with `ar(w) = ar(c) = ar(d) = 0`.

The symbol `·` has priority over `•`: `t · u • v := (t · u) • v`.

**§74.3 (Remark).** The inductive definition of MLL2I proof-structures extends that of MLL proof-structures (Remark 66.5) with two new connectives `⋊` and `⊛`. We write `ETens^{u,v}(S)` (resp. `EPar^{u,v}(S)`) for a proof-structure `S` linked by ⊛ (resp. ⋊) hyperedge with premises `u` and `v`. Inductive constructions for structural rules: `W(S)` (nullary), `D^u(S)` (unary), `C^{u,v}(S)` (binary).

**§74.4.** A multiplicative address `u(t)` of a well-formed vehicle can be turned into a non-linear address `u(t • Y)` for a fresh variable `Y`. The right part of `•` contains exponential information. It can interact by cut with several copies of the same atom: `v(t • (1 · Y))` and `v'(t • (r · Y'))`.

**Definition (Path address of an atom) (p. 349/§74.5).** The *path address* `pAddr_S(v)` of an atom `v` in a proof-structure `S` is defined inductively:
- If `S ∈ {Ax_{v,*}, Ax_{*,v}, W(S')}` then `pAddr_S(v) = X`;
- If `S = D^v(S')` then `pAddr_S(v) = pAddr_{S'}(v) • d`;
- If `S = C^{w₁',w₂'}(S')` and `pAddr_{S'}(w_i) = t • u` for `i ∈ {1,2}` then `pAddr_S(w₁) = t • (1 · u)` and `pAddr_S(w₂) = t • (r · u)` such that `w_i'` is a conclusion with `w_i` above `w_i'`;
- If `S = S₁ ⊎ S₂` and `v ∈ V^{S_i}` then `pAddr_S(v) = pAddr_{S_i}(v)`;
- If `S ∈ {Par^{v',*}(S'), Tens^{v,*}(S'), EPar^{v',*}(S')}` then `pAddr_S(v) = 1 · pAddr_{S'}(v)` such that `v'` is a conclusion with `v` above `v'`;
- If `S ∈ {Par^{*,v'}(S'), Tens^{*,v'}(S'), EPar^{*,v'}(S')}` then `pAddr_S(v) = r · pAddr_{S'}(v)` such that `v'` is a conclusion with `v` above `v'`;
- If `S = ETens^{w₁',w₂'}(S')`, then for a fresh variable `Y_i ∈ V` representing a box:
  - `pAddr_S(w₁) = (1 · pAddr_{S'}(w₁)) • Y_i`;
  - `pAddr_S(w₂) = (r · pAddr_{S'}(w₂)) • Y_i`;
  - All `u ∈ box(w_i)` have path addresses updated from `pAddr_{S'}(u) = t • u` to `(t • u) • Y_i`.
- `pAddr_S(v) = pAddr_{S'}(v)` otherwise.

Path address to `v` is uniquely defined w.r.t. a conclusion `c ∈ Concl(S')` where `S'` is `S` without cuts.

- **Independent** (no `u` such that `v ∈ box(u)`): `addr_S(v) := c(pAddr_S(v))`.
- **Dependent** (some `u` such that `v ∈ box(u)`): `addr_S(v) := pAddr_S(u){X := pAddr_S(v)}`.

**§74.6 (Box/dependencies in stellar resolution).** The translation of proof-structures is designed so that a cut between a `⋊` and an `⊛` hyperedge applies a cut between the left premise of `⋊` and the left premise of `⊛` together with all its dependencies, via term unification. All connections described by the left premise of `⋊` (erasure, duplication, dereliction, or more) are locally applied to all elements of an exponential box.

**§74.7 (Erasure in stellar resolution).** Two translations for weakening nodes:
1. **Girard's solution**: Do not translate weakened atoms. A cut connected to where the weakening link should be creates a "hole" (free polarised ray) that cannot be filled, triggering erasure of the diagram via operator `ƶ` (§52.6).
2. **Author's solution** (used in the thesis): Translate a weakened atom `u` as a "black-hole" star:

       v* := [+addr_S(v), +ω(X), −ω(f(X))]

   where `t` is the path address of `u`, `ω` is a fresh symbol not appearing in the translation of the whole proof-structure. This triggers an infinite loop for any diagram connected to it, making it impossible to construct a saturated diagram.

**Definition (Weakened atoms) (p. 350/§74.8).** `Weak(S) := {u★ | ∃e ∈ E. ℓ(e) = w, out(e) = u}`.

**Definition (Translation of computational content) (p. 350/§74.9).** The *vehicle* and *cuts* of an MLL2I proof-structure `S` are:

    Φ^ax_S := Σ_{e ∈ Ax(S)} [μ(addr_S(←e)), μ(addr_S(→e))] + Σ_{u ∈ Weak(S)} v★

    Φ^cut_S := Σ_{e ∈ Cuts(S)} [−←e(X), −→e(X)]

where `μ(c(t)) = +c(t)` when `c = ←e` or `c = →e` for some `e ∈ Cuts(S)` (related to a cut) and `μ(x) = x` otherwise. The *computational content* of `S` is the constellation:

    Φ^comp_S := Φ^ax_S ⊎ Φ^cut_S

**§74.10.** Examples of MLL2I proof-structures and translations are given in Fig. 74.1:
- Fig. 74.1(a): Identity function of λ-calculus (`ax`→`d`→`⋊`): vehicle `[+4(1·X•d), +4(r·X)]`.
- Fig. 74.1(b): Left-projection function `λxy.x` of λ-calculus: more complex constellation with black-hole star for the weakened atom.

**Theorem (Simulation of MLL2I cut-elimination) (p. 352/§74.11).** For an MLL2I proof-net `R` such that `R ↝* S` with `S` in normal form:

    AEx(Φ^comp_R) ≃_S Φ^ax_S

*Proof sketch.* All multiplicative cases were treated in Chapter 10 (Lemma 67.9). The only new cut case for MLL2I corresponds to a cut between `⋊` and `⊛`. It makes the left premises interact as in an `⊗/⅋` cut-elimination. The right premises are multiplicative. Three subcases for the interaction between left premises (box/dependency connections with structural rules):

1. **Left premise of `⋊` = conclusion of weakening `w`**: translated as black-hole, preventing any rays `+v(1·t_i•Y_i)` from the left premise of `⊛` from constructing a saturated diagram. All these stars are erased. Those rays are exactly the translation of vertices of the box associated with the left premise of `⊛`.

2. **Left premise of `⋊` = derelicted atoms** `+u(t_i•d)` interacting with left premises `−v(w_j•Y_j)` of `⊛` such that `t_i ⊲ w_j`: variables `Y_j` are replaced by `d`, linearising all rays `−v(w_j•Y_j)`. Potential for duplication given by variable `Y_j` is cancelled with constant `1`. This corresponds to box opening.

3. **Left premise of `⋊` = n copies** `+u₁(t•u₁), ..., +uₙ(t•uₙ)`: all match with left premises `+v₁(w•Y₁), ..., +vₘ(w•Yₘ)` of `⊛` such that `t ⊲ w`. Triggers duplications of all `v_i` considered as part of the same box. Each `+v_i(w•Y_i)` is duplicated into `+v₁(w•u₁), ..., +vₙ(w•uₙ)` where `u_i` are copy identifiers induced by trees of contraction.

**The simulation uses AEx (abstract execution), not IEx (interactive execution).**

---

## §75 Girard's Original Correctness Criterion (p. 352–356/§75)

**§75.1.** In the last paper of geometry of interaction [Gir13a], Girard suggested a correctness criterion for MLL2I in stellar resolution. In the first paper of transcendental syntax [Gir17, §5], he updated it to a simpler criterion using switchings (as in Danos-Regnier correctness).

**§75.2.** This correctness criterion cannot be expressed directly with proof-structures (at least without changing the definition of proof-structures) since it deeply relies on mechanisms of stellar resolution. Eng chooses not to give a notion of MLL2I proof-net and considers MLL2I proof-structures independently from usual linear logic theory. Girard's correctness is described informally; no adequacy result is stated. Girard sketched a proof in [Gir17, §5.7].

**Definition (MLL2I switching) (p. 353/§75.3).** Let `S` be an MLL2I proof-structure. An *MLL2I switching* is defined as an MLL switching `φ` extended with:
- `φ(e) ∈ {⊛_X, ⊛_1}` when `ℓ(e) = ⊛`;
- `φ(e) ∈ {⋊_L, ⋊_R}` when `ℓ(e) = ⋊`.

**Definition (MLL2I test) (p. 353/§75.4).** Let `S` be an MLL2I proof-structure and `φ` one of its switchings. The *test* associated with `S^φ` is the constellation:

    Φ^φ_S := Φ^cut_S ⊎ Σ_{v ∈ V^{S^φ}} v★

The translation `v★` of a vertex `v` (conclusion of a hyperedge `e`) is defined:

- If `v` is the conclusion of a `d` hyperedge whose input is itself below some `e` with `ℓ(e) = ax`:

      v★ = [−addr_S(v); +v(X•Y)]

- If `ℓ_E(e) = ⊛_X` and `in(e) = (u, w)`:

      v★ = [−u(X•X), −w(X); +v(X)]

- If `ℓ_E(e) = ⊛_1` and `in(e) = (u, w)`:

      v★ = [−u(X•1), −w(X); +v(X)]

- If `ℓ_E(e) = ⋊_L` and `in(e) = (u, w)`:

      v★ = [−u(X•Y); +v(X•Y)] + [−w(X), −∞(X); +∞(X)]

- If `ℓ_E(e) = ⋊_R` and `in(e) = (u, w)`:

      v★ = [−u(X•Y)] + [−u(X'•Y')] + [−w(X); +v(X)]

  where the star `[−u(X'•Y')]` is not used when `X'` can be instantiated *exactly* to `X`, meaning it is replaced by exactly the variable `X` (names of variables are taken into account, unlike usual unification).

Other cases are the same as for the multiplicative case (Definition 68.3).

**§75.5.** Similarly to the multiplicative case, the interaction `Ex(Φ^ax_S ⊎ Ex(Φ^φ_S))` between a vehicle and an MLL2I test produces the star of roots `[v₁(X), ..., vₙ(X)]` where `{v₁, ..., vₙ} ⊆ Concl(S)`. The requirement is that `v₁, ..., vₙ` correspond to all *linear conclusions* not having addresses of the shape `X • u_i` for some `u_i`. No conditions are required for non-linear (underlined) conclusions.

**§75.6 (Left-exponential tensor case — ⊛_X and ⊛_1).** The two tests for `⊛` check that the terms used have the right shape: the left input must be a non-linear atom of address `t•Y` where `Y` does not appear in `t`. A non-linear atom `r := +u(t•v)` passes both tests `⊛_X` and `⊛_1` when `t` matches with `X` and `v` with `X` and `1`. First, `t` must be a variable because otherwise, in the two tests, it would be connected to `X` of `−u(X•X)` and `−u(X•1)` which propagates a term to the conclusion making it impossible to obtain all roots of the form `u'(X)`. Hence `r = +u(X'•v)`. The only way to have `v ⊲ 1` is that either `v = 1` or `v` is a variable.

- If `v = 1` then when `r = +u(X'•1)` is connected to `−u(X•X)` of the test `⊛_X`, the constant `1` is propagated to the conclusion, preventing us from obtaining the exact star of roots as normal form. Hence `v ≠ 1`.
- If `v = Y`, then `r = +u(X'•Y)`. In the test `⊛_1`, it matches with `−u(X•1)`. Hence `Y = 1`. If `X' = Y` then the constant `1` is propagated to a conclusion. Finally, `Y` must be a variable different from `X'`.

**§75.7 (Left-exponential par case — ⋊_R right switching).** The test `⋊_R` is similar to `⅋_R`. The difference: we want to cancel `n ∈ ℕ` copies of non-linear atoms of the form `+u(t_i•u_i)`. We want to ensure all `t_i` are variables (the `u_i` can be exponential copy identifiers). Girard's trick: take the actual names of variables into account and consider *coherent constellations* [Gir16b] which excludes some substitutions between stars. In Eng's definition of test, this is expressed in the side condition of `⋊_R`. Girard's trick enforces `t_i` to be exactly `X`.

- If all `t_i = X`: the test `⋊_R` behaves as `⅋_R` because `X'` can be instantiated to `X` and hence `[−u(X'•Y')]` cannot be used.
- If one `t_i ≠ X`: `X'` cannot be instantiated to `X` and the two stars `[−u(X•Y)]` and `[−u(X'•Y')]` are used. This duplicates the star `+u(t_i•u_i)` twice, altering the normal form.

**§75.8 (Left-exponential par case — ⋊_L left switching).** The test `⋊_L` is more subtle. Girard requires `⋊_L` to be *cancelling*: any interaction with it normalises to the empty constellation `∅`. This is the main point which cannot easily be represented with usual proof-structures and exploits stellar resolution mechanisms. The current flows through the left premise (which is non-linear and can be erased or duplicated). Eng modifies Girard's definition by adding a black hole for consistency with the execution model. Girard's original definition is in [Gir17, §5.5]. The black-hole star `[−w(X), −∞(X); +∞(X)]` ensures that any stars reaching it will never be able to form a saturated diagram.

Two cases (Fig. 75.1):
- **Case 1**: The star for `⋊_L` is connected to copies of atoms `u₁, ..., uₙ`. If one of these atoms has a path leading to `v` by a cut, we get a cycle and infinitely many correct diagrams — execution is not strongly normalising. Hence the proof-structure is not correct.
- **Case 2**: No cycle of Case 1, and some atoms among `u₁, ..., uₙ` possibly have a path reaching an atom of `w`. Because of the star `[−w(X), +∞(X), −∞(X)]` of `⋊_L`, all stars connected to an atom of `w` (the whole constellation) will be erased — unable to produce a saturated diagram. Normal form is `∅`.

By using the black-hole trick, connectedness is maintained (the main problem with exponentials). If there is no `u_i` in Case 2, the black hole erases everything; in Case 1, we lose connectedness since `w` is isolated.

**Example (Correct proof-structures) (p. 356/§75.9).** The proof-structure representing the identity function in §74 has two switchings `⋊_L` and `⋊_R` for its only `⋊` link.

- Right switching (`⋊_R`) test:

      [−4(1·X•d); +3(X•Y)] + [−4(r·X); +2(X)] +
      [−3(X•Y)] + [−3(X'•Y')] + [−2(X); +4(X)] +
      [−4(X); 4(X)]

  Executes to `[−4(1·X•d)] + [−4(r·X); 4(X)]`. Connected to vehicle `[+4(1·X•d), +4(r·X)]`, produces `[4(X)]` — correct.

- Left switching (`⋊_L`) test:

      [−4(1·X•d); +3(X•Y)] + [−4(r·X); +2(X)] +
      [−3(X•Y); +4(X•Y)] + [−2(X), −∞(X); +∞(X)] +
      [−4(X); 4(X)]

  Reduces to `[−4(1·X•d); 4(X)] + [−4(r·X), −∞(X); +∞(X)]`. Connected to vehicle `[+4(1·X•d), +4(r·X)]`, produces a connected constellation which normalises to `∅` because of the black hole using symbol `∞`. This cancels the test, as expected.

### Comparison: Girard's Original vs. Danos-Regnier

Girard's original correctness criterion (from [Gir13a]) was formulated directly in terms of stellar resolution mechanisms and could not be expressed with proof-structures alone without changing their definition. In [Gir17, §5], Girard updated the criterion to use *switchings* — a formulation more similar to Danos-Regnier. The key differences:

1. **Scope**: Danos-Regnier applies to MLL (and MLL+MIX) proof-structures via acyclicity+connectedness of switched graphs; Girard's criterion applies to MLL2I and requires the additional cancellation property for `⋊_L` (which has no analogue in Danos-Regnier since there are no exponentials in MLL).

2. **Mechanism**: Danos-Regnier correctness is a purely graph-theoretic criterion (tree condition on switching graphs). Girard's MLL2I criterion is inherently computational: it relies on the normalisation behaviour of stellar resolution (the test for `⋊_L` must normalise to `∅`, the test for `⋊_R` must produce the correct star of roots).

3. **Adequacy**: Girard's criterion for MLL2I has no stated adequacy theorem in this chapter. Danos-Regnier for MLL was proven sound and complete in Chapter 10.

4. **Non-linear conclusions**: In the MLL2I correctness test, non-linear (underlined) conclusions are exempt from the requirement that `v₁, ..., vₙ` cover all conclusions — because underlined conclusions can be erased or duplicated an arbitrary number of times.

---

## §76 Discussion: What is a Non-Linear Proof? (p. 357/§76)

**§76.1.** Non-linear proofs are proofs able to erase or duplicate some logical entities — in sequent calculus, occurrences of labels representing formulas; in proof-net theory, duplication and erasure of some sub-proof-structures.

**§76.2.** In stellar resolution, duplication and erasure are expressed by very general, alogical notions. Duplication is expressed by the fact that a ray can be required by several other matchable rays. For instance, a ray `−1(X)` can be compatible with two rays `+1(1)` and `+1(r)`. The execution will duplicate `+1(X)` to satisfy both constraints. What is exponential linear logic with regard to those "natural/primitive" non-linear mechanisms?

**§76.3.** Exponentials (at least intuitionistic implication) can be seen as a way to *format* those non-linear mechanisms. It is *one way* to behave non-linearly. One can obtain several non-linear logics by changing the exponential rules of linear logic (soft linear logic, elementary linear logic, etc.) or go outside of any primitive logical system. The only limit is the primitive computational mechanisms considered.

**§76.4.** "Formatting" means choosing a specific shape for objects. The rays considered in Chapter 11 have the shape `c(t·u)`. This allows for nested boxes. Alternative non-linear formatting (which could not, at least not naturally, exist starting from linear logic as a primitive notion) is conceivable.

---

## Key Technical Summary

| Concept | Definition |
|---|---|
| MLL2I pre-formulas | `C, D ::= X_i | X_i^⊥ | C⊗D | C⅋D | C⊛D | C⋊D` |
| MLL2I formulas | `A, B ::= C | C̲` (underlined = `?C`) |
| `A⋊B` | `?A ⅋ B` (left-exponential par) |
| `A⊛B` | `!A ⊗ B` (left-exponential tensor) |
| dep function | `dep : V → 𝒫(V)`, dependencies of ⊛ left premises |
| Exponential box | Sub-proof-structure over `dep(v)` for left premise `v` of ⊛ |
| Path address | `pAddr_S(v)`, term built inductively tracking l/r paths and box variables `Y_i` |
| Computational content | `Φ^comp_S = Φ^ax_S ⊎ Φ^cut_S` |
| Cut-elimination simulation | AEx (abstract execution): `AEx(Φ^comp_R) ≃_S Φ^ax_S` |
| MLL2I switching | MLL switching + `φ(⊛) ∈ {⊛_X, ⊛_1}`, `φ(⋊) ∈ {⋊_L, ⋊_R}` |
| Girard correctness test | `Φ^φ_S = Φ^cut_S ⊎ Σ_{v ∈ V^{S^φ}} v★`; must produce correct star of roots |
| `⋊_L` cancellation | Test for left switching must normalise to `∅` |
| Non-linearity | Stellar primitive: ray matchable by multiple rays; exponentials format this |
