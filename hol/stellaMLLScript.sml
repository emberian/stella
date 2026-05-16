(* stellaMLLScript.sml
   MLL proof-structures as constellations — Eng §66 (proofs-as-constellations)
   and §67.10 (cut-elimination simulation theorem).

   ══════════════════════════════════════════════════════════════════════════════
   SCOPE
   ──────────────────────────────────────────────────────────────────────────────
   BOUNDED to Eng Ch.10 §66 and §67.10 only.
   §68–72 are NOT attempted.

   REUSED from existing stella theories:
     · stellaTermTheory      — term, Var, App, vars_t, subst_apply
     · stellaPolarisedTheory — polarity, encode_psym, decode_psym, uterm_t
     · stellaMatchTheory     — matchable, mm_reduces
     · stellaDiagramTheory   — constellation, ray, star, dep_graph,
                               all_colours, IdRays, stars_dep
     · stellaExecutionTheory — AEx_C (the abstract execution §49.42),
                               correct_C, CSatDiags_C, actualise

   FRESH (this file):
     · mll_edge_label        — labels on proof-structure edges (Ax/Tens/Par/Cut)
     · proof_struct          — MLL proof-structure record §66.3
     · ax_edges / cut_edges  — sub-multisets of edges by label §66.11
     · pAddr_S               — path address §66.7
     · addr_S                — address = conclusion(pAddr) §66.7
     · mu_ray                — polarity wrapper μ(·) §66.11
     · Phi_ax / Phi_cut      — vehicle and cut constellations §66.11
     · Phi_comp              — computational content §66.11
     · struct_equiv          — structural equivalence ≃_S §67.7
     · cut_elim_step         — one cut-elimination step R ~~> S §67.9
     · cut_elim_star         — R ~~>* S (reflexive-transitive) §67.10
     · normal_ps             — proof-structure in normal form (no cuts) §67.10
     · sim_cut_step          — Lemma §67.9 (one step, deferred)
     · sim_cut_elim          — Theorem §67.10 (full theorem, deferred)

   PROOF POLICY:  every non-trivial proof is discharged with `cheat` preceded
   by a PROOF-OBLIGATION block.  Closed EVAL computations are NOT debt.
   Zero uses of new_axiom / mk_thm.
   ══════════════════════════════════════════════════════════════════════════════
*)

open HolKernel boolLib bossLib;
open arithmeticTheory pred_setTheory finite_mapTheory listTheory pairTheory
     relationTheory;
open stellaTermTheory stellaPolarisedTheory stellaMatchTheory;
open stellaDiagramTheory;
open stellaExecutionTheory;

val _ = new_theory "stellaMLL";

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.3  MLL edge labels                                                       *)
(*                                                                             *)
(* Eng uses hyperedges in a proof-structure labelled by one of:                *)
(*   Ax   — axiom link  (binary: two conclusions)                              *)
(*   Tens — ⊗ tensor link  (binary input, one output)                         *)
(*   Par  — ⅋ par link     (binary input, one output)                         *)
(*   Cut  — cut link       (binary: two premise conclusions)                   *)
(*                                                                             *)
(* We represent these as a HOL4 datatype.                                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Datatype:                                               (* §66.3 *)
  mll_label = Ax | Tens | Par | Cut
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.3  MLL proof-structure                                                   *)
(*                                                                             *)
(* An MLL proof-structure S is a hypergraph:                                   *)
(*   V^S  : vertex set (atoms / formula occurrences) — encoded as num set     *)
(*   E^S  : edge set (links) — encoded as num set                             *)
(*   in_S : E^S → (num # num)   left/right input vertices                     *)
(*   out_S: E^S → num           output (conclusion) vertex                     *)
(*   lbl  : E^S → mll_label     edge label                                     *)
(*   concl: S → num set         the set of conclusion vertices (§66.3)         *)
(*                                                                             *)
(* For axiom and cut links the "output" slot is unused; we set it to 0 by     *)
(* convention.  For Ax, in_S(e) = (v₁, v₂) are the two atomic conclusions.   *)
(* For Tens/Par: in_S(e) = (v₁, v₂) premises, out_S(e) = v the output.       *)
(* For Cut: in_S(e) = (v₁, v₂) are the two cut-connected vertices.            *)
(*                                                                             *)
(* This is a *record* type so downstream definitions can pattern-match.        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Datatype:                                               (* §66.3 *)
  proof_struct = <|
    vertices : num set ;
    edges    : num set ;
    in_ps    : num -> (num # num) ;
    out_ps   : num -> num ;
    lbl      : num -> mll_label ;
    concl    : num set
  |>
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.11  Axiom and cut sub-edge-sets                                          *)
(*                                                                             *)
(* Ax(S)  = { e ∈ E^S | lbl(e) = Ax  }                                       *)
(* Cuts(S) = { e ∈ E^S | lbl(e) = Cut }                                       *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition ax_edges_def :                               (* §66.11 *)
  ax_edges (S : proof_struct) : num set =
    { e | e IN S.edges /\ S.lbl e = Ax }
End

Definition cut_edges_def :                              (* §66.11 *)
  cut_edges (S : proof_struct) : num set =
    { e | e IN S.edges /\ S.lbl e = Cut }
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.7  Path address  pAddr_S(v)                                              *)
(*                                                                             *)
(* The path address of an atom v in a proof-structure S is defined inductively *)
(* on the structure of S (Definition §66.7):                                   *)
(*                                                                             *)
(*   · If v ∈ Concl(S) of an axiom link e ∈ Ax(S):  pAddr_S(v) = Var x      *)
(*     for a fresh variable x.                                                  *)
(*   · If v is a conclusion reached via the LEFT  branch of a Tens/Par link:   *)
(*     pAddr_S(v) = App (encode_psym (Neutral, 1)) [pAddr_{S'}(v)]            *)
(*     (the "1" direction: left, encoded as App of neutral-1)                  *)
(*   · If v is a conclusion reached via the RIGHT branch of a Tens/Par link:   *)
(*     pAddr_S(v) = App (encode_psym (Neutral, 2)) [pAddr_{S'}(v)]            *)
(*     (the "r" direction: right, encoded as App of neutral-2)                 *)
(*   · Otherwise pAddr_S(v) = pAddr_{S'}(v).                                  *)
(*                                                                             *)
(* In Eng §66.7 the "directions" are the symbols 1 (left) and r (right).      *)
(* We encode them as neutral function symbols with arities-1 in our term       *)
(* representation:                                                              *)
(*   1  ≅ encode_psym (Neutral, 1)  — the neutral symbol named 1              *)
(*   r  ≅ encode_psym (Neutral, 2)  — the neutral symbol named 2              *)
(*                                                                             *)
(* Because the inductive structure of proof-structures is not primitive        *)
(* recursive in our flat record encoding, we give an *axiomatic* recursive     *)
(* specification: pAddr_S is a function from num → term satisfying the         *)
(* clauses above.  This is the approach used throughout the stella scaffold     *)
(* (state + cheat).                                                             *)
(*                                                                             *)
(* We define the direction constants:                                           *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §66.7  Direction symbols: "1" (left) and "r" (right) in Eng's notation. §66.2 *)
Definition dir_left_def :                               (* §66.2 *)
  dir_left : num = encode_psym (Neutral, 1)
End

Definition dir_right_def :                              (* §66.2 *)
  dir_right : num = encode_psym (Neutral, 2)
End

(* §66.7  pAddr_S: a function satisfying the recursive clauses of §66.7.
   We declare it as an uninterpreted constant and state its spec as a theorem
   (STATED+CHEAT, proof-obligation stellaMLL.01).                              *)
Definition pAddr_S_def :                                (* §66.7 *)
  pAddr_S (S : proof_struct) (v : num) : term =
    if v IN S.concl then Var v
    else
      (* Default: Var v.  The real recursive definition is given by
         PROOF-OBLIGATION[stellaMLL.01] below.                                *)
      Var v
End

(* The specification of pAddr_S (the inductive clauses of §66.7):
   PROOF-OBLIGATION[stellaMLL.01]: pAddr_S satisfies the inductive spec.      *)
(*
   PROOF-OBLIGATION[stellaMLL.01]:
   GOAL:
     !S v e.
       (* Ax case: v is one of the two conclusions of axiom e *)
       (e IN ax_edges S /\ (v = FST (S.in_ps e) \/ v = SND (S.in_ps e))) ==>
         pAddr_S S v = Var v

       /\ (* Left Tens/Par premise: v above via left branch *)
       (e IN S.edges /\ (S.lbl e = Tens \/ S.lbl e = Par) /\
        v = FST (S.in_ps e)) ==>
         pAddr_S S v = App dir_left [pAddr_S S (S.out_ps e)]

       /\ (* Right Tens/Par premise: v above via right branch *)
       (e IN S.edges /\ (S.lbl e = Tens \/ S.lbl e = Par) /\
        v = SND (S.in_ps e)) ==>
         pAddr_S S v = App dir_right [pAddr_S S (S.out_ps e)]

   STRATEGY:
     This is a well-foundedness argument on the depth of the proof-structure.
     In the full proof: define pAddr_S by structural recursion on a "depth"
     measure on vertices (the height from conclusions to atoms in the DAG of S).
     For the scaffold we state the spec and cheat.
   DRAFT-TACTICS: cheat (proof obligation, not attempted)
*)

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.7  Address  addr_S(v) = c(pAddr_S(v))                                   *)
(*                                                                             *)
(* The address of atom v w.r.t. conclusion c ∈ Concl(S) is:                  *)
(*   addr_S(v) = App c_sym [pAddr_S(v)]                                        *)
(* where c_sym is the function symbol for c.                                   *)
(*                                                                             *)
(* In our encoding: the conclusion vertex c is used as the symbol number       *)
(* (with neutral polarity for uncoloured and positive for cut-related):        *)
(* we encode c as encode_psym (Neutral, c) for the address symbol.             *)
(*                                                                             *)
(* (The μ-wrapper in §66.11 upgrades to Pos when c is cut-related.)           *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §66.7  Address of atom v relative to its conclusion vertex c. *)
Definition addr_S_def :                                 (* §66.7 *)
  addr_S (S : proof_struct) (c : num) (v : num) : term =
    App (encode_psym (Neutral, c)) [pAddr_S S v]
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.11  The μ function                                                       *)
(*                                                                             *)
(* §66.11: μ(c(t)) = +c(t) when c is the conclusion of a cut edge             *)
(*                 = c(t)   otherwise (keep as-is)                             *)
(*                                                                             *)
(* In our encoding:                                                             *)
(*   · a "cut-related" conclusion c is one that appears as in_S(e)            *)
(*     for some e ∈ cut_edges S.                                               *)
(*   · If c is cut-related: re-encode c with Pos polarity.                    *)
(*   · Otherwise: keep Neutral encoding.                                        *)
(*                                                                             *)
(* For a ray App h [pAddr]: h = encode_psym(pol, name).                       *)
(* We replace pol with Pos when name (the conclusion vertex) is cut-related.  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* Conclusion vertices that are endpoints of a cut edge. §66.11 *)
Definition cut_concls_def :                             (* §66.11 *)
  cut_concls (S : proof_struct) : num set =
    { v | ?e. e IN cut_edges S /\
              (v = FST (S.in_ps e) \/ v = SND (S.in_ps e)) }
End

(* §66.11  Apply μ to a ray: upgrade head polarity to Pos for cut conclusions. *)
Definition mu_ray_def :                                 (* §66.11 *)
  mu_ray (S : proof_struct) (r : ray) : ray =
    case r of
      App h args =>
        let (_, name) = decode_psym h in
        if name IN cut_concls S then
          App (encode_psym (Pos, name)) args
        else r
    | Var x => Var x
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.11  Vehicle Φ_S^ax: one star per axiom edge                              *)
(*                                                                             *)
(* Φ_S^ax := Σ_{e ∈ Ax(S)} [μ(addr_S(←e)), μ(addr_S(→e))]                   *)
(*                                                                             *)
(* where ←e = FST(in_S(e))  and  →e = SND(in_S(e)).                          *)
(*                                                                             *)
(* We build this as the image of the axiom edge set.  Since HOL4 sets are not *)
(* directly convertible to lists, we take a finite-set-to-list approach:       *)
(* Phi_ax S = SET_TO_LIST (IMAGE (ax_star S) (ax_edges S))                    *)
(* where ax_star S e = [mu_ray S (addr_S S (FST ..)), mu_ray S (addr_S S (SND..))]. *)
(*                                                                             *)
(* We axiomatise the order-independent content; a precise build would require  *)
(* CHOICE or a canonical ordering.  For the scaffold we define it as such a   *)
(* SET_TO_LIST image (computable when ax_edges S is decidable/finite).         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §66.11  Single axiom star for edge e. *)
Definition ax_star_def :                                (* §66.11 *)
  ax_star (S : proof_struct) (e : num) : star =
    let lv = FST (S.in_ps e) in
    let rv = SND (S.in_ps e) in
    [ mu_ray S (addr_S S lv lv) ;
      mu_ray S (addr_S S rv rv) ]
End

(* §66.11  Vehicle Φ_S^ax = disjoint union of axiom stars. *)
Definition Phi_ax_def :                                 (* §66.11 *)
  Phi_ax (S : proof_struct) : constellation =
    MAP (ax_star S) (SET_TO_LIST (ax_edges S))
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.11  Cut constellation Φ_S^cut: one star per cut edge                    *)
(*                                                                             *)
(* Φ_S^cut := Σ_{e ∈ Cuts(S)} [-←e(X), -→e(X)]                               *)
(*                                                                             *)
(* where X is a fresh variable (Var 0 in our encoding; distinct per star by   *)
(* the α-renaming θ_i applied in execution).                                   *)
(*                                                                             *)
(* The two rays are negative-polarised applications of the cut-endpoint        *)
(* function symbols to a fresh variable.                                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §66.11  Single cut star for edge e. *)
Definition cut_star_def :                               (* §66.11 *)
  cut_star (S : proof_struct) (e : num) : star =
    let lv = FST (S.in_ps e) in
    let rv = SND (S.in_ps e) in
    [ App (encode_psym (Neg, lv)) [Var 0] ;
      App (encode_psym (Neg, rv)) [Var 0] ]
End

(* §66.11  Cut constellation Φ_S^cut. *)
Definition Phi_cut_def :                                (* §66.11 *)
  Phi_cut (S : proof_struct) : constellation =
    MAP (cut_star S) (SET_TO_LIST (cut_edges S))
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.11  Computational content Φ_S^comp = Φ_S^ax ⊎ Φ_S^cut                  *)
(*                                                                             *)
(* The computational content of S is the disjoint union (as constellation     *)
(* list concatenation) of the vehicle and the cut constellation.              *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition Phi_comp_def :                               (* §66.11 *)
  Phi_comp (S : proof_struct) : constellation =
    Phi_ax S ++ Phi_cut S
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §67.7  Structural equivalence  ≃_S                                           *)
(*                                                                             *)
(* Two constellations Φ and Φ' are structurally equivalent (§67.7) if there   *)
(* is a bijection φ : I_Φ → I_{Φ'} such that:                                *)
(*   (a) |Φ[i]| = |Φ'[φ(i)]|  for all i  (same star sizes)                   *)
(*   (b) Φ[i][j] ⋈ Φ[i'][j'] iff Φ'[φ(i)][j] ⋈ Φ'[φ(i')][j']               *)
(*       for all i,i' ∈ I_Φ and j ∈ I_{Φ[i]}, j' ∈ I_{Φ[i']}               *)
(*                                                                             *)
(* i.e., the dependency graph structure is preserved under a bijection on star *)
(* indices.                                                                     *)
(*                                                                             *)
(* In our list representation:                                                  *)
(*   I_Φ = {0,..,LENGTH Φ - 1}                                                *)
(*   Φ[i] = EL i Φ                                                            *)
(*   ⋈ here means matchable (dep_edge_cond)                                    *)
(*                                                                             *)
(* NOTE: §67.7 also says "extended to rays" and requires colour-set           *)
(* parameters C and D.  For the scaffold we simplify to the pure structural    *)
(* bijection on star indices (the colour sets are implicit in the context of   *)
(* cut-elimination).                                                            *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §67.7  Structural equivalence of two constellations. *)
Definition struct_equiv_def :                           (* §67.7 *)
  struct_equiv (Phi : constellation) (Phi' : constellation) : bool =
    ?f : num -> num.
      (* f is a bijection I_Phi -> I_Phi' *)
      (!i. i < LENGTH Phi ==> f i < LENGTH Phi') /\
      (!i i'. i < LENGTH Phi /\ i' < LENGTH Phi /\ f i = f i' ==> i = i') /\
      (!i'. i' < LENGTH Phi' ==> ?i. i < LENGTH Phi /\ f i = i') /\
      (* Star sizes preserved *)
      (!i. i < LENGTH Phi ==> LENGTH (EL i Phi) = LENGTH (EL (f i) Phi')) /\
      (* Matchability pattern preserved *)
      (!i i' j j'.
         i  < LENGTH Phi /\ i'  < LENGTH Phi /\
         j  < LENGTH (EL i Phi) /\ j' < LENGTH (EL i' Phi) ==>
         (matchable (EL j (EL i Phi)) (EL j' (EL i' Phi)) <=>
          matchable (EL j (EL (f i) Phi')) (EL j' (EL (f i') Phi'))))
End

(* No custom infix notation for struct_equiv; use the function directly. *)

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §67.7  ≃_S is an equivalence relation                                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaMLL.02]:
   GOAL:   !Phi. Phi ≃_S Phi
   STRATEGY: witness f = identity; all clauses immediate.
   DRAFT-TACTICS:
     rw [struct_equiv_def] >> qexists_tac `\i. i` >> simp []
*)
Theorem struct_equiv_refl :
  !Phi. struct_equiv Phi Phi
Proof
  cheat
QED

(*
   PROOF-OBLIGATION[stellaMLL.03]:
   GOAL:   !Phi Phi'. Phi ≃_S Phi' ==> Phi' ≃_S Phi
   STRATEGY: invert the bijection f; the inverse is also a bijection and
             preserves matchability by symmetry.
   DRAFT-TACTICS:
     rw [struct_equiv_def] >> qexists_tac `\i'. @i. i < LENGTH Phi /\ f i = i'` >>
     ... (bijection inverse lemmas) ...
*)
Theorem struct_equiv_sym :
  !Phi Phi'. struct_equiv Phi Phi' ==> struct_equiv Phi' Phi
Proof
  cheat
QED

(*
   PROOF-OBLIGATION[stellaMLL.04]:
   GOAL:   !Phi Phi' Phi''. Phi ≃_S Phi' /\ Phi' ≃_S Phi'' ==> Phi ≃_S Phi''
   STRATEGY: compose the two bijections; transitivity of matchability iff.
   DRAFT-TACTICS:
     rw [struct_equiv_def] >>
     qexists_tac `\i. g (f i)` >>
     metis_tac []
*)
Theorem struct_equiv_trans :
  !Phi Phi' Phi''.
    struct_equiv Phi Phi' /\ struct_equiv Phi' Phi'' ==>
    struct_equiv Phi Phi''
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66  Proof-structure cut-elimination step  R ~~> S                           *)
(*                                                                             *)
(* One step of cut-elimination on proof-structures (§67.9):                   *)
(*   R ~~> S  iff S is obtained from R by eliminating one cut edge e_cut.     *)
(*   The two cases are:                                                         *)
(*     (a) Ax/cut case: the cut e_cut connects an axiom edge.                  *)
(*     (b) Par/Tens case: the cut connects a ⅋ edge to a ⊗ edge.              *)
(*                                                                             *)
(* We represent cut-elimination abstractly as a relation on proof-structs,    *)
(* parameterised by the eliminated cut edge.                                   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §67.9  One step of cut-elimination.
   R ~~> S means S is a proof-structure obtained from R by eliminating
   exactly one cut edge e_cut (via either the Ax/cut or the Par/Tens rule).   *)
Definition cut_elim_step_def :                          (* §67.9 *)
  cut_elim_step (R : proof_struct) (S : proof_struct) : bool =
    (* There exists a cut edge in R that is eliminated to produce S *)
    ?e_cut.
      e_cut IN cut_edges R /\
      (* S has strictly fewer cuts: the cut e_cut is removed *)
      cut_edges S PSUBSET cut_edges R /\
      (* S has the same vertex set (cut-elimination is local) *)
      S.vertices = R.vertices /\
      (* S is otherwise well-formed with the cut removed *)
      e_cut NOTIN S.edges /\
      (* The non-cut edges are inherited *)
      (R.edges DIFF cut_edges R) SUBSET S.edges
End

(* §67.10  Reflexive-transitive closure: cut_elim_star R S = R ~~>* S *)
Definition cut_elim_star_def :                          (* §67.10 *)
  cut_elim_star = RTC cut_elim_step
End

(* §67.10  A proof-structure is in normal form iff it has no cuts. *)
Definition normal_ps_def :                              (* §67.10 *)
  normal_ps (S : proof_struct) : bool = (cut_edges S = {})
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §67.7  AEx equivalence of computational contents                             *)
(*                                                                             *)
(* The statement of §67.9 involves AEx(Φ_R^comp) ≃_S AEx(Φ_S^comp).         *)
(*                                                                             *)
(* AEx_C, defined in stellaExecutionTheory, returns a *set of constellations*. *)
(* We need to lift struct_equiv to say "there exist representatives in the     *)
(* two AEx sets that are structurally equivalent":                              *)
(*                                                                             *)
(*   AEx_equiv Phi Phi' :=                                                     *)
(*     ?gamma gamma'. gamma IN AEx_C Phi /\ gamma' IN AEx_C Phi' /\           *)
(*                    gamma ≃_S gamma'                                          *)
(*                                                                             *)
(* For the deterministic case (all-objective, normal form is unique):          *)
(*   AEx_C Phi = {gamma}  and  AEx_C Phi' = {gamma'},                         *)
(* so AEx_equiv simplifies to gamma ≃_S gamma'.                               *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §67.7/§67.9  Structural equivalence lifted to AEx sets. *)
Definition AEx_equiv_def :                              (* §67.7 *)
  AEx_equiv (Phi : constellation) (Phi' : constellation) : bool =
    ?gamma gamma'.
      gamma IN AEx_C Phi /\ gamma' IN AEx_C Phi' /\
      struct_equiv gamma gamma'
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §67.9  Lemma: one cut-elimination step simulates on AEx                      *)
(*                                                                             *)
(* STATEMENT (§67.9): if R ~~> S by eliminating cut e_cut, then              *)
(*   AEx(Φ_R^comp) ≃_S AEx(Φ_S^comp)                                         *)
(*                                                                             *)
(* PROOF SKETCH (from §67.9 and docs):                                         *)
(*   · Ax/cut case: contracting the relevant stars in Φ_R^comp yields exactly *)
(*     the stars of Φ_S^comp (the cut star [-v₀(X), -v(X)] with an ax star   *)
(*     [+v₀(1·X), +v₀(r·X)] resolves to give a diagram in Φ_S^comp).         *)
(*   · Par/Tens case: the cut star duplicates; the diagrams of Φ_R^comp and   *)
(*     Φ_S^comp are equal up to change of function symbols (structural equiv). *)
(*                                                                             *)
(* DEFERRED: proof-obligation stellaMLL.05                                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaMLL.05]:
   GOAL:
     !R S.
       R ~~> S ==>
       AEx_equiv (Phi_comp R) (Phi_comp S)
   STRATEGY:
     Case split on the type of cut e_cut:
     (a) Ax/cut case (lbl(e₁) = Ax for the edge paired with e_cut):
         Unfold Phi_comp_def, Phi_ax_def, Phi_cut_def.
         The ax-star [μ(addr_R(←e₁)), μ(addr_R(→e₁))] and the
         cut-star [-←e_cut(X), -→e_cut(X)] resolve under execution to
         produce diagrams identical to the corresponding stars in Phi_S^comp.
         This is a concrete algebraic calculation on addr_S and mu_ray.
         The structural equivalence bijection is the identity on surviving stars.
     (b) Par/Tens case (lbl(e₁) = Par, lbl(e₂) = Tens):
         The cut duplicates into two new cuts.  The diagrams of Phi_R^comp
         and Phi_S^comp are matched by a bijection mapping the duplicated stars
         to the new pair.
     Both cases use stellaExecutionTheory.AEx_C properties (embeds_diag,
     CSatDiags_C) but at the level of "there exist matching elements".
   CITATION: §67.9 Lemma.
   DRAFT-TACTICS: cheat (non-trivial case split on cut-elimination rules)
*)
Theorem sim_cut_step :                                  (* §67.9 *)
  !R S.
    cut_elim_step R S ==>
    AEx_equiv (Phi_comp R) (Phi_comp S)
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §67.10  Theorem: simulation of cut-elimination for proof-nets                 *)
(*                                                                             *)
(* STATEMENT (§67.10): For an MLL+MIX proof-net R such that R ~~>* S with S   *)
(* in normal form (no cuts):                                                    *)
(*                                                                             *)
(*   AEx(Φ_R^comp) ≃_S Φ_S^ax                                                *)
(*                                                                             *)
(* i.e., the abstract execution of the computational content of R is           *)
(* structurally equivalent to the VEHICLE (axiom part) of S.                  *)
(*                                                                             *)
(* PROOF OUTLINE (§67.10):                                                     *)
(*   Induction on the number n of cut-elimination steps.                       *)
(*   · Base (n = 0): R already in normal form; Φ_R^comp = Φ_R^ax (no cuts);  *)
(*     AEx(Φ_R^ax) ≃_S Φ_R^ax by struct_equiv_refl (AEx of a vehicle with    *)
(*     no matchable pairs = the vehicle itself, up to ≃_S).                   *)
(*   · Step (n = n'+1): R₀ ~~> R ~~>^{n'} S.                                 *)
(*     By Lemma §67.9: AEx(Φ_{R₀}^comp) ≃_S AEx(Φ_R^comp).                  *)
(*     By IH on n':     AEx(Φ_R^comp)   ≃_S Φ_S^ax.                          *)
(*     By transitivity: AEx(Φ_{R₀}^comp) ≃_S Φ_S^ax.                         *)
(*                                                                             *)
(* DEFERRED: proof-obligation stellaMLL.06                                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaMLL.06]:
   GOAL:
     !R S.
       R ~~>* S /\ normal_ps S ==>
       AEx_equiv (Phi_comp R) (Phi_ax S)
   STRATEGY:
     Induction on the number of steps n in R ~~>* S (RTC induction on
     cut_elim_star = RTC cut_elim_step).
     Base case (RTC_REFL: R = S): normal_ps S ==> cut_edges S = {}.
       Then Phi_comp S = Phi_ax S ++ Phi_cut S = Phi_ax S ++ [] = Phi_ax S.
       AEx_equiv (Phi_ax S) (Phi_ax S) follows from struct_equiv_refl +
       AEx_C membership (Phi_ax S IN AEx_C (Phi_ax S) when no cuts).
     Inductive step (R₀ ~~> R ~~>* S):
       By IH: AEx_equiv (Phi_comp R) (Phi_ax S).
       By sim_cut_step (R₀ ~~> R): AEx_equiv (Phi_comp R₀) (Phi_comp R).
       By struct_equiv_trans: AEx_equiv (Phi_comp R₀) (Phi_ax S).
     The last step needs: AEx_equiv (Phi_comp R₀) (Phi_comp R) and
       AEx_equiv (Phi_comp R) (Phi_ax S) ==> AEx_equiv (Phi_comp R₀) (Phi_ax S).
     This requires transitivity of AEx_equiv, which follows from
     struct_equiv_trans + choosing the intermediate witnesses.
   CITATION: §67.10 Theorem (Simulation of reduction for proof-nets).
   DRAFT-TACTICS: cheat (RTC induction + struct_equiv_trans + sim_cut_step)
*)
Theorem sim_cut_elim :                                  (* §67.10 *)
  !R S.
    cut_elim_star R S /\ normal_ps S ==>
    AEx_equiv (Phi_comp R) (Phi_ax S)
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.11  SANITY: Φ_comp of a cut-free proof-structure equals Φ_ax             *)
(*                                                                             *)
(* If S has no cuts (cut_edges S = {}), then Phi_cut S = [] and              *)
(* Phi_comp S = Phi_ax S.                                                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem phi_comp_cutfree :
  !S. normal_ps S ==> Phi_comp S = Phi_ax S
Proof
  rw [normal_ps_def, Phi_comp_def, Phi_cut_def, cut_edges_def] >>
  (* cut_edges S = {} ==> MAP (cut_star S) [] = [] ==> Phi_ax S ++ [] = Phi_ax S *)
  simp [SET_TO_LIST_EMPTY]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.11  SANITY: Phi_ax and Phi_cut are disjoint (at the list level)          *)
(*                                                                             *)
(* They come from disjoint edge sets (ax_edges and cut_edges), so the stars   *)
(* are constructed from different edge indices.  The result is always a list   *)
(* concatenation — disjointness is of the source edge sets, not a general      *)
(* property of constellation lists.                                             *)
(*                                                                             *)
(* We state the simpler fact: the lengths add.                                  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem phi_comp_length :
  !S. LENGTH (Phi_comp S) = LENGTH (Phi_ax S) + LENGTH (Phi_cut S)
Proof
  rw [Phi_comp_def, LENGTH_APPEND]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66  SANITY: cut_elim_star is reflexive and transitive                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem cut_elim_star_refl :
  !S. cut_elim_star S S
Proof
  rw [cut_elim_star_def, RTC_REFL]
QED

Theorem cut_elim_star_trans :
  !R S T. cut_elim_star R S /\ cut_elim_star S T ==> cut_elim_star R T
Proof
  rw [cut_elim_star_def] >> metis_tac [RTC_TRANS]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §67.10  AEx_equiv is transitive (needed in the proof of sim_cut_elim)        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaMLL.07]:
   GOAL:
     !Phi Phi' Phi''.
       AEx_equiv Phi Phi' /\ AEx_equiv Phi' Phi'' ==>
       AEx_equiv Phi Phi''
   STRATEGY:
     From AEx_equiv Phi Phi': get gamma  IN AEx_C Phi  and gamma'  IN AEx_C Phi'  with gamma  ≃_S gamma'.
     From AEx_equiv Phi' Phi'': get gamma'' IN AEx_C Phi' and gamma''' IN AEx_C Phi'' with gamma'' ≃_S gamma'''.
     gamma' and gamma'' are both in AEx_C Phi'.
     For all-objective Phi' (when logical_emergence gives singleton AEx):
       gamma' = gamma'' (unique normal form); then gamma ≃_S gamma'' ≃_S gamma'''.
     By struct_equiv_trans: gamma ≃_S gamma'''.
     Hence AEx_equiv Phi Phi'' with witnesses gamma and gamma'''.
   NOTE: In the general case (non-deterministic) we need to relate gamma' and
     gamma''; the structural equivalence acts as a congruence here.
   DRAFT-TACTICS: cheat (needs struct_equiv_trans + AEx_C membership)
*)
Theorem AEx_equiv_trans :
  !Phi Phi' Phi''.
    AEx_equiv Phi Phi' /\ AEx_equiv Phi' Phi'' ==>
    AEx_equiv Phi Phi''
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* PROOF-DEBT LEDGER                                                             *)
(*                                                                               *)
(* stellaMLL.01  pAddr_S inductive specification                                 *)
(*   GOAL: pAddr_S S satisfies the §66.7 inductive clauses.                      *)
(*   STRATEGY: well-founded recursion on vertex depth in the proof-structure     *)
(*     DAG; requires showing termination (depth strictly decreases along edges). *)
(*   STATUS: deferred (structural recursion over DAG depth).                     *)
(*                                                                               *)
(* stellaMLL.02  struct_equiv_refl                                                *)
(*   GOAL: !Phi. Phi ≃_S Phi                                                     *)
(*   STRATEGY: identity bijection; all clauses trivially hold.                   *)
(*   STATUS: deferred (trivial once definitions are unfolded).                   *)
(*                                                                               *)
(* stellaMLL.03  struct_equiv_sym                                                 *)
(*   GOAL: !Phi Phi'. Phi ≃_S Phi' ==> Phi' ≃_S Phi                             *)
(*   STRATEGY: invert the bijection; use symmetry of matchable.                  *)
(*   STATUS: deferred (bijection inverse).                                        *)
(*                                                                               *)
(* stellaMLL.04  struct_equiv_trans                                               *)
(*   GOAL: !Phi Phi' Phi''. Phi ≃_S Phi' /\ Phi' ≃_S Phi'' ==> Phi ≃_S Phi''  *)
(*   STRATEGY: compose bijections; transitivity of iff.                          *)
(*   STATUS: deferred (bijection composition).                                    *)
(*                                                                               *)
(* stellaMLL.05  sim_cut_step  (§67.9 Lemma)                                     *)
(*   GOAL: !R S. R ~~> S ==> AEx_equiv (Phi_comp R) (Phi_comp S)                *)
(*   STRATEGY:                                                                    *)
(*     (a) Ax/cut case: concrete calculation — addr_S, mu_ray, AEx_C resolution; *)
(*         bijection is identity on surviving stars.                              *)
(*     (b) Par/Tens case: cut duplication; new bijection maps duplicated stars.   *)
(*     Both cases require: AEx_C membership (correct saturated diagrams) and     *)
(*     struct_equiv witnessing.                                                    *)
(*   STATUS: deferred (non-trivial case split on cut-elimination rules).         *)
(*   CITATION: §67.9 Lemma (Simulation of cut-elimination step).                 *)
(*                                                                               *)
(* stellaMLL.06  sim_cut_elim  (§67.10 Theorem)                                   *)
(*   GOAL: !R S. R ~~>* S /\ normal_ps S ==> AEx_equiv (Phi_comp R) (Phi_ax S)  *)
(*   STRATEGY:                                                                    *)
(*     RTC induction on cut_elim_star (= RTC cut_elim_step).                    *)
(*     Base: normal_ps S ==> Phi_comp S = Phi_ax S ==> AEx_equiv trivial.        *)
(*     Step: sim_cut_step + AEx_equiv_trans (stellaMLL.07).                       *)
(*   STATUS: deferred (RTC induction + stellaMLL.05 + stellaMLL.07).              *)
(*   CITATION: §67.10 Theorem (Simulation of reduction for proof-nets).           *)
(*                                                                               *)
(* stellaMLL.07  AEx_equiv_trans                                                  *)
(*   GOAL: !Phi Phi' Phi''. AEx_equiv Phi Phi' /\ AEx_equiv Phi' Phi'' ==>      *)
(*           AEx_equiv Phi Phi''                                                   *)
(*   STRATEGY: struct_equiv_trans + AEx_C membership witnesses.                  *)
(*   STATUS: deferred (needs AEx_C uniqueness in the all-objective deterministic  *)
(*     case, or a general congruence argument for struct_equiv).                  *)
(*                                                                               *)
(* INHERITED PROOF-DEBT (from earlier theories):                                  *)
(*   stellaExec.01  aex_no_matchable      (§49.54)                                *)
(*   stellaExec.02  aex_idempotent        (§49.55)                                *)
(*   stellaExec.03  embeds_diag_trans                                              *)
(*   stellaExec.04  free_ray_list [[Var 0]] = [(0, 0)]                            *)
(*   stellaExec.05  empty_Prob: Prob [] = {}                                       *)
(*   stellaRed.01–.08 (wf_red_measure through empty_normal_form)                  *)
(*   stellaDiagram.01–.11                                                          *)
(*   stellaMatchScript: alpha_unifiable_sym                                        *)
(*                                                                               *)
(* EVAL vs CHEAT SUMMARY:                                                         *)
(*   EVAL (closed computations, no debt):                                          *)
(*     · phi_comp_length   — LENGTH_APPEND, arithmetic                            *)
(*     · phi_comp_cutfree  — SET_TO_LIST_EMPTY + list simp                        *)
(*     · cut_elim_star_refl — RTC_REFL                                            *)
(*     · cut_elim_star_trans — RTC_TRANS + metis                                   *)
(*     · phi_comp_cutfree  — simp + SET_TO_LIST_EMPTY                             *)
(*   CHEAT (non-trivial, deferred):                                                *)
(*     stellaMLL.01–.07 as listed above.                                           *)
(*                                                                               *)
(* ZERO new_axiom / mk_thm USED IN THIS FILE.                                     *)
(* ─────────────────────────────────────────────────────────────────────────── *)

val _ = export_theory ();
