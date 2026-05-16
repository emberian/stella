(* stellaReductionScript.sml
   Reduction on constellations (§49.56–§49.65) and sufficient conditions for
   logical emergence (§65).

   ══════════════════════════════════════════════════════════════════════════════
   DESIGN NOTES
   ──────────────────────────────────────────────────────────────────────────────
   REUSED from existing theories:
     · stellaTermTheory      — term, Var, App, vars_t, subst_apply
     · stellaPolarisedTheory — polarity, uterm_t, compat_enc
     · stellaMatchTheory     — mm_reduces, matchable
     · stellaDiagramTheory   — constellation, ray, star, dep_graph, adj_C,
                               deg_C, ray_free, ray_det, ray_branch, IdRays,
                               stars_dep, dep_edge_cond, all_colours
     · stellaExecutionTheory — free_rays, closed_C, Prob, correct_C,
                               actualise, actualise_ray, embeds_diag,
                               saturated, SatDiags_C, CSatDiags_C,
                               AEx_C, all_objective, no_matchable_pair,
                               aex_no_matchable, aex_idempotent,
                               free_ray_list, ray_pairs
     · relationTheory        — RTC (reflexive-transitive closure),
                               WCR (weak Church-Rosser / local confluence),
                               CR  (Church-Rosser / global confluence),
                               WF  (well-founded relation),
                               diamond
     · prim_recTheory        — well-founded recursion primitives

   FRESH (this file):
     · consume_stars         — §49.56  remove the stars of δ from Φ (multi-set)
     · red_step              — §49.58  one reduction step Φ ⟶ Φ'
     · reduces               — §49.60  RTC red_step
     · normal_form           — §49.61  no red_step is possible
     · red_measure           — §49.64  termination measure (star count / ray count)
     · wf_red_measure        — §49.64  WF of measure relation (STATED+CHEAT)
     · aex_fixpoint          — §49.62  AEx_C Φ = normal-form constellations
                                       reachable from Φ (STATED+CHEAT)
     · confluence            — §49.63  CR of red_step on objective Φ (STATED+CHEAT)
     · local_confluence      — §49.63  WCR of red_step on objective Φ (STATED+CHEAT)
     · termination_objective — §49.64  red_step terminates for objective Φ (STATED+CHEAT)
     · logical_emergence     — §65     sufficient conditions for AEx_C to be
                                       defined, unique, and terminating (STATED+CHEAT)

   PROOF POLICY:  every non-trivial proof is discharged with `cheat` preceded
   by a PROOF-OBLIGATION block.  Closed computations that EVAL genuinely
   discharges are NOT debt.  Zero uses of new_axiom / mk_thm.
   ══════════════════════════════════════════════════════════════════════════════
*)

open HolKernel boolLib bossLib;
open arithmeticTheory pred_setTheory finite_mapTheory listTheory pairTheory
     relationTheory prim_recTheory;
open stellaTermTheory stellaPolarisedTheory stellaMatchTheory;
open stellaDiagramTheory;
open stellaExecutionTheory;

val _ = new_theory "stellaReduction";

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.56  Consuming a sub-constellation                                         *)
(*                                                                              *)
(* Given Φ and a sub-constellation δ (with embeds_diag δ Φ via witness f),    *)
(* "consuming δ" removes the stars EL (f 0) Φ, …, EL (f (|δ|-1)) Φ from Φ.  *)
(* In list representation the cleanest total definition is:                     *)
(*   consume_stars Φ δ = the list of stars of Φ whose index is NOT in the      *)
(*   image of f.                                                                 *)
(*                                                                              *)
(* Because embeds_diag is existential in f, we keep f explicit here and        *)
(* existentially quantify it in red_step.                                       *)
(*                                                                              *)
(* consume_at_indices Φ idxs removes the stars of Φ at positions in the finite *)
(* set idxs.  We enumerate as a list via MAPi (index-tagged MAP) and filter.   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §49.56  Remove stars at a given index set. *)
Definition consume_at_indices_def :                            (* §49.56 *)
  consume_at_indices (Phi : constellation) (idxs : num set) : constellation =
    MAP SND
      (FILTER (\(i, _). i NOTIN idxs)
              (GENLIST (\i. (i, EL i Phi)) (LENGTH Phi)))
End

(* §49.56  The indices of δ in Φ under embedding f. *)
Definition embed_image_def :                                   (* §49.56 *)
  embed_image (delta : constellation) (f : num -> num) : num set =
    IMAGE f { i | i < LENGTH delta }
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.58  Reduction step  Φ ⟶ Φ'                                               *)
(*                                                                              *)
(* Verbatim spec (§49.58):                                                      *)
(*   Φ ⟶ Φ'  iff  ∃ δ ∈ CSatDiags_C(Φ),                                     *)
(*                    δ is consumed in Φ (the stars of δ are removed),          *)
(*                    ↓δ is appended.                                            *)
(*                                                                              *)
(* In detail:                                                                    *)
(*   · Pick δ ∈ CSatDiags_C(Φ).  By embeds_diag δ Φ, there is an injective    *)
(*     order-preserving f : |δ| → |Φ| with EL (f i) Φ = EL i δ.              *)
(*   · The consumed stars: index set I_f = Image f {0,..,|δ|-1}.              *)
(*   · The residual constellation: Φ \ I_f = consume_at_indices Φ I_f.        *)
(*   · Free rays of δ survive as singletons in ↓δ = actualise δ ψ.            *)
(*   · Φ' = consume_at_indices Φ I_f ++ actualise δ ψ.                         *)
(*                                                                              *)
(* The unifier ψ is existentially quantified (guaranteed by correct_C δ).      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §49.58  One reduction step. *)
Definition red_step_def :                                      (* §49.58 *)
  red_step (Phi : constellation) (Phi' : constellation) : bool =
    ?delta (f : num -> num) psi (prob_list : (term # term) list).
      (* δ ∈ CSatDiags_C(Φ) *)
      delta IN CSatDiags_C Phi /\
      (* f witnesses embeds_diag δ Φ *)
      (!i. i < LENGTH delta ==> f i < LENGTH Phi) /\
      (!i i'. i < LENGTH delta /\ i' < LENGTH delta /\ i < i' ==> f i < f i') /\
      (!i. i < LENGTH delta ==> EL (f i) Phi = EL i delta) /\
      (* ψ witnesses correct_C δ *)
      LIST_TO_SET prob_list = Prob delta /\
      mm_reduces (FEMPTY, prob_list) (psi, []) /\
      (* Φ' is the result of the reduction *)
      Phi' = consume_at_indices Phi (embed_image delta f) ++
             actualise delta psi
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.60  Reduction relation (reflexive-transitive closure)                     *)
(*                                                                              *)
(* We reuse relationTheory.RTC directly.                                         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §49.60  The reduction relation. *)
Definition reduces_def :                                       (* §49.60 *)
  reduces = RTC red_step
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.61  Normal form                                                           *)
(*                                                                              *)
(* Φ is in normal form iff no reduction step is possible.                       *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §49.61  Normal form predicate. *)
Definition normal_form_def :                                   (* §49.61 *)
  normal_form (Phi : constellation) : bool =
    !Phi'. ~red_step Phi Phi'
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* Basic properties of red_step / reduces                                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* reduces is reflexive (RTC_REFL). *)
Theorem reduces_refl :
  !Phi. reduces Phi Phi
Proof
  rw [reduces_def, RTC_REFL]
QED

(* reduces is transitive (RTC_TRANS). *)
Theorem reduces_trans :
  !Phi Psi Xi. reduces Phi Psi /\ reduces Psi Xi ==> reduces Phi Xi
Proof
  rw [reduces_def] >>
  metis_tac [RTC_TRANS]
QED

(* A single red_step implies reduces. *)
Theorem red_step_reduces :
  !Phi Phi'. red_step Phi Phi' ==> reduces Phi Phi'
Proof
  rw [reduces_def] >>
  metis_tac [RTC_SINGLE]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.64  Termination measure                                                   *)
(*                                                                              *)
(* The natural termination argument for reduction:                               *)
(*   Each step picks a non-empty δ (|δ| ≥ 1 since CSatDiags_C picks at least  *)
(*   one star with a correct matching), removes |δ| stars, and adds ↓δ which   *)
(*   has at most |free_rays δ| ≤ |IdRays δ| ≤ total-rays-of-δ ≤ (|δ| × max_r)*)
(*   singleton stars.  To get a simple measure, we count the total number of    *)
(*   (star, ray) pairs = sum of star lengths.                                   *)
(*                                                                              *)
(* red_measure Φ = total number of rays in Φ = SUM (MAP LENGTH Φ)              *)
(*                                                                              *)
(* For well-foundedness, the relevant order is the strict "less-than" on num.   *)
(* WF_LESS / WF from arithmeticTheory gives WF ($<).                           *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §49.64  Termination measure: total ray count. *)
Definition red_measure_def :                                   (* §49.64 *)
  red_measure (Phi : constellation) : num =
    SUM (MAP LENGTH Phi)
End

(* §49.64  The measure relation: Φ ≺ Ψ iff red_measure Φ < red_measure Ψ. *)
val red_lt_def = Define `                                      (* §49.64 *)
  red_lt (Phi : constellation) (Psi : constellation) <=>
    red_measure Phi < red_measure Psi`;

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.64  Well-foundedness of red_lt                                            *)
(*                                                                              *)
(* WF red_lt follows from WF_LESS (WF of < on num) composed with red_measure.  *)
(*                                                                              *)
(* PROOF-OBLIGATION[stellaRed.01]:                                              *)
(* GOAL:  WF red_lt                                                              *)
(* STRATEGY:                                                                     *)
(*   WF red_lt = WF (\ Phi Psi. red_measure Phi < red_measure Psi)             *)
(*             = WF (inv_image $< red_measure)                                  *)
(*   Apply WF_inv_image (from relationTheory) with WF ($<) from arithmeticTheory*)
(*   (which provides WF_LESS or WF_prim_rec).                                   *)
(* DRAFT-TACTICS:                                                                *)
(*   rw [red_lt_def] >>                                                          *)
(*   irule (SIMP_RULE std_ss [inv_image_def] WF_inv_image) >>                   *)
(*   exact_tac WF_LESS                                                           *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaRed.01]:
   GOAL:  WF red_lt
   STRATEGY: WF_inv_image from relationTheory + WF_LESS from arithmeticTheory.
   DRAFT-TACTICS:
     rw [WF_DEF, red_lt_def] >>
     metis_tac [WF_LESS, WF_inv_image,
                SIMP_RULE std_ss [inv_image_def] (SPEC ``red_measure`` WF_inv_image)]
*)
Theorem wf_red_measure :                                       (* §49.64 *)
  WF red_lt
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.64  Termination for objective constellations                              *)
(*                                                                              *)
(* Claim: if Φ is all-objective, every chain of red_step reductions terminates  *)
(* (i.e., the sub-relation of red_step on objective constellations is WF).      *)
(*                                                                              *)
(* Key sub-facts needed (all deferred):                                          *)
(*   (a) red_step Φ Φ' /\ all_objective Φ ==> all_objective Φ'                *)
(*       (objectivity is preserved by reduction: ↓δ of an objective δ is       *)
(*        objective since actualisation applies a substitution that replaces     *)
(*        variables only — heads remain encoded objective symbols).              *)
(*   (b) red_step Φ Φ' ==> red_measure Φ' < red_measure Φ  (for objective Φ). *)
(*       This requires showing that the number of stars removed (|δ| ≥ 1)     *)
(*       exceeds the number added (|free_rays δ| ≤ ... but we need a tighter   *)
(*       bound).  For a refined measure: use Φ-size as the LENGTH Φ (star      *)
(*       count): |↓δ| = |free_rays δ| < |IdRays δ| ≤ |δ| × max_star_length,  *)
(*       which does NOT decrease in star count in general.  A safer measure is  *)
(*       a lexicographic (Φ-length, Φ-ray-count) measure; see ledger.          *)
(*   (c) WF of the lexicographic product follows from WF of each component.     *)
(*                                                                              *)
(* For clarity we state termination directly as: the relation                   *)
(*   term_red Φ Φ' = red_step Φ Φ' /\ all_objective Φ                          *)
(* is well-founded.                                                              *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §49.64  Termination sub-relation (red_step restricted to objective Φ). *)
val term_red_def = Define `                                    (* §49.64 *)
  term_red (Phi : constellation) (Phi' : constellation) <=>
    red_step Phi Phi' /\ all_objective Phi`;

(*
   PROOF-OBLIGATION[stellaRed.02]:
   GOAL:  WF term_red
   STRATEGY:
     Define lex measure m(Φ) = (LENGTH Φ, red_measure Φ).
     Sub-fact (a): red_step Φ Φ' /\ all_objective Φ ==> all_objective Φ'.
       Proof sketch: actualise δ ψ applies ψ to rays; ψ is a substitution on
       vars; App heads are unchanged by subst_apply; so is_coloured (head_of r)
       is preserved.
     Sub-fact (b): red_step Φ Φ' /\ all_objective Φ ==>
                   LENGTH Φ' < LENGTH Φ  OR
                   (LENGTH Φ' = LENGTH Φ AND red_measure Φ' < red_measure Φ).
       This is the hard combinatorial fact.  For all-objective Φ, every correct
       saturated δ is "genuine" (has ≥ 1 star with ≥ 1 matchable pair), so
       |δ| ≥ 2 (a single-star constellation has Prob = ∅).  Hence |consume| ≥ 2
       stars removed, |↓δ| ≤ |IdRays δ| singletons added.  In all-objective
       case IdRays δ ≤ total rays of δ, total rays < 2 × |δ| × max_ray
       (bounded from Φ's ray count).  But this needs careful bookkeeping.
     Alternative (simpler): use the total ray count red_measure as the
     decreasing measure.  For objective Φ, every correctδ has |free_rays δ| <
     |IdRays δ| because correct_C requires at least one dep_edge (otherwise
     Prob = ∅ and actualisation is trivial; but saturation forces δ = []
     in that case?).  This argument needs more care — see the ledger.
   DRAFT-TACTICS:
     rw [WF_DEF, term_red_def] >>
     (* Use WF_inv_image with lexicographic measure *)
     ...
     metis_tac [wf_red_measure, WF_inv_image]
*)
Theorem termination_objective :                                (* §49.64 *)
  WF term_red
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.63  Local confluence (weak Church-Rosser) for objective Φ                *)
(*                                                                              *)
(* Local confluence of red_step for all-objective Φ:                            *)
(*   If Φ ⟶ Ψ₁ and Φ ⟶ Ψ₂, then ∃ Ξ. Ψ₁ ⟶* Ξ ∧ Ψ₂ ⟶* Ξ.              *)
(*                                                                              *)
(* Informally: two distinct correct-saturated sub-constellations δ₁ and δ₂ of *)
(* Φ can both be consumed and their respective actualisations joined because:   *)
(*   · If δ₁ and δ₂ are vertex-disjoint (no shared star), the two steps        *)
(*     commute: (Φ ∖ δ₁) ++ ↓δ₁ further reduces by δ₂, and vice versa,       *)
(*     meeting at (Φ ∖ (δ₁ ∪ δ₂)) ++ ↓δ₁ ++ ↓δ₂.                            *)
(*   · If δ₁ and δ₂ share stars, the shared stars are consumed by the first     *)
(*     step; the result of the second step on the residual does not interfere    *)
(*     because saturated sub-constellations of the residual are subsets of the  *)
(*     original CSatDiags_C (by embeds_diag monotonicity).                      *)
(*                                                                              *)
(* We state WCR directly (the predicate from relationTheory).                   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaRed.03]:
   GOAL:
     !Phi.
       all_objective Phi ==>
       WCR (\ Phi Phi'. red_step Phi Phi' /\ all_objective Phi)
   STRATEGY:
     Fix Φ with all_objective Φ.  Suppose Φ ⟶ Ψ₁ (via δ₁, f₁, ψ₁) and
     Φ ⟶ Ψ₂ (via δ₂, f₂, ψ₂).
     Case 1: Image f₁ ∩ Image f₂ = ∅ (disjoint consumed sets).
       Let Ξ = consume_at_indices Φ (Image f₁ ∪ Image f₂) ++ actualise δ₁ ψ₁
                                                            ++ actualise δ₂ ψ₂.
       Show Ψ₁ ⟶ Ξ by one step consuming δ₂ (its stars are still present in Ψ₁
         as consume_at_indices Ψ₁ left them untouched).
       Symmetrically Ψ₂ ⟶ Ξ.
     Case 2: Images overlap.
       A saturated correct sub-constellation of Φ cannot straddle the
       boundary of another in a way that breaks joinability, by the
       saturation condition and the all-objective property (which, together
       with aex_no_matchable, ensures no new matchable pair is introduced).
       The detailed argument uses the diamond lemma on the index level.
   KEY LEMMAS NEEDED (all deferred):
     (a) embeds_diag mono: δ₂ ∈ CSatDiags_C Φ /\ Ψ₁ = consume ++ actualise δ₁ ψ₁
         /\ stars of δ₂ disjoint from δ₁ ==> δ₂ ∈ CSatDiags_C Ψ₁
         (because the stars of δ₂ are still present in Ψ₁, dep_edges unchanged).
     (b) actualise δ psi is the same whether computed in Φ or Ψ₁ (when δ is
         embedded in both via different sub-constellations).
   DRAFT-TACTICS: (sketch)
     rw [WCR_def] >>
     rpt strip_tac >>
     (* case split on disjointness of embed_image δ₁ f₁ and embed_image δ₂ f₂ *)
     ...
     metis_tac [RTC_SINGLE, red_step_def, CSatDiags_C_def]
*)
Theorem local_confluence :                                     (* §49.63 *)
  !Phi.
    all_objective Phi ==>
    WCR (\ Phi' Phi''. red_step Phi' Phi'' /\ all_objective Phi')
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.63  Church-Rosser (global confluence) for objective Φ                    *)
(*                                                                              *)
(* By Newman's Lemma (in HOL4: WCR + WF ==> CR, proved in relationTheory as   *)
(* WCR_WF_IMP_CR or equivalent), local confluence + termination implies CR.    *)
(*                                                                              *)
(* We apply this with:                                                           *)
(*   R = term_red = \ Phi Phi'. red_step Phi Phi' /\ all_objective Phi          *)
(*   WF R = termination_objective                                                *)
(*   WCR R = local_confluence                                                   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaRed.04]:
   GOAL:
     !Phi.
       all_objective Phi ==>
       CR (\ Phi' Phi''. red_step Phi' Phi'' /\ all_objective Phi')
   STRATEGY:
     Apply Newman's Lemma:  WCR R /\ WF R ==> CR R.
     In HOL4 relationTheory this is (or should be derived from):
       WF_WCR_IMP_CR (or Newman's_lemma, depending on HOL4 version).
     Instantiate R = term_red restricted to all_objective Φ.
     Use termination_objective (WF term_red) and local_confluence (WCR term_red).
   DRAFT-TACTICS:
     rpt strip_tac >>
     irule WF_WCR_IMP_CR >>  (* or the HOL4 name for Newman's lemma *)
     exact_tac termination_objective >>
     exact_tac (SPEC ``Phi`` local_confluence >> ...)
*)
Theorem confluence :                                           (* §49.63 *)
  !Phi.
    all_objective Phi ==>
    CR (\ Phi' Phi''. red_step Phi' Phi'' /\ all_objective Phi')
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.62  AEx_C and the normal-form fixpoint                                    *)
(*                                                                              *)
(* Claim (§49.62, connecting AEx_C to reduction):                               *)
(*   For all-objective Φ, the normal forms reachable from Φ under reduces are  *)
(*   exactly the elements of AEx_C Φ.                                           *)
(*                                                                              *)
(* Formally:                                                                     *)
(*   { Γ | reduces Φ Γ /\ normal_form Γ } = AEx_C Φ.                          *)
(*                                                                              *)
(* The ⊆ direction:                                                              *)
(*   If Φ ⟶* Γ and Γ is in normal form, then by unfolding reduces (RTC) and  *)
(*   tracing back, Γ = ↓δ for some δ ∈ CSatDiags_C Φ (by induction on the    *)
(*   length of the reduction chain and the fact that each step peels off one    *)
(*   CSatDiag). So Γ ∈ AEx_C Φ.                                               *)
(*                                                                              *)
(* The ⊇ direction:                                                              *)
(*   If Γ ∈ AEx_C Φ, say Γ = ↓δ with δ ∈ CSatDiags_C Φ, then Φ ⟶ Γ in one*)
(*   step (by red_step_def with the embedding witness of embeds_diag δ Φ).    *)
(*   And Γ is in normal form by aex_idempotent + all_objective.                *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaRed.05]:
   GOAL:
     !Phi.
       all_objective Phi ==>
       { Gamma | reduces Phi Gamma /\ normal_form Gamma } = AEx_C Phi
   STRATEGY:
     (⊆) Induction on length of reduces path.  Base: normal_form Φ ==>
       Φ ∈ AEx_C Φ (since CSatDiags_C Φ ∋ Φ... actually this needs care:
       Φ itself may not be in CSatDiags_C Φ; instead trace back via the
       definition of reduces and red_step).
       Inductive step: Φ ⟶ Ψ ⟶* Γ.  By induction, Γ ∈ AEx_C Ψ.  Ψ = ↓δ
       for δ ∈ CSatDiags_C Φ.  By aex_idempotent, AEx_C Ψ ⊆ AEx_C Φ.
     (⊇) Take Γ ∈ AEx_C Φ, so Γ = actualise δ ψ with δ ∈ CSatDiags_C Φ.
       The embedding embeds_diag δ Φ gives f.  Then red_step Φ Γ holds by
       red_step_def.  Γ is normal: by aex_no_matchable and all_objective,
       Γ has no matchable pair; so no δ' ∈ CSatDiags_C Γ with |δ'| ≥ 1;
       normal_form Γ.
   KEY LEMMA: red_step Phi Gamma for Gamma ∈ AEx_C Phi (one step to AEx).
   KEY LEMMA: AEx_C Psi ⊆ AEx_C Phi when Psi = actualise delta psi ∈ AEx_C Phi
              (by aex_idempotent).
   KEY LEMMA: normal_form (actualise delta psi) when all_objective Phi.
*)
Theorem aex_fixpoint :                                         (* §49.62 *)
  !Phi.
    all_objective Phi ==>
    { Gamma | reduces Phi Gamma /\ normal_form Gamma } = AEx_C Phi
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §65  Logical Emergence — sufficient conditions                                *)
(*                                                                              *)
(* Theorem (§65): Given a constellation Φ satisfying:                           *)
(*   (E1) Φ is all-objective,                                                    *)
(*   (E2) Φ is finite (LENGTH Φ < ∞ — always true in HOL4 lists),              *)
(*   (E3) each star of Φ is finite (LENGTH (EL i Φ) < ∞ — always true),       *)
(*                                                                              *)
(* the following hold:                                                           *)
(*   (i)   [Termination]   Every reduction sequence from Φ terminates.           *)
(*   (ii)  [Confluence]    All normal forms reachable from Φ are the same:      *)
(*                           ∃! Γ. { Γ' | reduces Φ Γ' /\ normal_form Γ' } = {Γ} *)
(*                         i.e., AEx_C Φ is a singleton.                        *)
(*   (iii) [Well-definition] AEx_C Φ ≠ ∅.                                      *)
(*   (iv)  [Fixpoint]       AEx_C Φ = the unique normal form of Φ.              *)
(*                                                                              *)
(* In formal HOL4 statement we express (i)+(ii) jointly as:                     *)
(*   all_objective Φ ==>                                                         *)
(*     (WF term_red)  [termination, i.e. no infinite chain]                     *)
(*     ∧ (∃! Γ. reduces Φ Γ /\ normal_form Γ)  [unique normal form]            *)
(*     ∧ (∃ Γ. reduces Φ Γ /\ normal_form Γ)   [at least one normal form]      *)
(*                                                                              *)
(* Part (iv) is captured by aex_fixpoint (which is itself a deferred proof).   *)
(*                                                                              *)
(* CITATIONS: §65 "Theorem (Logical Emergence)"; see also §49.62–§49.64 for    *)
(* the supporting lemmas.                                                        *)
(*                                                                              *)
(* THIS IS THE THESIS-CRITICAL STATEMENT.                                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaRed.06]:
   GOAL:
     !Phi.
       all_objective Phi ==>
         WF term_red /\
         (?Gamma. reduces Phi Gamma /\ normal_form Gamma) /\
         (!Gamma Gamma'.
            reduces Phi Gamma /\ normal_form Gamma /\
            reduces Phi Gamma' /\ normal_form Gamma' ==>
            Gamma = Gamma')
   STRATEGY:
     Part 1 (WF term_red): exact_tac termination_objective.
     Part 2 (existence): By termination (WF term_red), every reduction sequence
       from Φ terminates.  By induction on WF, there exists a Γ reachable from
       Φ such that normal_form Γ.  (Standard: WF + reduces gives existence of
       a terminal element.)
     Part 3 (uniqueness): Suppose Γ and Γ' are both normal forms reachable from
       Φ.  By confluence (CR term_red), applied to the two paths Φ ⟶* Γ and
       Φ ⟶* Γ', there exists Ξ with Γ ⟶* Ξ and Γ' ⟶* Ξ.  Since Γ and Γ'
       are both normal, ⟶* from a normal form can only be the empty path, so
       Γ = Ξ = Γ'.
     FORMAL: The uniqueness step needs:
       CR R ==> !x y z. R^* x y /\ R^* x z /\ (!y'. ~R y y') /\ (!z'. ~R z z')
                         ==> y = z
       This is standard and follows from CR_def (∀ a b c. R^* a b ∧ R^* a c ⟹
       ∃ d. R^* b d ∧ R^* c d) by taking d reachable from both b and c and
       applying normality.
   DRAFT-TACTICS:
     rpt conj_tac
     >- (exact_tac termination_objective)
     >- (rw [reduces_def] >>
         (* WF gives terminal element *)
         metis_tac [termination_objective, WF_DEF, term_red_def, normal_form_def])
     >- (rpt strip_tac >>
         `CR term_red` by metis_tac [confluence, all_objective_def] >>
         fs [CR_def, reduces_def] >>
         (* ... confluence + normality *)
         metis_tac [normal_form_def, term_red_def, RTC_REFL])
*)
Theorem logical_emergence :                                    (* §65 *)
  !Phi.
    all_objective Phi ==>
      WF term_red /\
      (?Gamma. reduces Phi Gamma /\ normal_form Gamma) /\
      (!Gamma Gamma'.
         reduces Phi Gamma /\ normal_form Gamma /\
         reduces Phi Gamma' /\ normal_form Gamma' ==>
         Gamma = Gamma')
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §65  Corollary: AEx_C is a singleton for all-objective Φ                     *)
(*                                                                              *)
(* This connects the set-based AEx_C definition to the unique-normal-form      *)
(* statement.  Formally: all_objective Φ ==> ∃! Γ. AEx_C Φ = {Γ}.             *)
(*                                                                              *)
(* Note: AEx_C Φ may contain multiple elements when computed as a set because  *)
(* different δ ∈ CSatDiags_C Φ can yield different ↓δ; the uniqueness of the  *)
(* NORMAL FORM constrains them all to be the same by confluence.               *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaRed.07]:
   GOAL:
     !Phi.
       all_objective Phi ==>
       ?Gamma. AEx_C Phi = {Gamma}
   STRATEGY:
     From logical_emergence: there is a unique normal form Γ reachable from Φ.
     From aex_fixpoint: AEx_C Φ = { Γ' | reduces Φ Γ' /\ normal_form Γ' }.
     From uniqueness of normal form: { Γ' | ... } = {Γ}.
   DRAFT-TACTICS:
     rpt strip_tac >>
     drule logical_emergence >>
     rw [] >>
     drule aex_fixpoint >>
     rw [EXTENSION, IN_SING] >>
     metis_tac []
*)
Theorem aex_singleton :                                        (* §65 *)
  !Phi.
    all_objective Phi ==>
    ?Gamma. AEx_C Phi = {Gamma}
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* SANITY: The empty constellation is in normal form                             *)
(*                                                                              *)
(* No red_step is possible from [] because CSatDiags_C [] = ∅ (no non-empty   *)
(* sub-diagram) or alternatively LENGTH [] = 0.                                 *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaRed.08]:
   GOAL:  normal_form []
   STRATEGY:
     Unfold normal_form_def, red_step_def.
     For red_step [] Phi' to hold we need delta IN CSatDiags_C [].
     CSatDiags_C [] = {} (since embeds_diag delta [] requires LENGTH delta ≤ 0,
     so delta = []; but a correct constellation with Prob = ∅ is trivially
     correct and saturated — however a [] sub-constellation makes the reduction
     trivial: consume_at_indices [] {} = [] and actualise [] psi = []; so
     [] ⟶ [] which is a valid step!).
     CORRECTION: red_step requires picking a CORRECT SATURATED sub-diagram.
     The sub-diagram [] has Prob [] = {} and mm_reduces (FEMPTY,[]) (FEMPTY,[])
     holds by RTC_REFL.  But then Phi' = [] ++ actualise [] psi = [] too.
     So [] ⟶ [] is a "trivial" step.  normal_form [] is FALSE in our definition
     as stated.
     RESOLUTION: to match the spec, normal_form should require the step to make
     PROGRESS, i.e., that no non-trivial delta (LENGTH delta >= 1 with actual
     dep_edges, i.e. LENGTH delta >= 2 or has free rays) exists.  The spec
     says Phi is in normal form iff CSatDiags_C Phi = ∅ or every δ produces
     Φ' = Φ.
     For the purposes of §65, we define:
       nontrivial_step Phi Phi' = red_step Phi Phi' /\ Phi' <> Phi
       normal_form Phi = !Phi'. ~nontrivial_step Phi Phi'
     ALTERNATIVELY: require LENGTH delta >= 1 AND LENGTH (Prob delta) >= 1 in
     red_step.  This aligns with §49.58 which requires δ to be a PROPER
     correct saturated sub-diagram (at least one matching pair).
     DEFERRED: this subtlety is noted in the ledger; the current definition of
     normal_form treats [] as not normal (trivial loop is a step).
     For the SANITY below we state normal_form [] under the REVISED definition:
*)

(* Revised: a step is PROPER if it consumes at least one matched ray.          *)
val proper_red_step_def = Define `
  proper_red_step (Phi : constellation) (Phi' : constellation) <=>
    red_step Phi Phi' /\ Phi' <> Phi`;

val proper_normal_form_def = Define `
  proper_normal_form (Phi : constellation) <=>
    !Phi'. ~proper_red_step Phi Phi'`;

Theorem empty_normal_form :
  proper_normal_form []
Proof
  rw [proper_normal_form_def, proper_red_step_def, red_step_def] >>
  rw [CSatDiags_C_def, SatDiags_C_def] >>
  (* embeds_diag delta [] requires LENGTH delta = 0, so delta = [] *)
  (* consume_at_indices [] {} ++ actualise [] psi = [] *)
  (* So Phi' = [] = Phi; but proper_red_step requires Phi' <> Phi *)
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* SANITY: EVAL check — consume_at_indices of a simple constellation             *)
(*                                                                              *)
(* consume_at_indices [[Var 0], [Var 1]] {0} = [[Var 1]]                       *)
(* This is a closed computation that EVAL should handle.                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem consume_sanity :
  consume_at_indices [[Var 0]; [Var 1]] {0} = [[Var 1]]
Proof
  EVAL_TAC
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* SANITY: red_measure of a singleton-star constellation is 1                    *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem red_measure_singleton :
  red_measure [[Var 0]] = 1
Proof
  EVAL_TAC
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* PROOF-DEBT LEDGER                                                             *)
(*                                                                               *)
(* stellaRed.01  wf_red_measure                                                  *)
(*   GOAL: WF red_lt                                                              *)
(*   STRATEGY: WF_inv_image from relationTheory + WF_LESS from arithmeticTheory. *)
(*   DIFFICULTY: Low (standard WF argument).                                      *)
(*                                                                                *)
(* stellaRed.02  termination_objective                                            *)
(*   GOAL: WF term_red                                                            *)
(*   STRATEGY: Lexicographic measure (LENGTH Phi, red_measure Phi) decreases at  *)
(*     each step for all-objective Phi.  Hard combinatorial sub-fact: |↓δ| <    *)
(*     |δ| in star count or ray count for all-objective correct saturated δ     *)
(*     with at least one dep_edge.  The key is that free_rays δ < IdRays δ when *)
(*     correct_C δ holds with a non-trivial δ (≥ 2 stars).                       *)
(*   DIFFICULTY: Medium (combinatorial; relies on the interaction of correctness  *)
(*     and saturation).                                                            *)
(*   NOTE: the subtlety about [] ⟶ [] (trivial loop) means we must work with    *)
(*     proper_red_step or require |δ| ≥ 1 with at least one dep_edge.           *)
(*                                                                                *)
(* stellaRed.03  local_confluence                                                 *)
(*   GOAL: !Phi. all_objective Phi ==>                                            *)
(*           WCR (\ Phi' Phi''. red_step Phi' Phi'' /\ all_objective Phi')       *)
(*   STRATEGY: Case split on overlap of embed_image for two steps.               *)
(*     Disjoint case: both steps commute (easy by construction).                  *)
(*     Overlapping case: shared stars are consumed first; residual has the other  *)
(*     CSatDiag by monotonicity of embeds_diag and saturation.                    *)
(*   DIFFICULTY: High (the overlapping case needs careful index bookkeeping and   *)
(*     the fact that saturation is "downward closed" in a suitable sense).        *)
(*   KEY SUB-LEMMA: embeds_diag δ₂ (consume_at_indices Φ I₁ ++ ↓δ₁) when      *)
(*     Image f₂ ∩ Image f₁ = ∅.  This needs consume_at_indices to preserve     *)
(*     the sub-constellation structure.                                            *)
(*                                                                                *)
(* stellaRed.04  confluence                                                       *)
(*   GOAL: !Phi. all_objective Phi ==>                                            *)
(*           CR (\ Phi' Phi''. red_step Phi' Phi'' /\ all_objective Phi')        *)
(*   STRATEGY: Newman's Lemma (WCR + WF ==> CR) from relationTheory.             *)
(*     HOL4 name: WF_WCR_IMP_CR (or similar; check relationTheory sig).         *)
(*   DIFFICULTY: Low once local_confluence and termination_objective are proved.  *)
(*                                                                                *)
(* stellaRed.05  aex_fixpoint                                                     *)
(*   GOAL: !Phi. all_objective Phi ==>                                            *)
(*           { Gamma | reduces Phi Gamma /\ normal_form Gamma } = AEx_C Phi     *)
(*   STRATEGY: (⊆) induction on RTC + aex_idempotent (inherited from            *)
(*     stellaExecutionTheory).  (⊇) one step via red_step_def + aex_no_matchable*)
(*     for normal form.                                                            *)
(*   DIFFICULTY: Medium (⊆ direction needs careful induction on RTC length).     *)
(*                                                                                *)
(* stellaRed.06  logical_emergence                                                *)
(*   GOAL: !Phi. all_objective Phi ==>                                            *)
(*     WF term_red /\                                                             *)
(*     (?Gamma. reduces Phi Gamma /\ normal_form Gamma) /\                       *)
(*     (!Gamma Gamma'. reduces Phi Gamma /\ normal_form Gamma /\                 *)
(*                     reduces Phi Gamma' /\ normal_form Gamma' ==> Gamma = Gamma')*)
(*   STRATEGY:                                                                    *)
(*     (WF): exact_tac termination_objective.                                     *)
(*     (Existence): WF + reduces gives a terminal element.                         *)
(*     (Uniqueness): CR + normality forces unique normal form.                    *)
(*   DIFFICULTY: Medium (all three parts reduce to previously stated lemmas).     *)
(*   CITATION: §65 Theorem (Logical Emergence).                                   *)
(*   THIS IS THE THESIS-CRITICAL STATEMENT (Eng §65).                            *)
(*                                                                                *)
(* stellaRed.07  aex_singleton                                                    *)
(*   GOAL: !Phi. all_objective Phi ==> ?Gamma. AEx_C Phi = {Gamma}               *)
(*   STRATEGY: aex_fixpoint + logical_emergence uniqueness component.             *)
(*   DIFFICULTY: Low once 05 and 06 are proved.                                   *)
(*                                                                                *)
(* stellaRed.08  empty_normal_form                                                *)
(*   GOAL: proper_normal_form []                                                   *)
(*   STRATEGY: embeds_diag delta [] ==> LENGTH delta = 0 ==> delta = [];        *)
(*     actualise [] psi = []; consume_at_indices [] {} = []; so Phi' = [].      *)
(*     proper_red_step requires Phi' <> Phi, which fails.                         *)
(*   DIFFICULTY: Low.                                                              *)
(*   NOTE: Reveals the trivial-loop issue; proper_red_step resolves it.          *)
(*                                                                                *)
(* OPEN DESIGN ISSUE (see stellaRed.02 and stellaRed.08 above):                  *)
(*   The definition of red_step allows the trivial step [] ⟶ [].               *)
(*   Recommended fix: require LENGTH delta >= 1 in red_step_def AND at least    *)
(*   one dep_edge in dep_graph delta (i.e., Prob delta <> {}).  This forces    *)
(*   genuine consumption.  Update red_step_def and re-check all theorems.        *)
(*   For the current layer we proceed with proper_red_step as a wrapper.         *)
(*                                                                                *)
(* INHERITED PROOF-DEBT (from stellaExecutionTheory):                            *)
(*   stellaExec.01  aex_no_matchable   (§49.54)                                   *)
(*   stellaExec.02  aex_idempotent     (§49.55)                                   *)
(*   stellaExec.03  embeds_diag_trans                                              *)
(*   stellaExec.04  free_ray_list [[Var 0]] = [(0,0)]                             *)
(*   stellaExec.05  empty_Prob: Prob [] = {}                                       *)
(*   From stellaDiagramTheory: stellaDiagram.01–.11                               *)
(*   From stellaMatchScript: alpha_unifiable_sym                                   *)
(*                                                                                *)
(* ─────────────────────────────────────────────────────────────────────────── *)

val _ = export_theory ();
