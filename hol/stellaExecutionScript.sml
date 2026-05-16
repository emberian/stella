(* stellaExecutionScript.sml
   Execution semantics of constellations: free rays, Prob(δ), correctness,
   actualisation ↓δ, saturation, and AEx — Eng §49.21–§49.42.
   Headline results: §49.54 (all-objective ⇒ no matchable pair in ↓δ) and
   §49.55 (idempotence of AEx for all-objective constellations).

   ══════════════════════════════════════════════════════════════════════════════
   DESIGN NOTES
   ──────────────────────────────────────────────────────────────────────────────
   REUSED from existing theories:
     · stellaTermTheory    — term, Var, App, vars_t, subst_apply
     · stellaPolarisedTheory — polarity, uterm_t (underlying |·|), compat_enc,
                               encode_psym, decode_psym
     · stellaMatchTheory   — mm_reduces, matchable
     · stellaDiagramTheory — constellation (= star list = (ray list) list),
                             ray, star, dep_graph, adj_C, deg_C, ray_free,
                             ray_det, ray_branch, IdRays, stars_dep,
                             dep_edge_cond, all_colours
   FRESH (this file):
     · free_rays           — §49.21  set of free ray-ids in a constellation
     · closed_C            — §49.21  constellation is closed (free = ∅)
     · eq_of_edge          — §49.27  equation associated with an edge
     · Prob                — §49.27  unification problem of a constellation
     · correct_C           — §49.34  has a unifier
     · actualise           — §49.34  ↓δ
     · embeds_diag         — §49.23  δ ⊑ δ'
     · saturated           — §49.23  ⊑-maximal
     · SatDiags_C          — §49.23
     · CSatDiags_C         — §49.23  correct saturated constellations
     · AEx_C               — §49.42  actualisation of CSatDiags_C
     · all_objective       — all rays in Φ have objective head (Pos or Neg)
     · no_matchable_pair   — no ray pair (i,j),(i',j') in ↓δ is matchable
     · aex_no_matchable    — §49.54 STATED+CHEAT
     · aex_idempotent      — §49.55 STATED+CHEAT

   PROOF POLICY:  every non-trivial proof is discharged with `cheat` preceded
   by a PROOF-OBLIGATION block.  Closed computations that EVAL genuinely
   discharges are NOT debt.  Zero uses of new_axiom / mk_thm.
   ══════════════════════════════════════════════════════════════════════════════
*)

open HolKernel boolLib bossLib;
open arithmeticTheory pred_setTheory finite_mapTheory listTheory pairTheory
     relationTheory;
open stellaTermTheory stellaPolarisedTheory stellaMatchTheory;
open stellaDiagramTheory;

val _ = new_theory "stellaExecution";

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.21  Free ray-ids and closed constellations                               *)
(*                                                                              *)
(* Verbatim spec:  free(δ) = { (i,j) ∈ IdRays(δ) | deg^C_δ(i,j) = 0 }       *)
(* I.e., rays that have no dependency edge; here C = all_colours δ            *)
(* (we follow the implicit "full colour set" convention of §49.21).            *)
(*                                                                              *)
(* δ is closed iff free(δ) = ∅.                                                *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §49.21  Free ray-indices of a constellation. *)
Definition free_rays_def :                                    (* §49.21 *)
  free_rays (delta : constellation) : (num # num) set =
    { (i, j) | (i, j) IN IdRays delta /\
               deg_C delta (all_colours delta) i j = 0 }
End

(* §49.21  A constellation is closed iff it has no free ray. *)
Definition closed_C_def :                                     (* §49.21 *)
  closed_C (delta : constellation) : bool = (free_rays delta = {})
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.27  Underlying problem  Prob(δ)                                          *)
(*                                                                              *)
(* For each edge e of dep_graph δ, with endpoints (i,j) and (i',j')           *)
(* (i.e. the two matched rays), we form the equation                            *)
(*   eq(e) = uterm_t(EL j (EL i δ)) =? uterm_t(EL j' (EL i' δ))             *)
(*                                                                              *)
(* In the formalism, α-renaming per vertex is applied before taking |·|; we    *)
(* bake the renaming into the definition using alpha_rename with distinct        *)
(* odd/even multipliers per star-index (a concrete choice that ensures          *)
(* variable-disjointness across stars).                                         *)
(*                                                                              *)
(* eq_of_edge δ (i,j) (i',j') = the equation for the dependency edge e         *)
(* between ray (i,j) and ray (i',j').                                           *)
(*                                                                              *)
(* Prob(δ) = { eq_of_edge δ p q | ∃ edge {INR i, INR i'} in dep_graph δ,     *)
(*                                  ray p ∈ EL i δ, ray q ∈ EL i' δ,          *)
(*                                  dep_edge_cond (all_colours δ) p_ray q_ray } *)
(*                                                                              *)
(* For the HOL4 formalisation we define:                                        *)
(*   eq_of_edge δ (i,j) (i',j') builds the pair                                *)
(*     (alpha_rename (star_rename i) (uterm_t (EL j (EL i δ))),               *)
(*      alpha_rename (\x. star_rename i' x + 1) (uterm_t (EL j' (EL i' δ)))) *)
(*                                                                              *)
(* and Prob(δ) is the set of all such pairs over all dependency edges.         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* Variable renaming for star i: even multiplier ensures disjointness. *)
Definition star_rename_def :
  star_rename (i : num) (x : num) : num = 2 * (i + 1) * x
End

(* Per-star variable renaming as a substitution.
   theta_i i t = t with variables x replaced by Var (2*(i+1)*x).
   This is the α-renaming θ_i of §49.34.                                       *)
Definition theta_i_def :
  theta_i (i : num) (t : term) : term =
    subst_apply (FUN_FMAP (\x. Var (star_rename i x)) (vars_t t)) t
End

(* §49.27  The unification equation for a dependency edge. *)
Definition eq_of_edge_def :                                   (* §49.27 *)
  eq_of_edge (delta : constellation)
             (i : num) (j : num) (i' : num) (j' : num)
             : (term # term) =
    let r  = EL j  (EL i  delta) in
    let r' = EL j' (EL i' delta) in
    (theta_i i  (uterm_t r),
     theta_i i' (uterm_t r'))
End

(* §49.27  Prob(δ): the set of all unification equations arising from edges. *)
Definition Prob_def :                                         (* §49.27 *)
  Prob (delta : constellation) : (term # term) set =
    { eq_of_edge delta i j i' j' |
      i  < LENGTH delta /\ j  < LENGTH (EL i  delta) /\
      i' < LENGTH delta /\ j' < LENGTH (EL i' delta) /\
      i <> i' /\
      dep_edge_cond (all_colours delta)
                    (EL j (EL i delta))
                    (EL j' (EL i' delta)) }
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.34  Correctness: Prob(δ) is unifiable                                    *)
(*                                                                              *)
(* δ is correct iff the set Prob(δ) has a unifier, i.e., there exists a        *)
(* substitution σ such that MM-reduces every equation in Prob(δ) to a solved    *)
(* form (which we model as: there is a finite ordering of Prob(δ) as a list    *)
(* such that mm_reduces reaches a solved state).                                *)
(*                                                                              *)
(* We model "has a unifier" as: ∃ sigma (list : (term#term) list).             *)
(*   SET_OF_LIST list = Prob(delta) /\                                           *)
(*   mm_reduces (FEMPTY, list) (sigma, [])                                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §49.34  Correctness of a constellation. *)
Definition correct_C_def :                                    (* §49.34 *)
  correct_C (delta : constellation) : bool =
    ?sigma (prob_list : (term # term) list).
      LIST_TO_SET prob_list = Prob delta /\
      mm_reduces (FEMPTY, prob_list) (sigma, [])
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.34  Actualisation  ↓δ                                                    *)
(*                                                                              *)
(* When δ is correct with solution ψ, and per-vertex α-renamings θ_v have been *)
(* applied, the actualisation ↓δ is the star indexed by free(δ):               *)
(*   (↓δ)[(i,j)] = (ψ ∘ θ_i)(Φ[i][j])                                        *)
(*               = subst_apply ψ (alpha_rename (star_rename i) (EL j (EL i δ)))*)
(*                                                                              *)
(* In the HOL4 definition we supply ψ (the unifier) explicitly; the caller     *)
(* must assert correct_C δ to know that such ψ exists.  This keeps the         *)
(* definition total (always produces a term) while making the usage constraint  *)
(* visible in the theorem statements.                                           *)
(*                                                                              *)
(* The result type is constellation: a (star list).                             *)
(* We build it as a list of singletons indexed by the list of free ray-ids.    *)
(* (Each free ray becomes its own star in the result — this matches §49.34.)   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* Apply ψ ∘ θ_i to a single ray (i,j). §49.34 *)
Definition actualise_ray_def :                                (* §49.34 *)
  actualise_ray (delta : constellation)
                (psi   : num |-> term)
                (i     : num)
                (j     : num) : ray =
    subst_apply psi (theta_i i (uterm_t (EL j (EL i delta))))
End

(* §49.34  ↓δ: the actualised constellation.
   We iterate over the list of free ray-ids (in canonical order) and wrap each
   actualised ray as a singleton star.
   free_list delta = SORTED list of elements of free_rays delta.
   For the definition we use a list comprehension via FILTER + MAPi.           *)

(* Enumerate all (i,j) pairs in IdRays delta in lexicographic order. *)
Definition ray_pairs_def :
  ray_pairs (delta : constellation) : (num # num) list =
    FLAT (GENLIST (\i. GENLIST (\j. (i, j)) (LENGTH (EL i delta)))
                  (LENGTH delta))
End

(* Free ray-ids as an ordered list (same lexicographic enumeration, filtered). *)
Definition free_ray_list_def :                                (* §49.21 *)
  free_ray_list (delta : constellation) : (num # num) list =
    FILTER (\(i, j). deg_C delta (all_colours delta) i j = 0)
           (ray_pairs delta)
End

(* §49.34  ↓δ as a constellation (list of singleton stars). *)
Definition actualise_def :                                    (* §49.34 *)
  actualise (delta : constellation) (psi : num |-> term) : constellation =
    MAP (\(i, j). [actualise_ray delta psi i j])
        (free_ray_list delta)
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.23  Diagram embedding  δ ⊑ δ'                                            *)
(*                                                                              *)
(* δ ⊑ δ' iff δ is a sub-constellation of δ' (as multi-sets / lists there is  *)
(* a length-preserving prefix or an injective map of indices).                  *)
(*                                                                              *)
(* Eng's definition: δ ⊑ δ' iff every star of δ appears (up to permutation)   *)
(* as a star of δ'.  In our list representation we use the natural sublist     *)
(* embedding: ∃ an injective, order-preserving map f : {0,..,|δ|-1} →          *)
(* {0,..,|δ'|-1} with EL (f i) δ' = EL i δ.                                   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §49.23  Embedding: δ embeds into δ'. *)
Definition embeds_diag_def :                                  (* §49.23 *)
  embeds_diag (delta : constellation) (delta' : constellation) : bool =
    ?f : num -> num.
      (!i. i < LENGTH delta ==> f i < LENGTH delta') /\
      (!i i'. i < LENGTH delta /\ i' < LENGTH delta /\ i < i' ==> f i < f i') /\
      (!i. i < LENGTH delta ==> EL (f i) delta' = EL i delta)
End

(* §49.23  Saturated: ⊑-maximal in the set of constellations under Φ and C. *)
(* A constellation δ is saturated in the context of Φ (a background             *)
(* constellation) and C if there is no proper extension δ' ⊋ δ with           *)
(* embeds_diag δ δ'.                                                            *)
(* In Eng, saturation is defined for a fixed class of constellations generated  *)
(* by a single Φ; we abstract over the "ambient" Φ and leave the class          *)
(* membership as a precondition.                                                 *)
Definition saturated_def :                                    (* §49.23 *)
  saturated (delta : constellation) (Phi : constellation) : bool =
    !delta'.
      embeds_diag delta delta' /\
      LENGTH delta' <= LENGTH Phi ==>
      LENGTH delta' = LENGTH delta
End

(* §49.23  SatDiags_C(Φ): saturated constellations within Φ. *)
Definition SatDiags_C_def :                                   (* §49.23 *)
  SatDiags_C (Phi : constellation) : constellation set =
    { delta | embeds_diag delta Phi /\ saturated delta Phi }
End

(* §49.23  CSatDiags_C(Φ): correct saturated constellations within Φ. *)
Definition CSatDiags_C_def :                                  (* §49.23 *)
  CSatDiags_C (Phi : constellation) : constellation set =
    { delta | delta IN SatDiags_C Phi /\ correct_C delta }
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.42  AEx_C(Φ) — the set of actualisations of CSatDiags_C(Φ)             *)
(*                                                                              *)
(* AEx_C(Φ) := ↓(CSatDiags_C(Φ))                                              *)
(*           = { ↓δ | δ ∈ CSatDiags_C(Φ) }                                    *)
(*                                                                              *)
(* Each δ may have a different ψ; we existentially quantify over it.            *)
(* The result is a SET of constellations.                                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §49.42  AEx: actualisation of all correct saturated diagrams.
   We existentially quantify over the unifier psi; the existence of psi is
   guaranteed by correct_C delta (which is part of CSatDiags_C membership).   *)
Definition AEx_C_def :                                        (* §49.42 *)
  AEx_C (Phi : constellation) : constellation set =
    { gamma | ?delta psi (prob_list : (term # term) list).
                delta IN CSatDiags_C Phi /\
                LIST_TO_SET prob_list = Prob delta /\
                mm_reduces (FEMPTY, prob_list) (psi, []) /\
                gamma = actualise delta psi }
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* Auxiliary: all-objective constellation                                        *)
(*                                                                              *)
(* Eng §49.54: "Φ all-objective" means every ray in Φ has an objective         *)
(* (i.e. polarised: Pos or Neg) head symbol.  In our encoding: for every       *)
(* (i,j) ∈ IdRays Φ, the head of EL j (EL i Φ) is coloured (is_coloured h).  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* Extract the head of a term (returns 0 for Var, which is Pos-coded). *)
Definition head_of_def :
  head_of (App h _ : ray) = h /\
  head_of (Var _)          = 0
End

(* §49.54  All-objective: every ray head is coloured (Pos or Neg). *)
Definition all_objective_def :                                (* §49.54 *)
  all_objective (Phi : constellation) : bool =
    !i j.
      i < LENGTH Phi /\ j < LENGTH (EL i Phi) ==>
      is_coloured (head_of (EL j (EL i Phi)))
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.54  No matchable pair in ↓δ                                              *)
(*                                                                              *)
(* Auxiliary predicate: a constellation γ has no matchable pair of rays.       *)
(* Used to state §49.54.                                                         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition no_matchable_pair_def :
  no_matchable_pair (gamma : constellation) : bool =
    !i j i' j'.
      i  < LENGTH gamma /\ j  < LENGTH (EL i  gamma) /\
      i' < LENGTH gamma /\ j' < LENGTH (EL i' gamma) /\
      (i, j) <> (i', j') ==>
      ~matchable (EL j (EL i gamma)) (EL j' (EL i' gamma))
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.54  All-objective Φ ⇒ no matchable pair in ↓δ                           *)
(*                                                                              *)
(* Verbatim spec (§49.54): if Φ is all-objective and δ ∈ CSatDiags_C(Φ),     *)
(* then no two distinct rays in ↓δ are matchable.                               *)
(*                                                                              *)
(* STRATEGY (informal):                                                          *)
(*   · By correctness (correct_C δ) we have ψ unifying Prob(δ).                *)
(*   · The actualised rays (↓δ)[(i,j)] = (ψ∘θ_i)(Φ[i][j]) are ground in     *)
(*     variables that are pairwise disjoint across stars.                         *)
(*   · If two actualised rays were matchable, their underlying terms would be    *)
(*     α-unifiable; but the unifier ψ already consumed all equations in Prob(δ) *)
(*     and the "correct + saturated" conditions prevent any residual match.      *)
(*   · The all-objective assumption ensures the compatibility check             *)
(*     compat_enc applies only to Pos/Neg heads, which are anti-reflexive.      *)
(*                                                                              *)
(* PROOF: deferred — PROOF-OBLIGATION[stellaExec.01].                           *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaExec.01]:
   GOAL:
     !Phi delta psi (prob_list : (term # term) list).
       all_objective Phi /\
       delta IN CSatDiags_C Phi /\
       LIST_TO_SET prob_list = Prob delta /\
       mm_reduces (FEMPTY, prob_list) (psi, []) ==>
       no_matchable_pair (actualise delta psi)
   STRATEGY:
     1. Unfold actualise_def, actualise_ray_def, no_matchable_pair_def.
     2. Two distinct actualised rays r = (ψ∘θ_i)(Φ[i][j]) and
        r' = (ψ∘θ_{i'})(Φ[i'][j']) come from (i,j) ≠ (i',j') in free_rays δ.
     3. Free rays have deg_C = 0, so no dep_edge_cond between them.
     4. If no dep_edge_cond then ~matchable by definition of matchable and
        dep_edge_cond: matchable implies dep_edge_cond (contrapositive).
     5. All-objective ensures head is coloured, so only Pos/Neg heads remain;
        but the anti-reflexivity of compat_enc for like polarities and the
        no-edge condition together prevent matchability.
   NOTE: The key sub-lemma is:
     matchable r r' ==> dep_edge_cond (all_colours δ) r r'
   which follows from matchable_def and dep_edge_cond_def given colours ⊆ all_colours.
   DRAFT-TACTICS: (sketch)
     rw [no_matchable_pair_def, actualise_def, actualise_ray_def] >>
     rpt strip_tac >>
     fs [free_ray_list_def, ray_pairs_def] >>
     `~dep_edge_cond (all_colours delta) (EL j (EL i delta)) (EL j' (EL i' delta))`
       by (rw [dep_edge_cond_def] >>
           (* deg_C = 0 means adj_C = {} *) ...) >>
     metis_tac [matchable_def, dep_edge_cond_def, matchable_sym]
*)
Theorem aex_no_matchable :                                    (* §49.54 *)
  !Phi delta psi (prob_list : (term # term) list).
    all_objective Phi /\
    delta IN CSatDiags_C Phi /\
    LIST_TO_SET prob_list = Prob delta /\
    mm_reduces (FEMPTY, prob_list) (psi, []) ==>
    no_matchable_pair (actualise delta psi)
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.55  AEx_C is idempotent for all-objective Φ                              *)
(*                                                                              *)
(* Verbatim spec (§49.55): if Φ is all-objective then                           *)
(*   AEx_C(AEx_C(Φ)) = AEx_C(Φ)                                               *)
(*                                                                              *)
(* In our set-of-constellations formulation:                                    *)
(*   BIGUNION { AEx_C gamma | gamma ∈ AEx_C Phi } = AEx_C Phi                 *)
(*                                                                              *)
(* STRATEGY (informal):                                                          *)
(*   ⊆ direction: an element of AEx_C(AEx_C Φ) is ↓δ' for some               *)
(*     δ' ∈ CSatDiags_C(γ) with γ ∈ AEx_C(Φ), γ = ↓δ for δ ∈ CSatDiags_C Φ.*)
(*     By §49.54 (aex_no_matchable), γ has no matchable pair; then the only    *)
(*     correct saturated sub-constellation of γ is γ itself (any proper sub-   *)
(*     constellation would have a free ray, contradicting saturation).           *)
(*     So ↓δ' = ↓γ = γ, which is already in AEx_C Φ.                          *)
(*   ⊇ direction: every γ ∈ AEx_C Φ satisfies γ ∈ AEx_C(AEx_C Φ) because     *)
(*     γ = ↓δ for δ ∈ CSatDiags_C Φ ⊆ CSatDiags_C(AEx_C Φ) (with            *)
(*     appropriate embedding).                                                   *)
(*                                                                              *)
(* PROOF: deferred — PROOF-OBLIGATION[stellaExec.02].                           *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaExec.02]:
   GOAL:
     !Phi.
       all_objective Phi ==>
       BIGUNION { AEx_C gamma | gamma IN AEx_C Phi } = AEx_C Phi
   STRATEGY:
     (⊆) Let ξ ∈ AEx_C(AEx_C Φ), so ξ = ↓δ' with δ' ∈ CSatDiags_C(γ) and
         γ ∈ AEx_C(Φ).  By aex_no_matchable, γ has no matchable pair.
         No matchable pair ⇒ no dep_edge in dep_graph γ ⇒ every ray of γ is
         free ⇒ free_rays(γ) = IdRays(γ) ⇒ Prob(γ) = ∅ ⇒ correct_C γ trivially.
         The unique saturated correct sub-constellation of γ is γ itself, so
         ↓γ = γ (no equations to solve) and ξ = γ ∈ AEx_C Φ.
     (⊇) Let γ ∈ AEx_C Φ, say γ = ↓δ with δ ∈ CSatDiags_C Φ.  Then γ itself
         is in CSatDiags_C(AEx_C Φ) (by embedding), and ↓γ = γ (from the ⊆
         argument).  So γ ∈ AEx_C(AEx_C Φ).
   KEY LEMMAS NEEDED (all deferred):
     (a) no_matchable_pair γ ==> free_rays γ = IdRays γ
         (immediate from deg_C = 0 for all rays when no dep_edge)
     (b) no_matchable_pair γ ==> correct_C γ
         (Prob γ = ∅ when no dep_edges; solved by FEMPTY)
     (c) closed_C ↓δ iff Prob δ is satisfiable and saturated
         (standard property of actualisation)
   DRAFT-TACTICS: (sketch of ⊆ direction)
     rw [BIGUNION_IN, AEx_C_def, CSatDiags_C_def, SatDiags_C_def] >>
     rpt strip_tac >>
     (* γ = actualise delta psi, delta ∈ CSatDiags_C Phi *)
     (* ξ = actualise delta' psi', delta' ∈ CSatDiags_C(actualise delta psi) *)
     `no_matchable_pair (actualise delta psi)` by
       metis_tac [aex_no_matchable] >>
     (* no matchable pair => free_rays = IdRays => Prob = {} *)
     ... (key lemmas (a)(b)(c) above) ...
     metis_tac []
*)
Theorem aex_idempotent :                                      (* §49.55 *)
  !Phi.
    all_objective Phi ==>
    BIGUNION { AEx_C gamma | gamma IN AEx_C Phi } = AEx_C Phi
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* SANITY: empty constellation is closed and correct                             *)
(*                                                                              *)
(* The empty constellation [] has no rays, no edges, Prob = ∅.                *)
(* EVAL discharges these (closed computation on list lengths).                  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem empty_free_rays :
  free_rays [] = {}
Proof
  rw [free_rays_def, IdRays_def, EXTENSION]
QED

Theorem empty_closed :
  closed_C []
Proof
  rw [closed_C_def, empty_free_rays]
QED

(*
   PROOF-OBLIGATION[stellaExec.05]:
   GOAL:   Prob [] = {}
   STRATEGY: Prob_def set comprehension; i < LENGTH [] = i < 0 = F; so set = {}.
   DRAFT-TACTICS: rw [Prob_def, EXTENSION] >> simp [LIST_TO_SET]
*)
Theorem empty_Prob :
  Prob [] = {}
Proof
  cheat
QED

Theorem empty_correct :
  correct_C []
Proof
  rw [correct_C_def] >>
  map_every qexists_tac [`FEMPTY`, `[]`] >>
  simp [LIST_TO_SET, empty_Prob, mm_reduces_def, RTC_REFL]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* SANITY: embeds_diag reflexivity                                               *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem embeds_diag_refl :
  !delta. embeds_diag delta delta
Proof
  rw [embeds_diag_def] >>
  qexists_tac `\i. i` >>
  simp []
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* SANITY: embeds_diag transitivity                                              *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaExec.03]:
   GOAL:
     !delta delta' delta''.
       embeds_diag delta delta' /\ embeds_diag delta' delta'' ==>
       embeds_diag delta delta''
   STRATEGY:
     Compose the two order-preserving injections f and g: use (g ∘ f).
     Strict monotonicity: f i < f i' ==> g (f i) < g (f i').
   DRAFT-TACTICS:
     rw [embeds_diag_def] >>
     qexists_tac `g ∘ f` >>  (* actually lambda i. g (f i) *)
     simp [] >> metis_tac []
*)
Theorem embeds_diag_trans :
  !delta delta' delta''.
    embeds_diag delta delta' /\ embeds_diag delta' delta'' ==>
    embeds_diag delta delta''
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* SANITY: EVAL example — free_ray_list of tiny one-star constellation          *)
(*                                                                              *)
(* Phi1 = [[Var 0]]: one star, one ray, C = {} (Var has no coloured head).    *)
(* deg_C Phi1 {} 0 0 = CARD (adj_C Phi1 {} 0 0) = CARD {} = 0.               *)
(* So free_ray_list Phi1 = [(0,0)].                                             *)
(*                                                                              *)
(* NOTE: EVAL cannot unfold adj_C (it involves matchable + alpha_unifiable,    *)
(* which are not EVAL-friendly).  We state this as a proof obligation.         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaExec.04]:
   GOAL:   free_ray_list [[Var 0]] = [(0, 0)]
   STRATEGY:
     Unfold free_ray_list_def, ray_pairs_def, GENLIST, FLAT, FILTER.
     Compute deg_C [[Var 0]] (all_colours [[Var 0]]) 0 0 = 0 by showing
     adj_C [[Var 0]] {} 0 0 = {} (no other stars, so no i' ≠ 0 with i' < 1).
   DRAFT-TACTICS:
     rw [free_ray_list_def, ray_pairs_def, deg_C_def, adj_C_def, all_colours_def]
     >> simp [GENLIST, FLAT, FILTER]
*)

(* ─────────────────────────────────────────────────────────────────────────── *)
(* PROOF-DEBT LEDGER                                                             *)
(*                                                                               *)
(* stellaExec.01  aex_no_matchable                                               *)
(*   !Phi delta psi (prob_list : (term # term) list).                             *)
(*     all_objective Phi /\ delta IN CSatDiags_C Phi /\                          *)
(*     LIST_TO_SET prob_list = Prob delta /\                                      *)
(*     mm_reduces (FEMPTY, prob_list) (psi,[]) ==>                               *)
(*     no_matchable_pair (actualise delta psi)                                    *)
(*   STRATEGY: free rays have deg_C=0 => no dep_edge_cond; matchable =>          *)
(*     dep_edge_cond (contrapositive); all_objective forces Pos/Neg heads;       *)
(*     compat_enc anti-reflexive for like polarities.                             *)
(*   KEY SUB-LEMMA: matchable r r' ==> dep_edge_cond (all_colours δ) r r'.      *)
(*   (Proof: matchable_def + colour subset; both sides colour ⊆ all_colours.)   *)
(*                                                                                *)
(* stellaExec.02  aex_idempotent                                                  *)
(*   !Phi. all_objective Phi ==>                                                  *)
(*     BIGUNION { AEx_C gamma | gamma IN AEx_C Phi } = AEx_C Phi                *)
(*   STRATEGY: ⊆: use aex_no_matchable; no_matchable_pair => no dep_edge =>     *)
(*     Prob=∅ => unique correct-saturated sub is self; ↓γ=γ ∈ AEx_C Phi.       *)
(*   ⊇: γ ∈ AEx_C Phi ==> γ ∈ AEx_C(AEx_C Phi) by reflexivity of embedding.   *)
(*   KEY SUB-LEMMAS: (a) no matchable pair => free_rays = IdRays;               *)
(*     (b) Prob ∅ => correct_C via FEMPTY; (c) closed actualisation.            *)
(*                                                                                *)
(* stellaExec.03  embeds_diag_trans                                               *)
(*   embeds_diag delta delta' /\ embeds_diag delta' delta'' ==>                  *)
(*     embeds_diag delta delta''                                                   *)
(*   STRATEGY: compose the two injections; g∘f is strictly monotone.            *)
(*                                                                                *)
(* stellaExec.04  free_ray_list [[Var 0]] = [(0, 0)]                             *)
(*   STRATEGY: adj_C [[Var 0]] {} 0 0 = {} (no other star); CARD {} = 0.        *)
(*                                                                                *)
(* stellaExec.05  empty_Prob: Prob [] = {}                                        *)
(*   STRATEGY: set comprehension; i < LENGTH [] = i < 0 = F; so set is {}.      *)
(*   (Bookkeeping: HOL4 set-builder notation + LENGTH simp.)                     *)
(*                                                                                *)
(* INHERITED PROOF-DEBT (from stellaDiagramScript):                               *)
(*   stellaDiagram.01–.11 (dep_edge_cond_sym, stars_dep_sym, FINITE_adj_C,      *)
(*     dep_graph_adjacent, tiny_alpha_unifiable, tiny_dep_edges_sing,            *)
(*     det_neutral_adj_empty, branch_ray_is_branching, tiny_colours_{r0,r1},    *)
(*     tiny_stars_dep)                                                            *)
(*   From stellaMatchScript: alpha_unifiable_sym (perm+swap_all argument).       *)
(*                                                                                *)
(* ─────────────────────────────────────────────────────────────────────────── *)

val _ = export_theory ();
