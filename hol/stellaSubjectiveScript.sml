(* stellaSubjectiveScript.sml
   Subjective-ray dynamics: §49.50 new-ray creation (fusion + retained variables),
   §49.52 iterated/hyper execution, and the headline theorem
   subjective ⇒ ¬idempotent (formal "subjective = live", docs/00 §4.4 / 4th convergence).

   ══════════════════════════════════════════════════════════════════════════════
   DESIGN NOTES
   ──────────────────────────────────────────────────────────────────────────────
   REUSED:
     · stellaTermTheory    — term, Var, App, vars_t, subst_apply, is_var
     · stellaPolarisedTheory — polarity, is_coloured, uterm_t, encode_psym,
                               decode_psym, compat_enc
     · stellaMatchTheory   — matchable, mm_reduces
     · stellaDiagramTheory — constellation, ray, star, IdRays, all_colours,
                             is_coloured_def, colours_eqns, dep_edge_cond
     · stellaExecutionTheory — AEx_C, actualise, all_objective, correct_C,
                               aex_idempotent (§49.55 objective reference)

   FRESH (this file):
     · subjective_ray      — §48.7: coloured ray with ≥1 coloured argument
     · animist_star        — §48.10: star containing ≥1 subjective ray
     · has_subjective      — constellation contains ≥1 subjective ray
     · bare_var_rays       — retained bare-variable rays of a star (§49.50)
     · subst_ray           — apply substitution θ to a single ray
     · new_rays_after_fusion — §49.50 structural relation: substitution image
                               of retained bare-variable rays (NOT a new primitive)
     · matchable_frontier  — rays now matchable after substitution (§49.50)
     · AEx_iter            — §49.52 iterated execution (n rounds)
     · hyper_AEx           — §49.52 fixpoint / hyper execution (partial)
     · AEx_proper_time_round — §49.52 one proper-time tick well-defined
     · subj_not_idempotent — §49.57/docs-00-§4.4 headline: subjective ⇒ ¬idempotent

   PROOF POLICY:
     - No new_axiom / mk_thm.
     - Non-trivial proofs: PROOF-OBLIGATION[stellaSubj.NN] comment + cheat.
     - EVAL for closed computations only.
     - Fresh numbering: stellaSubj.01 through stellaSubj.09.

   CITATIONS: §NN.M refers to Eng (Boris Eng, Exegesis of Transcendental Syntax).
              docs/01 = docs/01-subjective-engine-and-valence.md.
   ══════════════════════════════════════════════════════════════════════════════
*)

open HolKernel boolLib bossLib;
open arithmeticTheory pred_setTheory finite_mapTheory listTheory pairTheory
     relationTheory optionTheory;
open stellaTermTheory stellaPolarisedTheory stellaMatchTheory;
open stellaDiagramTheory;
open stellaExecutionTheory;

val _ = new_theory "stellaSubjective";

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §48.7  Subjective ray                                                        *)
(*                                                                             *)
(* Eng §48.7: a ray is *subjective* if its head symbol is coloured (Pos/Neg)  *)
(* AND at least one of its arguments is also coloured (i.e. has a coloured    *)
(* head).  Bare-variable arguments do not count as coloured.                  *)
(*                                                                             *)
(* docs/01 §2.1: "bare `Var` non-matchable means *until substituted to a     *)
(* coloured term*, NOT dropped" — so the structural definition must check     *)
(* argument heads, not merely non-emptiness.                                  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* Is the head of a ray/term coloured?  (reuses stellaDiagram.is_coloured)   *)
Definition ray_head_coloured_def:                              (* §48.7 *)
  ray_head_coloured (t : ray) : bool =
    case t of
      App h _ => is_coloured h
    | Var _   => F
End

(* Does a ray have at least one argument with a coloured head?                *)
Definition has_coloured_arg_def:                               (* §48.7 *)
  has_coloured_arg (t : ray) : bool =
    case t of
      App _ args => EXISTS ray_head_coloured args
    | Var _      => F
End

(* §48.7  Subjective ray: coloured head AND ≥1 coloured argument.            *)
Definition subjective_ray_def:
  subjective_ray (r : ray) =
    (ray_head_coloured r /\ has_coloured_arg r)
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §48.10  Animist star                                                         *)
(*                                                                             *)
(* Eng §48.10: a star is *animist* (subjective) if it contains at least one   *)
(* subjective ray.                                                             *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition animist_star_def:                                   (* §48.10 *)
  animist_star (s : star) : bool =
    EXISTS subjective_ray s
End

(* Convenience: does a constellation contain at least one subjective ray?    *)
Definition has_subjective_def:
  has_subjective (Phi : constellation) : bool =
    EXISTS animist_star Phi
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.50  Retained bare-variable rays                                         *)
(*                                                                             *)
(* docs/01 §2.1 (adjudicated canonical):                                      *)
(* "bare-variable rays are *retained* in stars (never dropped)".              *)
(* A ray is a bare-variable ray if it is exactly  Var x  for some x.         *)
(* After a fusion step applying substitution θ, these retained rays become   *)
(* subst_apply θ (Var x) = the term θ maps x to.  When that image has a      *)
(* coloured head, the ray *enters the matchable frontier*.                    *)
(*                                                                             *)
(* This is NOT a new rule — it is standard substitution on retained rays.    *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* The subset of rays in star s that are bare variables.                     *)
Definition bare_var_rays_def:                                  (* §49.50 *)
  bare_var_rays (s : star) : ray list =
    FILTER is_var s
End

(* Apply a substitution θ (num |-> term) to a single ray.                   *)
Definition subst_ray_def:
  subst_ray (theta : num |-> term) (r : ray) : ray =
    subst_apply theta r
End

(* §49.50  Image of retained bare-variable rays under a fusion substitution. *)
(*                                                                             *)
(* After fusing a subjective ray using substitution θ, each bare-variable    *)
(* ray  Var x  in the same star becomes  θ(Var x) = subst_apply θ (Var x).  *)
(* Those images that have coloured heads become matchable (enter frontier).  *)
(*                                                                             *)
(* This is a DEFINED relation, not a new primitive (docs/01 §2.1).            *)
Definition new_rays_after_fusion_def:                          (* §49.50 *)
  new_rays_after_fusion (theta : num |-> term) (s : star) : ray list =
    MAP (subst_ray theta) (bare_var_rays s)
End

(* §49.50  The matchable frontier after applying θ: those new rays that      *)
(* have a coloured head (thus become matchable with some other ray).          *)
Definition matchable_frontier_def:                             (* §49.50 *)
  matchable_frontier (theta : num |-> term) (s : star) : ray list =
    FILTER ray_head_coloured (new_rays_after_fusion theta s)
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.50  Structural property: fusion on a subjective ray expands the        *)
(* matchable frontier.                                                          *)
(*                                                                             *)
(* Informally: when a subjective ray [−f(+g(X))] fuses with a matching ray  *)
(* [+f(+g(X))], the substitution θ = {X ↦ +g(X)} is applied to the star's   *)
(* retained bare-variable ray [X], yielding [+g(X)], which has coloured head *)
(* and enters the frontier.  This is Eng §49.50's worked example.             *)
(*                                                                             *)
(* PROOF-OBLIGATION[stellaSubj.01]:                                            *)
(* GOAL:                                                                       *)
(*   !s theta.                                                                 *)
(*     animist_star s /\                                                       *)
(*     EXISTS (\r. subjective_ray r /\ matchable r (App _ _)) s /\            *)
(*     mm_reduces (FEMPTY, prob) (theta, []) ==>                               *)
(*     ?r. MEM r (matchable_frontier theta s) /\ ray_head_coloured r          *)
(* STRATEGY:                                                                   *)
(*   Unfold animist_star_def, subjective_ray_def, matchable_frontier_def,     *)
(*   new_rays_after_fusion_def, bare_var_rays_def.                            *)
(*   The subjective ray has a coloured-head argument, say  App c ts.          *)
(*   The fusion substitution θ binds the bare-var rays to the corresponding  *)
(*   terms from the unification — follow Eng §49.50 worked example:           *)
(*   −f(+g(X)) ⋈ +f(+g(X)) ⟹ θ = {X↦+g(X)}: bare ray X ↦ +g(X) is         *)
(*   coloured, enters matchable_frontier.                                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem subjective_fusion_expands_frontier:                    (* §49.50 *)
  !theta s.
    animist_star s /\
    bare_var_rays s <> [] /\
    EXISTS ray_head_coloured (new_rays_after_fusion theta s) ==>
    matchable_frontier theta s <> []
Proof
  (* PROOF-OBLIGATION[stellaSubj.01]: unfold defs; EXISTS + FILTER; direct.  *)
  simp [matchable_frontier_def, new_rays_after_fusion_def, bare_var_rays_def] >>
  rw [] >>
  (* EXISTS ray_head_coloured xs ==> FILTER ray_head_coloured xs <> []       *)
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.52  Iterated execution   AEx^n                                          *)
(*                                                                             *)
(* Eng §49.52:                                                                 *)
(*   AEx^0(Φ)(Ψ)   = Ψ                        (identity on interaction space) *)
(*   AEx^{n+1}(Φ)(Ψ) = AEx(Φ' ++ AEx^n(Φ)(Ψ))                              *)
(*     where Φ' = those stars of Φ whose head ray is matchable with a ray    *)
(*                in AEx^n(Φ)(Ψ)  (the "current matchable stars of Φ")       *)
(*                                                                             *)
(* In our setting Φ = reference constellation (non-linear supply), Ψ = the   *)
(* interaction space.  We model Φ' as the stars of Φ that have a ray         *)
(* matchable with some ray of the current state gamma.                        *)
(*                                                                             *)
(* NOTE: this is an *approximation* adequate for stating the fixpoint         *)
(* properties; the full Layer-1 engine (docs/01 §2) adds lazy supply and     *)
(* semaphore ordering (§49.50, docs/01 §2.1 (2)).                             *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* Stars of Phi matchable with any ray in gamma.                             *)
(* A star s is "Phi-matchable against gamma" if ∃ ray r in s, ∃ ray r' in   *)
(* some star of gamma, such that matchable r r'.                              *)
Definition phi_matchable_stars_def:                            (* §49.52 *)
  phi_matchable_stars (Phi : constellation) (gamma : constellation)
      : constellation =
    FILTER
      (\s. EXISTS (\r.
             EXISTS (\s'. EXISTS (\r'. matchable r r') s') gamma) s)
      Phi
End

(* §49.52  n-fold iterated execution.                                         *)
(*   AEx_iter 0 Phi Psi        = Psi                                          *)
(*   AEx_iter (n+1) Phi Psi                                                   *)
(*     = BIGUNION { AEx_C (phi_matchable_stars Phi gamma ++ gamma)            *)
(*               | gamma IN AEx_iter n Phi Psi }                              *)
(*                                                                             *)
(* We compute a SET of constellations at each step (AEx_C is set-valued).    *)
Definition AEx_iter_def:                                       (* §49.52 *)
  AEx_iter 0 (Phi : constellation) (Psi : constellation)
    = {Psi} /\
  AEx_iter (SUC n) Phi Psi
    = BIGUNION { AEx_C (phi_matchable_stars Phi gamma ++ gamma)
               | gamma IN AEx_iter n Phi Psi }
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.52  Hyper execution — fixpoint when it exists                           *)
(*                                                                             *)
(* Eng §49.52: hyper AEx^∞ := AEx^k when ∃k. AEx^{k+1}(Phi)(Psi) =         *)
(*             AEx^k(Phi)(Psi).  Eng §49.60: it need not exist.              *)
(*                                                                             *)
(* We model it as an option type: SOME when a fixpoint is reached at round k,*)
(* NONE otherwise (open-endedness is the expected subjective regime).         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* Is a fixpoint reached at round k?                                         *)
Definition is_fixpoint_at_def:
  is_fixpoint_at (k : num) (Phi : constellation) (Psi : constellation) =
    (AEx_iter (SUC k) Phi Psi = AEx_iter k Phi Psi)
End

(* hyper_AEx: least fixpoint round, if one exists within bound.              *)
(* (We do not claim termination; this is a search up to an external bound.) *)
Definition hyper_AEx_def:                                      (* §49.52 *)
  hyper_AEx (bound : num) (Phi : constellation) (Psi : constellation)
      : (constellation set) option =
    if is_fixpoint_at bound Phi Psi
    then SOME (AEx_iter bound Phi Psi)
    else NONE
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.52  One proper-time round is well-defined                               *)
(*                                                                             *)
(* docs/01 §2.1 (3) (adjudicated canonical):                                  *)
(* ONE tick of the agent's proper time = one Eng §49.52 iterated-execution   *)
(* round AEx^n → AEx^{n+1} in which the agent's subjective rays cross the   *)
(* agent/environment cut and the reafference cycle closes once.               *)
(*                                                                             *)
(* Here we state the purely structural well-definedness: AEx_iter (n+1) is  *)
(* a well-defined set of constellations given AEx_iter n.  The full          *)
(* reafference-cycle property is a Layer-2 predicate (docs/01 §3).           *)
(*                                                                             *)
(* PROOF-OBLIGATION[stellaSubj.02]:                                            *)
(* GOAL:                                                                       *)
(*   !n Phi Psi.                                                               *)
(*     AEx_iter (SUC n) Phi Psi =                                             *)
(*     BIGUNION { AEx_C (phi_matchable_stars Phi gamma ++ gamma)              *)
(*              | gamma IN AEx_iter n Phi Psi }                               *)
(* STRATEGY: Direct from AEx_iter_def (definitional equality after SUC).     *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem AEx_proper_time_round:                                 (* §49.52 *)
  !n Phi Psi.
    AEx_iter (SUC n) Phi Psi =
    BIGUNION { AEx_C (phi_matchable_stars Phi gamma ++ gamma)
             | gamma IN AEx_iter n Phi Psi }
Proof
  (* PROOF-OBLIGATION[stellaSubj.02]: direct unfolding of AEx_iter_def.     *)
  simp [AEx_iter_def]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.52 / §49.60  Fixpoint may not exist (open-endedness)                   *)
(*                                                                             *)
(* Eng §49.60: the hyper-execution fixpoint need not exist for subjective     *)
(* constellations.  We state this as a non-theorem (we CANNOT prove           *)
(* ∀ bound. hyper_AEx bound Phi Psi = SOME _) — only for the objective       *)
(* fragment does termination follow from §49.55.                              *)
(*                                                                             *)
(* PROOF-OBLIGATION[stellaSubj.03]:                                            *)
(* GOAL:                                                                       *)
(*   ?Phi Psi. !bound. hyper_AEx bound Phi Psi = NONE                        *)
(* STRATEGY:                                                                   *)
(*   Exhibit a subjective constellation Phi (e.g. one with a self-referential *)
(*   matchable-frontier growth) and show AEx_iter (k+1) strictly grows at    *)
(*   every k.  The existence of such a constellation follows from             *)
(*   subjective_fusion_expands_frontier + a fixed-point-free iteration.      *)
(*   Deferring: this is a liveness property requiring a concrete witness.    *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem hyper_AEx_may_not_exist:                               (* §49.60 *)
  ?Phi Psi. !bound. hyper_AEx bound Phi Psi = NONE
Proof
  (* PROOF-OBLIGATION[stellaSubj.03]: exhibit a non-terminating constellation.*)
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* HEADLINE THEOREM: subjective ⇒ ¬idempotent                                  *)
(*                                                                             *)
(* Formal statement of "subjective = live" (docs/00 §4.4 / 4th convergence): *)
(*                                                                             *)
(*   If Phi contains a subjective ray then AEx_C is NOT idempotent:          *)
(*   ¬(AEx_C (BIGUNION { AEx_C gamma | gamma IN AEx_C Phi }) = AEx_C Phi)   *)
(*   (contrast §49.55: all-objective ⇒ idempotent).                          *)
(*                                                                             *)
(* More precisely:                                                             *)
(*   has_subjective Phi ==>                                                   *)
(*   ?(gamma : constellation).                                                *)
(*     gamma IN AEx_C Phi /\                                                  *)
(*     BIGUNION { AEx_C gamma' | gamma' IN AEx_C Phi } ≠ AEx_C Phi          *)
(*                                                                             *)
(* This is the formal inversion of aex_idempotent (§49.55), making           *)
(* non-idempotence the *definition* of the live/subjective regime.            *)
(*                                                                             *)
(* PROOF-OBLIGATION[stellaSubj.04]:                                            *)
(* GOAL:                                                                       *)
(*   !Phi.                                                                     *)
(*     has_subjective Phi ==>                                                  *)
(*     BIGUNION { AEx_C gamma | gamma IN AEx_C Phi } <> AEx_C Phi            *)
(* STRATEGY:                                                                   *)
(*   1. By subjective_fusion_expands_frontier, there exists a star s ∈ Phi   *)
(*      and substitution theta s.t. matchable_frontier theta s ≠ [].          *)
(*   2. This frontier ray r is in AEx_C Phi but NOT in the image of AEx_C    *)
(*      applied a second time to AEx_C Phi (because r was produced by the    *)
(*      subjective fusion substitution and it introduces a new matchable pair *)
(*      that AEx_C Phi itself did not yet contain).                            *)
(*   3. Therefore AEx_C (AEx_C Phi) strictly extends AEx_C Phi.              *)
(*   Key sub-lemma: let gamma0 ∈ AEx_C Phi contain the freshly created ray r;*)
(*   then AEx_C gamma0 ≠ gamma0  (r is still matchable within gamma0).       *)
(*   This contradicts idempotence if r is coloured.                           *)
(*   Formalising requires connecting matchable_frontier to the AEx_C witness  *)
(*   constellation — full proof deferred.                                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem subj_not_idempotent:                                   (* §49.57 / docs/00 §4.4 *)
  !Phi.
    has_subjective Phi ==>
    BIGUNION { AEx_C gamma | gamma IN AEx_C Phi } <> AEx_C Phi
Proof
  (* PROOF-OBLIGATION[stellaSubj.04]:
     GOAL: has_subjective Phi ==>
           BIGUNION {AEx_C g | g IN AEx_C Phi} ≠ AEx_C Phi
     STRATEGY:
       Via subjective_fusion_expands_frontier: a fusion step strictly extends
       the matchable frontier, so a second AEx_C application finds new edges
       and produces at least one new actualisation not present in AEx_C Phi.
       Formally: exhibit a g ∈ AEx_C Phi and a gamma' ∈ AEx_C g
       such that gamma' ∉ AEx_C Phi.  Requires a concrete witness from the
       subjective_ray + animist_star structure.
  *)
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* Corollary: contrapositive of §49.55 idempotence                            *)
(*                                                                             *)
(* aex_idempotent (stellaExecution): all_objective ==> idempotent.            *)
(* subj_not_idempotent (this file):  has_subjective ==> ¬idempotent.         *)
(*                                                                             *)
(* Together they bracket the alive/dead divide at the HOL4 level.             *)
(*                                                                             *)
(* PROOF-OBLIGATION[stellaSubj.05]:                                            *)
(* GOAL:                                                                       *)
(*   !Phi.                                                                     *)
(*     has_subjective Phi /\ all_objective Phi ==> F                          *)
(* STRATEGY:                                                                   *)
(*   has_subjective gives a ray with coloured head AND coloured arg.          *)
(*   all_objective says every ray has coloured head; the two are compatible.  *)
(*   BUT a subjective ray also has a coloured argument, which by unfolding    *)
(*   subjective_ray_def is has_coloured_arg — this is consistent with         *)
(*   all_objective.  Hence they are NOT mutually exclusive in general.        *)
(*   The live/dead *dynamics* (not the syntactic predicates alone) diverge.  *)
(*   The corollary is stated as a consistency lemma only.                     *)
(*                                                                             *)
(* NOTE: The predicates all_objective and has_subjective are orthogonal       *)
(* (a constellation can satisfy both).  The dynamical divergence is           *)
(* captured by subj_not_idempotent vs aex_idempotent (the real theorem pair). *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* Consistency: a constellation may satisfy both; no contradiction.          *)
Theorem subj_and_obj_consistent:
  ?Phi. has_subjective Phi /\ all_objective Phi
Proof
  (* PROOF-OBLIGATION[stellaSubj.05]:
     Exhibit a constellation with a ray App(Pos,n)[App(Pos,m)[]]:
       - head is coloured (Pos,n) => all_objective satisfied for this ray
       - argument App(Pos,m)[] has coloured head => subjective_ray holds
     Single-star singleton constellation.
  *)
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.52  AEx_iter 0 = identity                                               *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem AEx_iter_zero:                                         (* §49.52 *)
  !Phi Psi. AEx_iter 0 Phi Psi = {Psi}
Proof
  simp [AEx_iter_def]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.52  Monotonicity of AEx_iter: the set of reachable states grows        *)
(*                                                                             *)
(* PROOF-OBLIGATION[stellaSubj.06]:                                            *)
(* GOAL:                                                                       *)
(*   !n Phi Psi.                                                               *)
(*     AEx_iter n Phi Psi SUBSET AEx_iter (SUC n) Phi Psi \/                 *)
(*     AEx_iter (SUC n) Phi Psi SUBSET AEx_iter n Phi Psi                    *)
(*     (neither direction holds in general; the iteration is not monotone     *)
(*      without additional hypotheses — this is the non-termination heart)    *)
(* NOTE: We state only that the step is well-typed; monotonicity is not       *)
(* asserted (it fails for subjective constellations — that IS §49.60).        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem AEx_iter_step_welltyped:
  !n Phi Psi.
    AEx_iter (SUC n) Phi Psi =
    BIGUNION { AEx_C (phi_matchable_stars Phi gamma ++ gamma)
             | gamma IN AEx_iter n Phi Psi }
Proof
  simp [AEx_iter_def]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.50  Substitution on retained bare-variable rays is standard subst      *)
(*                                                                             *)
(* Sanity: subst_ray theta (Var x) = subst_apply theta (Var x).              *)
(* This confirms new_rays_after_fusion is definitionally standard substitution*)
(* (not a new semantic primitive).                                            *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem subst_ray_var:                                         (* §49.50 *)
  !theta x. subst_ray theta (Var x) = subst_apply theta (Var x)
Proof
  simp [subst_ray_def]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* EVAL sanity: bare_var_rays of a bare-variable star                         *)
(*                                                                             *)
(* bare_var_rays [Var 0; Var 1] = [Var 0; Var 1]                             *)
(* (EVAL discharges this — closed computation on concrete lists + is_var.)   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem eval_bare_var_rays_example:
  bare_var_rays [Var 0; Var 1] = [Var 0; Var 1]
Proof
  EVAL_TAC
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* EVAL sanity: subjective_ray on a concrete ray                               *)
(*                                                                             *)
(* The ray  App (encode_psym (Pos,0)) [App (encode_psym (Pos,1)) []]         *)
(* has coloured head (Pos,0) and coloured argument (Pos,1) => subjective.     *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem eval_subjective_ray_example:
  subjective_ray
    (App (encode_psym (Pos, 0)) [App (encode_psym (Pos, 1)) []])
  = T
Proof
  EVAL_TAC
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* EVAL sanity: animist_star on a concrete star                                *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem eval_animist_star_example:
  animist_star
    [App (encode_psym (Pos, 0)) [App (encode_psym (Neg, 0)) []]]
  = T
Proof
  EVAL_TAC
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* EVAL sanity: a pure bare-variable ray is NOT subjective                    *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem eval_var_not_subjective:
  subjective_ray (Var 0) = F
Proof
  EVAL_TAC
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* EVAL sanity: AEx_iter 0                                                     *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem eval_AEx_iter_zero_example:
  AEx_iter 0 [] [] = {[]}
Proof
  EVAL_TAC
QED

(* ════════════════════════════════════════════════════════════════════════════ *)
(*  PROOF-OBLIGATION LEDGER                                                     *)
(*  (end-of-file; all non-trivial proofs are deferred here)                   *)
(*  ────────────────────────────────────────────────────────────────────────── *)
(*                                                                             *)
(*  stellaSubj.01  subjective_fusion_expands_frontier                         *)
(*    GOAL: animist_star s /\ bare_var_rays s ≠ [] /\                        *)
(*          EXISTS ray_head_coloured (new_rays_after_fusion theta s) ==>      *)
(*          matchable_frontier theta s ≠ []                                   *)
(*    STRATEGY: EXISTS + FILTER; follows from EXISTS_FILTER or a hand-case.  *)
(*    BLOCKED-ON: —                                                            *)
(*                                                                             *)
(*  stellaSubj.02  AEx_proper_time_round                                      *)
(*    GOAL: AEx_iter (SUC n) Phi Psi = BIGUNION {...}                         *)
(*    STRATEGY: direct from AEx_iter_def; DISCHARGED by simp.                *)
(*    BLOCKED-ON: —                                                            *)
(*                                                                             *)
(*  stellaSubj.03  hyper_AEx_may_not_exist                                    *)
(*    GOAL: ?Phi Psi. !bound. hyper_AEx bound Phi Psi = NONE                 *)
(*    STRATEGY: exhibit a non-terminating subjective constellation.           *)
(*    BLOCKED-ON: stellaSubj.04 (need the non-idempotent witness first).      *)
(*                                                                             *)
(*  stellaSubj.04  subj_not_idempotent  (HEADLINE)                            *)
(*    GOAL: has_subjective Phi ==>                                            *)
(*          BIGUNION {AEx_C g | g IN AEx_C Phi} ≠ AEx_C Phi                  *)
(*    STRATEGY: subjective fusion expands frontier; second AEx_C finds new   *)
(*              edges; exhibit gamma' ∈ AEx_C g with gamma' ∉ AEx_C Phi.    *)
(*    BLOCKED-ON: stellaSubj.01 + concrete witness + AEx_C monotone lemma.   *)
(*                                                                             *)
(*  stellaSubj.05  subj_and_obj_consistent                                    *)
(*    GOAL: ?Phi. has_subjective Phi /\ all_objective Phi                    *)
(*    STRATEGY: exhibit App(Pos,n)[App(Pos,m)[]] as single-ray constellation.*)
(*    BLOCKED-ON: —                                                            *)
(*                                                                             *)
(*  stellaSubj.06  (non-)monotonicity of AEx_iter — NOT STATED AS THEOREM   *)
(*    NOTE: non-monotonicity is the §49.60 open-endedness; stated in prose.  *)
(*                                                                             *)
(*  stellaSubj.07 – stellaSubj.09: reserved for future Layer-1b obligations. *)
(*                                                                             *)
(*  EVAL proofs (NOT debt — closed computations fully discharged):           *)
(*    eval_bare_var_rays_example     [Var 0; Var 1]   => [Var 0; Var 1]      *)
(*    eval_subjective_ray_example    App(Pos,0)[App(Pos,1)[]] => T            *)
(*    eval_animist_star_example      star with subjective ray => T            *)
(*    eval_var_not_subjective        Var 0 => F                               *)
(*    eval_AEx_iter_zero_example     AEx_iter 0 [] [] = {[]}                 *)
(*                                                                             *)
(*  TOTAL cheats: 4  (stellaSubj.01, .03, .04, .05)                          *)
(*  TOTAL EVAL:   5  (fully discharged, no debt)                              *)
(*  new_axiom / mk_thm: 0                                                     *)
(* ════════════════════════════════════════════════════════════════════════════ *)

val _ = export_theory ();
