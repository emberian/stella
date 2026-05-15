(* stellaTermScript.sml
   First-order terms over a signature (Eng §B.1.2–§B.1.8).

   REUSE: finite_mapTheory (FEMPTY, FUPDATE, FAPPLY, FDOM, SUBMAP),
          pred_setTheory (BIGUNION, FINITE, UNION), listTheory.
   The HOL4 triangular-unification term type is binary; Eng's is n-ary.
   We define a fresh n-ary term type and re-prove only what is needed here.
*)

open HolKernel boolLib bossLib;
open arithmeticTheory pred_setTheory finite_mapTheory listTheory;

val _ = new_theory "stellaTerm";

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §B.1.4  First-order terms                                                   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Datatype:
  term = Var num              (* variable X ∈ V *)
       | App num (term list)  (* f(t₁,…,tₙ) *)
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §B.1.5  Variable set  vars(t)                                               *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* Use Hol_defn for a mutually-recursive (term # term list) definition.
   HOL4 recognises this as structurally recursive; no termination condition
   is generated.  We extract the equations and induction theorem manually.   *)

val vars_defn = Hol_defn "vars_t" `
  (vars_t (Var x)      = {x}) /\
  (vars_t (App _ ts)   = vars_l ts) /\
  (vars_l []           = {}) /\
  (vars_l (t :: ts)    = vars_t t UNION vars_l ts)`;

val vars_def = LIST_CONJ (Defn.eqns_of vars_defn);
val vars_ind = Option.valOf (Defn.ind_of vars_defn);

val _ = save_thm ("vars_def", vars_def);
val _ = save_thm ("vars_ind", vars_ind);

Theorem FINITE_vars_t[simp]:
  (!t : term. FINITE (vars_t t)) /\
  (!ts : term list. FINITE (vars_l ts))
Proof
  HO_MATCH_MP_TAC vars_ind >> simp [vars_def]
QED

val FINITE_vars = save_thm ("FINITE_vars", CONJUNCT1 FINITE_vars_t);
val FINITE_vars_l = save_thm ("FINITE_vars_l", CONJUNCT2 FINITE_vars_t);

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §B.1.7  Substitutions — finite maps  num |-> term                          *)
(*                                                                             *)
(* REUSE: finite_mapTheory (FEMPTY, FUPDATE, FAPPLY, FDOM, SUBMAP, etc.)      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

val subst_defn = Hol_defn "subst_apply" `
  (subst_apply theta (Var x) =
     if x IN FDOM theta then theta ' x else Var x) /\
  (subst_apply theta (App f ts) =
     App f (subst_l theta ts)) /\
  (subst_l theta []       = []) /\
  (subst_l theta (t :: ts) = subst_apply theta t :: subst_l theta ts)`;

val subst_def = LIST_CONJ (Defn.eqns_of subst_defn);
val subst_ind = Option.valOf (Defn.ind_of subst_defn);

val _ = save_thm ("subst_def", subst_def);
val _ = save_thm ("subst_ind", subst_ind);

Theorem subst_apply_empty[simp]:
  (!t : term.  subst_apply FEMPTY t  = t) /\
  (!ts : term list. subst_l FEMPTY ts = ts)
Proof
  HO_MATCH_MP_TAC subst_ind >> simp [subst_def, FDOM_FEMPTY]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* Structural predicates                                                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition is_var_def[simp]:
  is_var (Var _)   = T /\
  is_var (App _ _) = F
End

val _ = export_theory();
