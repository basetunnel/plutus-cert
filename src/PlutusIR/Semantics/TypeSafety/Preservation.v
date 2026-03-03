Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.
Require Import PlutusCert.PlutusIR.Semantics.Static.Typing.Typing.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.Static.Theorems.UniqueTypes.
Require Import PlutusCert.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.

From PlutusCert Require Import
  PlutusIR
  Util.Tactics
.

Require Import Lists.List.
Import ListNotations.


(* SubstituteT behaves as substituteTCA when substituting closed types *)
Lemma closed__substituteT_CA :
  forall X U T,
    Ty.closed U ->
    substituteTCA X U T = substituteT X U T.
Proof.
(* ADMITTED: Time constraints *)
Admitted.

Require Import Coq.Program.Equality.

(* Term language type preservation of closed terms under evaluation/reduction, ignoring error terms.
   Per issue 92: Not provable. Must be proved up to α-equivalence. See thesis Richard
*)
Theorem eval__type_preservation : forall t T v k,
    nil ,, nil |-+ t : T ->
    t =[k]=> v ->
    (nil ,, nil |-+ v : T \/ is_error v).
Proof.
    intros t T v k Ht Hbs.
    generalize dependent T.
    induction Hbs; intros.
    - (* E_LamAbs *)
      left.
      exact Ht.
    - (* E_Apply *)
      admit.
    - (* E_TyAbs *)
      left.
      exact Ht.
    - (* E_TyInst *)
      admit.
    - (* E_IWrap *)
      admit.
    - (* E_Unwrap *)
      admit.
    - (* E_Constant*)
      left.
      exact Ht.
    - (* E_Constr_nil *)
      left.
      exact Ht.
    - (* E_Constr_cons *)

      admit.
      (* TODO: No typing rules for constr yet*)
    - (* E_Builtin *)
      left.
      exact Ht.
    - (* E_Apply_Builtin_Partial *)
      inversion Ht; subst.
      inversion H0; subst.
      + admit.
      + (* Hmm need some induction *)
        admit.
      + (* Some induction *)
        admit.
    - (* E_TyInst_Builtin_Partial *)
      admit.
    - (* E_Apply_Builtin_Full *)
      admit.
    - (* E_TyInst_Builtin_Full *)
      admit.
    - (* E_Error *)
      left.
      exact Ht.
    - (* E_Error_Apply1 *)

      (* Error rule was changed to allow
        type checking completeness to go through,
        but that does no longer work for
        preservation now.

        Decided in meeting April 16 that we will keep it that way and
        will not care about preservation of errors.
        *)
Admitted.

From PlutusCert Require Import Alpha.Spec.

Import TY.

Axiom ctx_refl_nil : ctx_refl [].

Create HintDb alpha.
Hint Resolve
  alpha_refl
  ctx_refl_nil
: alpha.

(* shorter syntax for ∃T', ... T' /\ T ~ T' *)

Notation "'∃α' T' '~' T , P" := (exists T' : ty, P /\ [] ⊢* T ~ T')
  (at level 200, P at level 0, T at level 0, no associativity).

Import PIRNotations.
Open Scope pir_scope.

Require Import PlutusCert.PlutusIR.Semantics.Static.Typing.Typing.
(*
Theorem type_preservation t T v k :
    t =[k]=> v ->
    [] ,, [] |-+ t : T ->
    is_error v \/ (exists T',
      [] ,, [] |-+ v : T' /\ ty_alpha [] T T').
      *)
Theorem type_preservation t T v k :
    t =[k]=> v ->
    has_type [] [] t T -> (* TODO, has_type and alpha notation collides *)
    is_error v \/ ∃α T' ~ T , (has_type [] [] v T').
Proof with eauto with alpha.
  intros H_eval.
  revert T.
  induction H_eval; intros S H_typing.
  all: try now (right; exists S; split; eauto with alpha).
  all: try now (left; constructor). (* Error cases *)
  all: admit.
Admitted.
