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
  - (* Apply *)
    inversion H_typing; subst.

    repeat match goal with
    | IH : (forall _, has_type _ _ ?t _ -> _),
      H_ty : has_type _ _ ?t _ |- _
      => specialize (IH _ H_ty); clear H_ty
    end.

    repeat match goal with
    | IH : (is_error _ \/ _) |- _ =>
        destruct IH as [H_err | IH];
        try now inversion H_err
    end.

    destruct_hypos.

    match goal with
    | H : has_type [] [] (λ x T t0) x1 |- _ => inversion H; subst
    end.

    assert (H_ty_subst : (has_type [] [] (subst x v2 t0) T2n))
      by admit. (* subst preserves typing *)

    specialize (IHH_eval3 T2n H_ty_subst).
    destruct IHH_eval3; try auto.
    right.
    destruct H4 as [T_subst [H_T_subst H_alpha]].
    eexists.
    split.
    eassumption.

    assert (H_S_T2n : [] ⊢* S ~ T2n) by admit. (* Follows from Ty_Fun ~ Ty_Fun ... *)

    eapply alpha_trans.
    2: eassumption.
    2: eassumption.
    constructor.
  - (* TyInst *)
    inversion H_typing; subst.


    repeat match goal with
    | IH : (forall _, has_type _ _ ?t _ -> _),
      H_ty : has_type _ _ ?t _ |- _ => specialize (IH _ H_ty); clear H_ty
    end.
    repeat match goal with
    | IH : (is_error _ \/ _) |- _ =>
        destruct IH as [H_err | IH];
        try now inversion H_err
    end.

    destruct IHH_eval1 as [T_Λ [H_typing_Λ H_alpha_Λ]].
    inversion H_typing_Λ; subst.

    admit.

  - (* IWrap *)
    admit.
  - (* Unwrap *)
    admit.
  - (* Built-in Apply *)
    admit.
  - (* Built-in TyInst *)
    admit.
  - (* Built-in saturated Apply *)
    admit.
  - (* Let NonRec *)
    (* Need IH over eval_bindings_nonrec *)
    admit.
  - (* Let Rec *)
    (* Need IH over eval_bindings_nonrec *)
    admit.
  - (* DatatypeBind *)
    inversion H_typing; subst.
    admit.
Admitted.
