Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.

Require Import PlutusCert.PlutusIR.Transform.DeadCode.Spec2.
Require Import PlutusCert.PlutusIR.Transform.DeadCode.SSP.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Analysis.BoundVars.
Require Import PlutusCert.PlutusIR.Analysis.Purity.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.


Import PlutusNotations.


(** ** The main theorem *)

Definition P_dc t t' :=
    forall Δ Γ T,
    Δ ,, Γ |-+ t : T ->
    LR_logically_approximate Δ Γ t t' T.

Definition P_dc_NonRec t' bs bs' :=
    forall Δ Γ T,
    Δ ,, Γ |-oks_nr bs ->
    forall t Γ_bs Γ_t Δ_t,
    Δ_t = flatten (List.map binds_Delta bs) ++ Δ  ->
    map_normalise (flatten (List.map binds_Gamma bs)) Γ_bs ->
    Γ_t = Γ_bs ++ Γ ->
    LR_logically_approximate Δ_t Γ_t t t' T ->
    LR_logically_approximate Δ Γ (Let NonRec bs t) (Let NonRec bs' t') T
.

Definition P_dc_Rec (bs'0 : list binding) t' bs bs' :=
    (* Note: perhaps bs'0 will be necessary here, e.g. something like
         exists bs'', bs'0 = bs'' ++ bs'
    *)
    forall Δ Γ T,
    Δ ,, Γ |-oks_r bs ->
    forall t,
    LR_logically_approximate Δ Γ t t' T ->
    LR_logically_approximate Δ Γ (Let Rec bs t) (Let Rec bs' t') T.

(* Add as general lemma in Static.Typing *)
Lemma let_nonrec_inv : forall {Δ Γ b bs},
  Δ ,, Γ |-oks_nr (b :: bs)->
  exists Γ_b,
  map_normalise (binds_Gamma b) Γ_b /\
  (((binds_Delta b) ++ Δ) ,, (Γ_b ++ Γ) |-oks_nr bs)
.
Admitted.

Notation "'[' γ ; ρ ']' t" := (msubst γ (msubstA ρ t)) (at level 10).
Notation "'[' γ ; ρ ']_bnr' t" := (msubst_bnr γ (msubstA_bnr ρ t)) (at level 10).
Notation "'[' γ ; ρ ']_b' t" := (msubst_b γ (msubstA_b ρ t)) (at level 10).

Lemma elim_nonrec_approx : forall Δ Γ b bs t T t' Γ_b,
  disjoint (bvb b) (fv t') ->
  disjoint (btvb b) (Term.ftv t') ->
  map_normalise (binds_Gamma b) Γ_b ->
  binds_Delta b ++ Δ,, Γ_b ++ Γ |- (Let NonRec       bs  t) ≤ t' : T ->
  Δ                 ,, Γ        |- (Let NonRec (b :: bs) t) ≤ t' : T.
Proof.
  intros.
  unfold LR_logically_approximate.
  repeat split.
  1,2:  admit. (* Typing *)

  setoid_rewrite RV_RC.
  intros.


  (* Push substitutions in *)
  rewrite msubstA_LetNonRec
        , msubst_LetNonRec
        , msubstA_BindingsNonRec_cons
        , msubst_bnr_cons
  in H5.
  inversion H5; subst. clear H5.
  destruct b.

  - destruct v.

    (* Push subistutitions further in *)
    rewrite msubstA_TermBind
          , msubst_TermBind
    in H10.
    inversion H10; subst. clear H10.


    + (* E_Let_TermBind *)
      Set Diffs "on".

      rewrite btvbs_cons in H17.
      unfold btvb in H17.
      rewrite app_nil_l in H17.
      (* Pull substitutions out *)
      rewrite <- msubst_LetNonRec in H17.
      rewrite <- msubstA_LetNonRec in H17.

      (* Simplify disjoint assumptions *)
      simpl in H0, H.
      unfold disjoint in *.
      apply Forall_inv in H.
      clear H0.
      simpl in H2.
      admit.


    + (* E_Error_Let_Termbind*)
      admit.

  - (* TypeBind *)
    admit.

  - (* DatatypeBind *)
    admit.
Admitted.

Lemma has_type_NonRec_nil : forall Δ Γ t T,
  Δ,, Γ |-+ (Let NonRec nil t) : T ->
  Δ,, Γ |-+ t : T.
Admitted.


Theorem dc__approx : forall t t',
    dc t t' ->
    P_dc t t'.
Proof.
  apply dc__multind with (P := P_dc) (P0 := P_dc_NonRec) (P1 := P_dc_Rec).

  - (* Var *)
    admit.
    (* TODO: compatibility lemmas *)
  - (* TyAbs *)
    admit.
  - (* LamAbs *)
    admit.
  - (* Apply *)
    admit.
  - (* Constant *)
    admit.
  - (* Builtin *)
    admit.
  - (* TyInst *)
    admit.
  - (* Error *)
    admit.
  - (* IWrap *)
    admit.
  - (* Unwrap *)
    admit.
  - (* Constr nil *)
    admit.
  - (* Constr cons *)
    admit.
  - (* Case nil *)
    admit.
  - (* Case cons *)
    admit.


  - (* dc_Let_NonRec *)
    admit.

  - (* dc_Let_Rec *)
    admit.

  - (* dc_NonRec_elim *)
    intros.
    unfold P_dc_NonRec in *.
    intros.
    rename Γ_bs into Γ_bbs.
    inversion H0; subst.

    unfold flatten in H2.
    simpl in H2.
    rewrite concat_app in H2.
    apply map_normalise__app in H2 as [Γ_bs [Γ_b [H_mapnorm_b [H_mapnorm_bs H_eq]]]].
    simpl in H_mapnorm_bs. rewrite app_nil_r in H_mapnorm_bs.

    pose proof (map_normalise__deterministic _ _ _ H_mapnorm_bs H10); subst.

    apply H with
      (t := t) (T := T)
      (Δ := binds_Delta b ++ Δ) (Γ := bsGn ++ Γ)
      (Γ_bs := Γ_bs)
      in H4.
    destruct H_unused as [ H_unused_bvb H_unused_btvb ].
    eauto using elim_nonrec_approx.
    all: try assumption.
    + rewrite flatten_app, app_assoc. reflexivity.
    + rewrite app_assoc. reflexivity.

   - (* dc_NonRec_keep *)
    admit.

  - (* dc_NonRec_nil *)
    intros.
    unfold P_dc_NonRec in *.
    intros Δ Γ T H_ty.
    admit.
    (*
    apply has_type_NonRec_nil in H_ty.
    eauto using compat_nil.
    *)

  - (* dc_Rec_elim *)
    admit.

  - (* dc_Rec_keep *)
    admit.

  (* dc_Rec_nil *)
Admitted.

Definition P_dc_rev t t' :=
    forall Δ Γ T,
    Δ ,, Γ |-+ t : T ->
    LR_logically_approximate Δ Γ t' t T.

Lemma elim_nonrec_approx_rev : forall Δ Γ b bs t T t' Γ_b,
  disjoint (bvb b) (fv t') ->
  disjoint (btvb b) (Term.ftv t') ->
  pure_binding nil b ->
  map_normalise (binds_Gamma b) Γ_b ->
  binds_Delta b ++ Δ,, Γ_b ++ Γ |- t' ≤ (Let NonRec       bs  t)  : T ->
  Δ                 ,, Γ        |- t' ≤ (Let NonRec (b :: bs) t)  : T.
Admitted.

Theorem dc__approx_rev : forall t t',
    dc t t' ->
    P_dc_rev t t'.
Proof.
Admitted.


Corollary dc__logical_equiv Δ Γ t t' T:
  dc t t' ->
  LR_logically_equivalent Δ Γ t t' T.
Admitted.
