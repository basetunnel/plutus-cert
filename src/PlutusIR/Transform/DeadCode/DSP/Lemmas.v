From Coq Require Import
  List
  Strings.String
  Lia
  Program.Equality
.

Require Import PlutusCert.PlutusIR.Transform.DeadCode.Spec3.
From PlutusCert Require Import Semantics.Dynamic.
From PlutusCert Require Import Semantics.Static.
From PlutusCert Require Import Analysis.WellScoped.
From PlutusCert Require Import Analysis.NoShadow.
From PlutusCert Require Import TypeSafety.TypeLanguage.Preservation.
From PlutusCert Require Import SemanticEquivalence.LogicalRelation.
From PlutusCert Require Import FreeVars.
From PlutusCert Require Import Purity.
From PlutusCert Require Import Substitution.Free.
From PlutusCert Require Import Util.List.

Import ListNotations.
Import Utf8_core.

Import FreeVars.Term.



Section TypingHelpers.

  Lemma lookup_app_r {A} k (v : A) xs xs' :
    lookup k xs = Some v -> lookup k (xs ++ xs') = Some v.
  Proof.
  Admitted.

  Lemma lookup_app {A} k (v : A) xs xs' :
    lookup k (xs ++ xs') = Some v ->
    lookup k xs = Some v \/ lookup k xs' = Some v.
  Proof.
  Admitted.

  Definition P_has_type Δ Γ t T :=
    forall Γ1 Γ2 x Tx,
      ~ In x (fv t) ->
      Γ = Γ1 ++ (x, Tx) :: Γ2 ->
      Δ,, (Γ1 ++ Γ2) |-+ t : T.

  Definition P_bindings_well_formed_nonrec Δ Γ bs :=
    forall Γ1 Γ2 x Tx,
      ~ In x (fvbs fvb NonRec bs) ->
      Γ = Γ1 ++ (x, Tx) :: Γ2 ->
      Δ,, (Γ1 ++ Γ2) |-oks_nr bs.

  Definition P_bindings_well_formed_rec Δ Γ bs :=
    forall Γ1 Γ2 x Tx,
      ~ In x (fvbs fvb NonRec bs) ->
      Γ = Γ1 ++ (x, Tx) :: Γ2 ->
      Δ,, (Γ1 ++ Γ2) |-oks_r bs.

  Definition P_binding_well_formed Δ Γ rec b :=
    forall Γ1 Γ2 x Tx,
      ~ In x (fvb NonRec b) ->
      Γ = Γ1 ++ (x, Tx) :: Γ2 ->
      Δ,, (Γ1 ++ Γ2) |-ok_b rec # b.

  From PlutusCert Require Import Static.Typing.Typing.
  Lemma strengthen_Γ Δ Γ t T :
    has_type Δ Γ t T ->
    forall Γ1 Γ2 x Tx,
      ~ In x (fv t) ->
      Γ = Γ1 ++ (x, Tx) :: Γ2 ->
      Δ,, (Γ1 ++ Γ2) |-+ t : T.
  Proof.
    apply (has_type__multind
      P_has_type
      constructor_well_formed
      P_bindings_well_formed_nonrec
      P_bindings_well_formed_rec
      P_binding_well_formed).

    - (* Var *)
      unfold P_has_type.
      intros.
      subst.
  Admitted.

  (* Specialized version of strengthen_Γ *)
  Lemma strengthen_Γ_cons Δ Γ t T x Tx :
    ~ In x (fv t) ->
    Δ,, (x, Tx) :: Γ |-+ t : T ->
    Δ,, Γ |-+ t : T.
  Proof.
    intros.
    apply strengthen_Γ with (Γ := (x, Tx) :: Γ) (Γ1 := []) (Γ2 := Γ) (x := x) (Tx := Tx).
    all: auto.
  Qed.

End TypingHelpers.

Section SubstitutionLemmas.


  Lemma msubst_not_in_fv x t' γ t :
    x ∉ fv t ->
    msubst ((x, t') :: γ) t = msubst γ t.
  Proof.
  Admitted.

  (* Substituting type annotations will not change free term variables*)
  Lemma fv_msubstA_fv ρ t :
    fv (msubstA ρ t) = fv t.
  Proof.
  Admitted.


  Import PlutusNotations.

  Lemma compose_subst_msubst : forall x tx γ t,
    subst x tx (msubst γ t) = msubst ((x, tx) :: γ) t.
  Proof. Admitted.

  Lemma compose_subst_msubst_bindings_nonrec : forall x tx γ bs,
    <{ [ x := tx ]bnr ([γ]*bnr bs) }> = <{ [(x, tx) :: γ]*bnr bs }>.
  Proof. Admitted.

  Lemma result_msubstA_result v δ :
    result v ->
    result <{ :[ δ ]* v}>.
  Proof.
  (** Should hold: only substitutes in types *)
  Admitted.


  Lemma result_msubst_result v γ :
    result v ->
    result <{[γ]* v}>.
  Proof.
  (** Should hold: only substitute under lambdas etc *)
  Admitted.


End SubstitutionLemmas.

Section ScopingLemmas.

  Lemma well_scoped_bindings_Rec__Forall Δ Γ bs :
    Δ,, Γ |-ws_oks_r bs ->
    Forall (fun b => Δ ,, Γ |-ws_ok_b b) bs.
  Proof.
    intros H_ws.
    dependent induction H_ws.
    all: auto using Forall.
  Qed.



  Lemma append_distr_remove_many xs ys zs :
    (xs ++ ys) \ zs = (xs \ zs) ++ (ys \ zs).
  Proof.
  Admitted.

  Lemma remove_assoc xs ys zs :
    (xs \ ys) \ zs = xs \ (ys ++ zs).
  Proof.
  Admitted.

  Lemma remove_swap xs ys zs :
    (xs \ ys) \ zs = (xs \ zs) \ ys.
  Proof.
  Admitted.

  Lemma remove_idemp xs ys :
    (xs \ ys) \ ys = xs \ ys.
  Proof.
  Admitted.

  Lemma remove_many_nil xs :
    [] \ xs = [].
  Proof.
    induction xs.
    all: simpl; try rewrite IHxs; auto.
  Qed.


  (* Convenient *)
  Lemma fv_bindings_eq bs :
    fv_bindings Rec bs = List.concat (map (fvb Rec) bs) \ (bvbs bs).
  Proof.
    unfold fv_bindings.
    (* generalize (bvbs bs) as bvbs_bs.*)
    induction bs as [ | b bs].
    - simpl. reflexivity.
    -
    simpl.
    setoid_rewrite append_distr_remove_many.
    f_equal.
    rewrite IHbs.
    setoid_rewrite bvbs_cons.
    rewrite remove_swap.
    rewrite remove_assoc.
    rewrite <- app_assoc.
    setoid_rewrite <- remove_assoc.
    rewrite <- remove_assoc.
    rewrite remove_idemp.
    reflexivity.
  Qed.

  Lemma fv_binding_Rec__fv_bindings_Rec bs Γ :
    Forall (fun b => (fv_binding Rec b) \ (bvbs bs) ⊆ Γ) bs ->
    fv_bindings Rec bs ⊆ Γ.
  Proof.
    intros H_bs.
    unfold fv_bindings.
    rewrite fv_bindings_eq.
    revert H_bs.
    (* Generalize (bvbs bs) so it stays constant in the IH *)
    generalize (bvbs bs).
    intros vars H_bs.
    induction bs; simpl.
    - rewrite remove_many_empty.
      apply empty_subset.
    - inversion H_bs. subst.
      rewrite remove_many_app.
      apply subset_append.
      + assumption.
      + auto.
  Qed.

  Ltac simpl_fvb :=
      unfold fv_binding; rewrite Term.fvb_equation
    .

  Ltac use_IH :=
      intros;
      rewrite fv_equation;
      inversion H_ws; subst;
     eauto.

  Definition P_Term (t : term) : Prop :=
    ∀ Δ Γ (H_ws : well_scoped Δ Γ t),
    fv t ⊆ Γ.

  Definition P_Binding (b : binding) :=
    ∀ Δ Γ rec (H_ws_bs : binding_well_formed Δ Γ b),
    fv_binding rec b ⊆ Γ.

  (* The free variables of a well-scoped term appear in Γ *)
  Lemma well_scoped_fv : (∀ t, P_Term t) /\ (∀ b, P_Binding b).
  Proof.
    apply term__multind with (P := P_Term) (Q := P_Binding).
    all: simpl; unfold P_Term; unfold P_Binding.
    - (* Let *)
      intros rec bs t IH_bs IH_t Δ Γ H_ws.
      rewrite Term.fv_equation.

      inversion H_ws; subst.
      + (* NonRec *)
        apply subset_append.
        * (* Free vars of bs are in Γ *)
          clear - IH_bs H4.
          revert Δ Γ IH_bs H4.
          induction bs as [ | b bs]; intros.
          **  simpl. unfold subset.
              intros.
              inversion H.
          ** inversion IH_bs; subst.
             inversion H4; subst.
             assert
               (HH : fv_bindings NonRec bs ⊆ (bvb b ++ Γ)) by eauto.
             unfold fv_bindings.
             rewrite Term.fvbs_equation.
             fold fv_bindings.
             apply subset_append.
             *** inversion IH_bs; subst.
                 eapply H6. eauto.
             *** apply subset_remove_many. eauto.
       * (* Free vars in (t \ bvbs) are in Γ*)
         assert (fv t ⊆ (rev (bvbs bs) ++ Γ)) by eauto.
         apply subset_rev_append_l in H.
         eauto using subset_remove_many.

      + (* Rec *)
        apply subset_append.
        * apply fv_binding_Rec__fv_bindings_Rec.
          apply well_scoped_bindings_Rec__Forall in H6.

          rewrite Util.ForallP_Forall in IH_bs.
          rewrite Forall_forall in *.
          intros b H_b_bs.

          specialize (H6 b H_b_bs).
          eapply IH_bs with (rec := Rec) in H6.
          ** apply subset_rev_append_l in H6.
             apply subset_remove_many.
             assumption.
          ** assumption.
        * apply IH_t in H7.
          apply subset_rev_append_l in H7.
          apply subset_remove_many.
          assumption.

    - (* Var *)
      intros x Δ Γ H_ws.
      rewrite Term.fv_equation.
      inversion H_ws. subst.
      unfold subset.
      intros x' H_in.
      assert (x' = x) by eauto using in_singleton_eq.
      subst.
      auto.

    - (* TyAbs *)
      use_IH.

    - (* LamAbs *)
      intros x τ t IH_t Δ Γ.
      intro.
      rewrite fv_equation.
      inversion H_ws; subst.
      specialize (IH_t _ _ H3).

      remember (remove string_dec x (Term.fv t)) as fv'.

      assert (x ∉ fv'). {
        subst fv'.
        eapply remove_In.
      }

      eapply (subset_cons (x := x)).
      + subst fv'. auto using remove_subset.
      + assumption.

    -  (* Apply *)
      use_IH.
      apply subset_append; eauto.

    - (* Constant*)
      use_IH.
      apply empty_subset.

    - (* Builtin *)
      use_IH.
      apply empty_subset.

    - (* TyInst *)
      use_IH.

    - (* Error *)
      use_IH.
      apply empty_subset.

    - (* IWrap *)
      use_IH.

    - (* Unwrap *)
      use_IH.

    - (* Constr *)
      admit.

    - (* Case *)
      admit.

    - (* TermBind *)
      intros s [x ty] t IH_t Δ Γ rec H_ws_b.
      destruct rec.
      all: simpl_fvb.
      + (* NonRec*)
        inversion H_ws_b; subst.
        eauto.
      + inversion H_ws_b; subst.
        eapply remove_subset.
        eauto.
    - (* TypeBind *)
      + intros.
        simpl_fvb.
        apply empty_subset.
    - intros dtd Δ Γ rec H_ws.
      simpl_fvb.
      apply empty_subset.

  Admitted.

  Corollary well_scoped_fv_term t Δ Γ :
    (Δ,, Γ |-+ t) -> fv t ⊆ Γ.
  Proof.
    revert Δ Γ.
    apply (proj1 well_scoped_fv t).
  Qed.

  (* The free type variables of a well-scoped term appear in Γ *)
  Lemma well_scoped_ftv {Δ Γ t}:
    well_scoped Δ Γ t ->
    ftv t ⊆ Δ.
  Proof.
  Admitted.

End ScopingLemmas.


Definition close ρ γ t := msubst γ (msubstA ρ t).

Lemma close_equation : ∀ ρ γ t,
  close ρ γ t = msubst γ (msubstA ρ t).
Proof. reflexivity. Qed.

Definition close_bnr ρ γ bs := msubst_bnr γ (msubstA_bnr ρ bs).

Lemma close_bnr_equation : ∀ ρ γ bs,
  close_bnr ρ γ bs = msubst_bnr γ (msubstA_bnr ρ bs).
Proof. reflexivity. Qed.

Section Purity.

  (* Semantically pure _closed_ term *)
  Definition pure t := exists k v, t =[k]=> v /\ ~ is_error v.

  (* Only substitutes pure (closed) terms *)
  Definition pure_substitution (γ : env) := Forall (fun '(x, t) => pure t) γ.

  Lemma RG_pure_substitution_1 : forall ρ k Γ γ γ',
    RG ρ k Γ γ γ' -> pure_substitution γ.
  Proof.
    intros ρ k Γ γ γ' H_RG.
    dependent induction H_RG.
    - constructor.
    - constructor.
      destruct H.
      assert (v1 =[0]=> v1). { apply eval_result. assumption. }
      + repeat eexists.
        all: eassumption.
      + assumption.
  Qed.

  Inductive substitution : tass -> env -> Prop :=
    | S_nil : substitution [] []
    | S_cons : forall Γ γ x t T,
        substitution Γ γ ->
        normal_Ty T ->
        ([] ,, [] |-+ t : T) ->
        substitution ((x, T) :: Γ) ((x, t) :: γ).

  Lemma RG_substitution_1 : forall ρ k Γ γ γ', RG ρ k Γ γ γ' -> substitution Γ γ.
  Proof.
  (* Should hold: substitution contains less information *)
  Admitted.

  (* Semantically pure _open_ term *)
  Definition pure_open Δ Γ t τ :=
    normal_Ty τ ->
    Δ ,, Γ |-+ t : τ ->
    forall ρ γ,
    substitution Γ γ ->
    pure_substitution γ ->
    pure (close ρ γ t).

  Definition pure_binding Δ Γ b :=
    match b with
      | TermBind Strict (VarDecl _ T) t => exists Tn, normalise T Tn /\ pure_open Δ Γ t Tn
      | _ => True
    end.


  Lemma msubst_result t γ ρ:
    result t /\ ~ is_error t ->
    result (msubst γ (msubstA ρ t)) /\ ~ is_error (msubst γ (msubstA ρ t)).
  Proof.
  Admitted.

  Lemma is_pure_nil_pure_open Δ Γ t τ:
    is_pure [] t ->
    pure_open Δ Γ t τ.
  Proof.
    intros H_is_pure H_normal H_ty ρ γ Γ_γ γ_pure.
    inversion H_is_pure.
    - unfold pure, close.
      remember (msubst γ (msubstA ρ t)) as t'.
      assert (H_t' : result t' /\ ~ is_error t').
      { subst. auto using msubst_result. }
      destruct H_t'.
      exists 0, t'.
      split.
      + apply eval_result. assumption.
      + assumption.
    - inversion H.
    - inversion H.
  Qed.


End Purity.

Lemma Forall_singleton {A} P (x : A) :
  Forall P [x] <-> P x.
Proof.
  split.
  - inversion 1. assumption.
  - auto.
Qed.

Lemma disjoint_contradiction {A : Set} {xs ys} {x : A} :
  x ∈ xs ->
  x ∈ ys ->
  ¬ (disjoint xs ys).
Proof.
Admitted.

Lemma no_shadow_disjoint Δ Γ rec bs t Δ' Γ' t' :

  (* Properties on pre-term *)
  no_shadow Δ Γ (Let rec bs t) ->

  (* Properties on post-term *)
  well_scoped Δ' Γ' t' ->

  (* TODO: why was this assumption not here? *)
  elim t t' ->

  Δ' ⊆ Δ ->
  Γ' ⊆ Γ ->
  forall b,
    In b bs ->
    disjoint (bvb b) (fv t') /\
    disjoint (btvb b) (ftv t').
Proof with eauto.
  intros H_pre_ns H_post_ws H_elim H_Δ_Δ' H_Γ_Γ'.
  intros b H_in_b_bs .

  destruct b as [ s [x ty] t_rhs | | ].
  all: split.

  (* TermBind term variables *)
  - unfold disjoint.

    (* TermBind *)
    + simpl.
      rewrite Forall_singleton.
      intros H_x_in_fv.

      assert (H_x_in_Γ : x ∈ Γ). {
        apply H_Γ_Γ'.
        eapply well_scoped_fv_term...
      }

      assert (H_x_in_bound_vars : x ∈ bound_vars (Let rec bs t)). {
        admit.
        (* TermBind s (VarDecl x ty) t_rhs ∈ bs *)
      }

      apply Term.ns_disjoint in H_pre_ns as H_disjoint.
      assert (H_not_disjoint : ¬ (disjoint Γ (bound_vars (Let rec bs t)))). {
        eapply (disjoint_contradiction H_x_in_Γ H_x_in_bound_vars).
      }
      contradiction.

  - (* TermBind type-variables*)
    admit.

  - (* TypeBind term-variables *)
    admit.

  - (* TypeBind type-variables *)
    admit.

  - (* DatatypeBind term-variables *)
    admit.

  - (* DatatypeBind type-variables *)
    admit.
Admitted.
