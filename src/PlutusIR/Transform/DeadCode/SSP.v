Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.PlutusIR.Transform.DeadCode.Spec2.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import PlutusCert.PlutusIR.Semantics.Static.
From PlutusCert Require Import Normalization.BigStep.

Import Utf8_core.


Set Diffs "on".

Definition P_has_type Δ Γ t1 T : Prop :=
  forall t2,
    dc t1 t2 ->
    Δ ,, Γ |-+ t2 : T.

Definition P_constructor_well_formed Δ c T : Prop :=
  Δ |-ok_c c : T.

Definition P_bindings_well_formed_nonrec Δ Γ bs1 : Prop :=
  (
    forall bs2,
      Δ ,, Γ |-oks_nr bs1 ->
      Compat.Compat_Bindings dc bs1 bs2 ->
      Δ ,, Γ |-oks_nr bs2
  ).

Definition P_bindings_well_formed_rec Δ Γ bs1 : Prop :=
  forall bs2,
    Δ ,, Γ |-oks_r bs1 ->
    Compat.Compat_Bindings dc bs1 bs2 ->
    Δ ,, Γ |-oks_r bs2
.

Definition P_binding_well_formed Δ Γ rec b1 : Prop :=
  forall b2,
    Δ ,, Γ |-ok_b rec # b1 ->
    Compat.Compat_Binding dc b1 b2 ->
    Δ ,, Γ |-ok_b rec # b2
.

#[export] Hint Unfold
  P_has_type
  P_constructor_well_formed
  P_bindings_well_formed_nonrec
  P_bindings_well_formed_rec
  P_binding_well_formed
  : core.


(* TODO: move to separate file *)
Section CompatLemmas.

  Import Transform.Compat.

  Lemma compat_Binding__binds_Gamma b1 b2 :
    Compat_Binding dc b1 b2 ->
    binds_Gamma b1 = binds_Gamma b2.
  Proof.
    intros H_compat.
    inversion H_compat; reflexivity.
  Qed.

  Lemma compat_Binding__binds_Delta b1 b2 :
    Compat_Binding dc b1 b2 ->
    binds_Delta b1 = binds_Delta b2.
  Proof.
    intros H_compat.
    inversion H_compat; reflexivity.
  Qed.

  Lemma compat_Bindings__binds_Gamma bs1 bs2 :
    Compat_Bindings dc bs1 bs2 ->
    map binds_Gamma bs1 = map binds_Gamma bs2.
  Proof.
    revert bs2.
    induction bs1.
    all: intros bs2 H_compat; inversion H_compat.
    - reflexivity.
    - subst.
      simpl.
      f_equal;
      auto using compat_Binding__binds_Gamma.
  Qed.

  Lemma compat_Bindings__binds_Delta bs1 bs2 :
    Compat_Bindings dc bs1 bs2 ->
    map binds_Delta bs1 = map binds_Delta bs2.
  Proof.
    revert bs2.
    induction bs1.
    all: intros bs2 H_compat; inversion H_compat.
    - reflexivity.
    - subst.
      simpl.
      f_equal;
      auto using compat_Binding__binds_Delta.
  Qed.

End CompatLemmas.


(*

Theorem dc__SSP : forall Δ Γ t1 T,
    Δ ,, Γ |-+ t1 : T ->
    P_has_type Δ Γ t1 T.
Proof with (eauto with typing).
  apply has_type__multind
    with
      (P := P_has_type)
      (P0 := P_constructor_well_formed)
      (P1 := P_bindings_well_formed_nonrec)
      (P2 := P_bindings_well_formed_rec)
      (P3 := P_binding_well_formed)
  .

  all: try (* All P_has_type cases, except Let Rec and Let NonRec *)
    (intros;
    unfold P_has_type;
    intros t' H_dc;
    inversion H_dc;
    inversion H_compat; clear H_compat; subst;
    eauto using has_type
    )
    .

  2: { (* Let Rec *)
    unfold P_has_type.
    unfold P_bindings_well_formed_rec in *.
    intros.
    match goal with | H : dc _ _ |- _ => inversion H; subst; clear H end.
    - (* Compat *)
      match goal with
        | H : Compat.Compat _ _ _ |- _ => inversion H; subst; clear H
      end.
      erewrite compat_Bindings__binds_Delta
        with (bs1 := bs) (bs2 := bs') in *;
        try assumption.
      erewrite compat_Bindings__binds_Gamma
        with (bs1 := bs) (bs2 := bs') in *;
        try assumption.
      eauto using has_type.
    - (* dc_Rec *)

      admit.
    }

Admitted.

  *)


Definition P_dc t t' :=
  ∀ Δ Γ T,
    Δ ,, Γ |-+ t : T ->
    Δ ,, Γ |-+ t' : T
.


Definition P_dc_NonRec t' bs bs' :=
  ∀ Δ Γ T t,
    (*
    Δ' = flatten (map binds_Delta bs) ++ Δ ->
    map_normalise (flatten (map binds_Gamma bs)) bsGn ->
    Γ' = bsGn ++ Γ ->
    Δ' ,, Γ' |-+ t : T ->
    Δ' ,, Γ' |-+ t' : T ->
    *)
    P_dc t t' ->
    Δ ,, Γ |-+ (Let NonRec bs t) : T ->
    Δ ,, Γ |-+ (Let NonRec bs' t') : T
.

  (*
      map_normalise (flatten (map binds_Gamma bs0)) bsGn ->
      map_normalise (flatten (map binds_Gamma bs0')) bsGn ->
      Γ' = bsGn ++ Γ ->
      Δ' ,, Γ' |-oks_r bs ->
      *)

Definition P_dc_Rec (bs0' : list binding) (t' : term) (bs bs' : list binding) :=
    forall Δ Γ,
    Δ ,, Γ |-oks_r bs ->
    Δ ,, Γ |-oks_r bs'
  .
  (*
  ∀ Δ Γ T t Δ' bsGn Γ',
    Δ' = flatten (map binds_Delta bs) ++ Δ ->
    map_normalise (flatten (map binds_Gamma bs)) bsGn ->
    Γ' = bsGn ++ Γ ->
    Δ' ,, Γ' |-+ t : T ->
    Δ' ,, Γ' |-+ t' : T ->
    Δ' ,, Γ' |-+ (Let Rec bs t) : T ->
    Δ' ,, Γ' |-+ (Let Rec bs' t') : T
    *)

Import Transform.Compat.

Ltac inversion_typing :=
  match goal with
    | H : has_type _ _ _ _ |- _ => inversion H; subst
  end.

Lemma dc_Rec__map_normalise bs0' bs bs' t' (bsGn bsGn' : list (string * ty)):
  dc_Rec bs0' t' bs bs' ->
  map_normalise (flatten (map binds_Gamma bs)) bsGn ->
  exists bsGn',
    map_normalise (flatten (map binds_Gamma bs')) bsGn'.
Admitted.


Lemma unused_strengthen_Delta b bs t Δ Γ T:
  unused_in b (Let Rec bs t) ->
  flatten (map binds_Delta (b :: bs)) ++ Δ,, Γ |-+ t : T ->
  flatten (map binds_Delta bs) ++ Δ,, Γ |-+ t : T.
Admitted.

Lemma unused_strengthen_Gamma b bs t Δ Γ T:
  unused_in b (Let Rec bs t) ->
  flatten Δ,, flatten (binds_Gamma b :: map binds_Gamma bs) ++ Γ |-+ t : T ->
  flatten Δ,, flatten (map binds_Gamma bs) ++ Γ |-+ t : T.
Admitted.


(* Lemma for unused_in__incl*)
Lemma incl_disjoint {A} (xs ys ys' : list A) :
  incl ys ys' ->
  disjoint xs ys' ->
  disjoint xs ys.
Admitted.

(* If a binding is unused in the whole let-rec, it's also unused in a let-rec
* with fewer bindings*)
Lemma unused_in__incl b bs bs0 t:
  incl bs bs0 ->
  unused_in b (Let Rec bs0 t) ->
  unused_in b (Let Rec bs t).
Proof.
  intros.
  unfold unused_in in *.
  (* ADMITTED: used disjoint lemmas to simplify assumptions, then use
  * incl_disjoint *)
Admitted.

(*  Related bindings can be used interchangably in the context of the post-term.
    This should hold in both directions.
    TODO: prove in backwards direction (if needed)
   *)
Lemma dc_Rec__strengthen bs0' t' bs bs' bsGn Δ Γ T:
  dc_Rec bs0' t' bs bs' ->
  incl bs' bs0' ->

  (* TODO: add these to the typing rule of let-rec, there can be no shadowing in
   * a let-rec *)
  NoDup (bvbs bs) ->
  NoDup (btvbs bs) ->

  map_normalise (flatten (map binds_Gamma bs)) bsGn ->
  flatten (map binds_Delta bs) ++ Δ ,, bsGn ++ Γ |-+ t' : T ->
  exists bsGn',
    map_normalise (flatten (map binds_Gamma bs')) bsGn' /\
    (flatten (map binds_Delta bs') ++ Δ ,, bsGn' ++ Γ |-+ t' : T)
.
Proof.
  intros H_dc H_incl H_NoDup_bvbs H_NoDup_btvbs H_map_norm H_typing.
  assert
    (H : exists bsGn', map_normalise (flatten (map binds_Gamma bs')) bsGn')
      by eauto using dc_Rec__map_normalise.
  destruct H as [bsGn' H_map_norm'].
  exists bsGn'.
  split.
  - assumption.
  - (* Generalise for induction *)
    revert bs' H_dc H_incl bsGn bsGn' H_typing H_map_norm H_map_norm'.
    induction bs as [ | b bs ]  ; intros bs' H_dc H_incl bsGn bsGn' H_typing H_map_norm H_map_norm'.
    + (* [] *)
      inversion H_dc; subst.
      unfold flatten in *.
      simpl in *.
      inversion H_map_norm'; subst.
        inversion H_map_norm; subst.
      assumption.
    + (* _ :: _ *)
      inversion H_dc; subst.
      * (* dc_Rec_elim *)
        simpl in H_map_norm.
        assert (H_NoDup_bvbs_tl : NoDup (bvbs bs)). { admit. } (* TODO: use NoDup_app_remove1 *)
        assert (H_NoDup_btvbs_tl : NoDup (btvbs bs)). { admit. } (* TODO: use NoDup_app_remove1 *)

        specialize (IHbs H_NoDup_bvbs_tl H_NoDup_btvbs_tl). clear H_NoDup_bvbs_tl H_NoDup_btvbs_tl.
        specialize (IHbs _ H_dc_bs). clear H_dc_bs.
        specialize (IHbs H_incl).

        assert (H_unused_t' : unused_in b t'). { admit. } (* TODO: follows from H_NoDup_... *)

        rename bsGn into bbsGn.
        assert (H_map_norm_bs : exists bsGn,
          map_normalise (flatten (map binds_Gamma bs)) bsGn). { admit. } (* TODO: simplify and inversion *)
        destruct H_map_norm_bs as [ bsGn H_map_norm_bs].

        assert (H_typing' : flatten (map binds_Delta bs) ++ Δ,, bsGn ++ Γ |-+ t' : T).
        { apply unused_strengthen_Delta in H_typing.

          - rewrite flatten_cons in H_map_norm.
            apply map_normalise__app in H_map_norm.
            destruct H_map_norm as [_ [bGn [_ [H_map_norm_bGn _]]]].
            admit.
          - admit.

        }

        specialize (IHbs _ _ H_typing' H_map_norm_bs H_map_norm').
        assumption.

      * (* dc_Rec_keep *)
        unfold flatten in H_map_norm, H_map_norm'.
        simpl in H_map_norm, H_map_norm'.
        rewrite concat_app in H_map_norm, H_map_norm'.
        apply map_normalise__app in H_map_norm, H_map_norm'.

        admit.
Admitted.



Theorem dc__SSP' : forall t t',
    dc t t' ->
    P_dc t t'
.
Proof with (eauto with typing).
  apply dc__multind
    with (P := P_dc) (P0 := P_dc_NonRec) (P1 := P_dc_Rec).

  (* All compatibility / reflexivity cases *)
  all: try
    solve
      [
        unfold P_dc, P_dc_NonRec, P_dc_Rec in *
      ; intros
      ; inversion_typing
      ; eauto using has_type
      ].
  -
    repeat unfold P_dc, P_dc_NonRec, P_dc_Rec in *.
    intros ? ? ? ? H_dc_t IH_t H_dc_Rec IH_Rec ? ? ? H_typing_Let.
    inversion H_typing_Let; subst.
    eapply IH_t in H7;
      try (solve [eassumption | reflexivity]).
    eapply IH_Rec in H6.
    econstructor; eauto.
    eauto using has_type, bindings_well_formed_rec.

    all: admit.
  - admit.

  - admit.
  - admit.
  - admit.
  -admit.
Admitted.
