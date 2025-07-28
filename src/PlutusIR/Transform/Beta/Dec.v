From Coq Require Import
  Lists.List
  Strings.String.
Import ListNotations.
From PlutusCert Require Import
  PlutusIR
  Util
  Compat
  LetMergeNR
  FreeVars
  Util.List
  Util.Tactics
  Size
  Beta.Spec
.
Require Import
  Bool.Bool.
From PlutusCert Require Import
  Equality.


(* Defines when an argument in the (extended) application context has a
   sound decision procedure *)
Definition app_ctx_dec := list (term * (term -> bool)).

Section DEC.

  (* Decision procedures for each of the constructors in beta
   *)

  Context
    (dec : app_ctx_dec -> term -> term -> bool)
    (C : app_ctx_dec)
    (t t' : term)
  .

  Definition dec_compat : bool :=
    match C, t, t' with
    | [], t, t' => Compat.dec (dec []) t t'
    | _, _, _ => false
    end
    .

  Definition dec_Apply : bool :=
    match C, t, t' with
    | C, Apply s t, r => dec ((t, dec [] t) :: C) s r
    | _, _, _ => false
    end
  .

  Definition dec_TyAbs_TyInst : bool :=
    match C, t, t' with
    | []
    , TyInst (TyAbs X K t) T
    , Let NonRec [TypeBind (TyVarDecl X' K') T'] t'
    =>
        String.eqb X X' &&
        Kind_eqb K K' &&
        Ty_eqb T T' &&
        dec [] t t'
    | _, _, _ => false
    end.

  Definition dec_LamAbs : bool :=
    match C, t, t' with
    | (t0, dec_t0) :: C
    , LamAbs x T t
    , Let NonRec [TermBind Strict (VarDecl x' T') t0'] t'
    =>
        String.eqb x x' &&
        Ty_eqb T T' &&
        dec_t0 t0' &&
        dec C t t' &&
        forallb (fun '(t, f) => negb (in_str x (Term.fv t))) C
    | _, _, _ => false
    end
  .

End DEC.



Fixpoint dec (C : app_ctx_dec) (t t' : term) : bool :=
     dec_compat dec C t t'
  || dec_Apply dec C t t'
  || dec_LamAbs dec C t t'
  || dec_TyAbs_TyInst dec C t t'
.

Lemma dec_unfold C t t' :
  dec C t t' =
     dec_compat dec C t t'
  || dec_Apply dec C t t'
  || dec_LamAbs dec C t t'
  || dec_TyAbs_TyInst dec C t t'
.
Proof.
  destruct C, t, t'; reflexivity.
Qed.



Section SOUND.

  (* Soudness proofs for each of the constructor's decision procedure *)

  (* Defines when an argument in the (extended) application context has a
     sound decision procedure
  *)
  Definition arg_sound '(t, dec_t) :=
    forall t', dec_t t' = true -> betas [] t t'.

  #[local]
  Hint Unfold arg_sound : core.


  Lemma Forall_map_fst {A} (f : term -> Prop) (l : list (term * A)):
    Forall (fun '(t, _) => f t) l ->
    Forall (fun t => f t) (map fst l).
  Proof.
    induction l.
    - auto.
    - inversion 1; subst.
      destruct a.
      constructor; auto.
  Qed.


  Context
    (dec : app_ctx_dec -> term -> term -> bool)
    (dec_sound : forall C s t,
      Forall arg_sound C ->
      dec C s t = true ->
      betas (map fst C) s t)
    (C : list (term * (term -> bool)))
    (C_sound : Forall arg_sound C)
    (t t' : term)
  .

  Lemma dec_sound_Apply : dec_Apply dec C t t' = true -> betas (map fst C) t t'.
  Proof.
    unfold dec_Apply.
    destruct_match; try solve [inversion 1].
    intros H_dec.
    apply b_Apply.
    apply dec_sound in H_dec.
    - auto.
    - specialize (dec_sound []) as dec_sound_nil. (* specialize IH for argument in list *)
      auto using Forall.
  Defined.

  Lemma dec_sound_LamAbs : dec_LamAbs dec C t t' = true -> betas (map fst C) t t'.
  Proof.
    unfold dec_LamAbs.
    repeat (destruct_match; try solve [inversion 1]).
    intros H_dec.
    repeat apply andb_and in H_dec as [H_dec ?].
    simpl.

    apply b_LamAbs; try solve [auto with reflection].

    - eauto using Forall_inv_tail.
    - unfold arg_sound in C_sound.
      auto using Forall_inv.
      apply Forall_inv in C_sound.
      auto.
    - apply Forall_map_fst.
      rewrite forallb_forall in H.
      rewrite Forall_forall.
      intros.
      specialize (H x H3).
      destruct x.
      apply negb_in_str__NotIn.
      assumption.
  Defined.

  Lemma dec_sound_TyBeta :
    dec_TyAbs_TyInst dec C t t' = true ->
    betas (map fst C) t t'.
  Proof.
    unfold dec_TyAbs_TyInst.
    repeat (destruct_match; try solve [inversion 1]).
    specialize (dec_sound []). (* specialize IH *)
    intro; destruct_hypos.
    apply b_TyInst_TyAbs; auto with reflection.
  Defined.


  Definition P_term t := forall C t',
    dec_compat dec C t t' = true ->
    betas (map fst C) t t'
  .

  Lemma dec_sound_compat :
    dec_compat dec C t t' = true ->
    betas (map fst C) t t'.
  Proof.
    specialize (dec_sound []). (* usable IH for auto due to map fst *)
    destruct C; try solve [inversion 1].
    destruct t, t'.
    all: try solve [unfold dec_compat; inversion 1].
    all: intros H_dec; simpl in H_dec; try discriminate H_dec.
    all: split_hypos.
    all: try (constructor; (auto with compat reflection)).
    - (* Let *)
      apply c_Let; try solve [eauto with compat reflection].
      + revert dependent l0. induction l; intros l0 H_dec.
        * destruct l0; simpl.
          ** constructor.
          ** inversion H_dec.
        * destruct l0.
          ** inversion H_dec.
          ** constructor.
            ***
                unfold forall2b, Compat.dec_binding in H_dec.
                destruct a, b; destruct_hypos; try solve [inversion H1].
                destruct_hypos.
                ++ eauto with compat reflection.
                ++ eauto with compat reflection.
                ++ eauto with compat reflection.
            ***
                unfold forall2b, Compat.dec_binding in H_dec.
            destruct_hypos.
              auto.
  Defined.

End SOUND.

Create HintDb beta_sound.
#[export] Hint Resolve
  dec_sound_compat
  dec_sound_Apply
  dec_sound_LamAbs
  dec_sound_TyBeta
: beta_sound
.



Fixpoint dec_sound C t t' {struct t} :
  Forall arg_sound C ->
  dec C t t' = true ->
  betas (map fst C) t t'.
Proof.
  setoid_rewrite dec_unfold.
  repeat rewrite orb_true_iff.
  intros C_sound H_dec.
  repeat destruct H_dec as [ H_dec | H_dec ];
  eauto 2 with beta_sound. (* Search becomes inefficient, probably because it doesn't know in what order to try the dec_sound lemmas  *)
Defined.
