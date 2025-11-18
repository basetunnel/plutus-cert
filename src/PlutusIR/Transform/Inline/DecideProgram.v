Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import PeanoNat.

Import ListNotations.
From Equations Require Import Equations.
Require Import Program.
Require Import Lia.

Set Implicit Arguments.
Set Equations Transparent.

From PlutusCert Require Import Util.
From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import PlutusIR.Analysis.FreeVars.
From PlutusCert Require Import PlutusIR.Transform.Inline.Spec.
From PlutusCert Require Import PlutusIR.Transform.Compat.
From PlutusCert Require Import PlutusIR.Examples.


Generalizable All Variables.
Definition Env := list (prod string Term).

(*
Derive NoConfusion NoConfusionHom Subterm for Term.
*)

Definition Smaller (s s' t t' : Term) : Prop :=
  term_size s + term_size s' < term_size t + term_size t'.

Definition SmallerBindings (cs cs' bs bs': list Binding) : Prop :=
  length cs + length cs' < length bs + length bs'.

Lemma size_non_zero : forall t, term_size t > 0.
  induction t; compute; intuition.
  (* induction t; compute; lia*)
Qed.


(*
Show how fold term_size reduces into recursive calls
*)
Lemma fold_reduce_let : forall r t bs,
  term_size (Let r bs t)  = 1 + list_sum (term_size t :: map binding_size bs).
reflexivity. Qed.

Lemma fold_reduce_apply : forall s t,
  term_size (Apply s t) = 1 + list_sum [term_size s ; term_size t].
reflexivity. Qed.

Lemma fold_reduce_tyabs : forall n k t,
  term_size (TyAbs n k t) = 1 + list_sum [term_size t].
reflexivity. Qed.

Lemma fold_reduce_lamabs : forall n k t,
  term_size (LamAbs n k t) = 1 + list_sum [term_size t].
reflexivity. Qed.

Lemma fold_reduce_tyinst : forall t ty,
  term_size (TyInst t ty) = 1 + list_sum [term_size t].
reflexivity. Qed.

Lemma fold_reduce_iwrap : forall ty1 ty2 t,
  term_size (IWrap ty1 ty2 t) = 1 + list_sum [term_size t].
reflexivity. Qed.

Lemma fold_reduce_unwrap : forall t,
  term_size (Unwrap t) = 1 + list_sum [term_size t].
reflexivity. Qed.

Lemma fold_reduce_termbind s v t:
  binding_size (TermBind s v t) = 1 + list_sum [term_size t].
  reflexivity.
Qed.

(*Prove that structural subterms are smaller in size*)
Lemma let_struct : forall r bs t, term_size t < term_size (Let r bs t).
Proof. intros r bs t. rewrite fold_reduce_let. simpl. intuition. Qed.

Lemma app_struct_l : forall s t, term_size s < term_size (Apply s t).
  compute; intuition.
Qed.

Lemma app_struct_r : forall s t, term_size t < term_size (Apply s t).
Proof. intros s t. rewrite fold_reduce_apply. simpl. intuition. Qed.

Lemma tyabs_struct : forall n k t, term_size t < term_size (TyAbs n k t).
Proof. intros n k t. rewrite fold_reduce_tyabs. simpl. intuition. Qed.

Lemma lamabs_struct : forall n ty t, term_size t < term_size (LamAbs n ty t).
Proof. intros n k t. rewrite fold_reduce_lamabs. simpl. intuition. Qed.

Lemma tyinst_struct : forall t ty, term_size t < term_size (TyInst t ty).
Proof. intros t ty. rewrite fold_reduce_tyinst. simpl. intuition. Qed.

Lemma iwrap_struct : forall ty1 ty2 t, term_size t < term_size (IWrap ty1 ty2 t).
Proof. intros ty1 ty2 t. rewrite fold_reduce_iwrap. simpl. intuition. Qed.

Lemma unwrap_struct : forall t, term_size t < term_size (Unwrap t).
Proof. intros t. rewrite fold_reduce_unwrap. simpl. intuition. Qed.

Lemma termbind_struct s v t :  term_size t < binding_size (TermBind s v t).
Proof. rewrite fold_reduce_termbind. simpl. intuition. Qed.

Lemma bind_binds_struct b bs : binding_size b < bindings_size (b :: bs).
Proof. unfold bindings_size. simpl. intuition. Qed.


Definition TermsLt := fun ts ts' =>
  match ts, ts' with
  | (t1, t2), (t1', t2') => term_size t1 + term_size t2 < term_size t1' + term_size t2'
  end.

Definition is_compat_binding (b b' : Binding) R
(is_r_term : forall (t t' : Term), term_size t + term_size t' < binding_size b + binding_size b'
  -> option (R t t'))
: option (Compat_Binding R b b').
Proof.
refine (

  match b as p return b = p -> _ with
    | TypeBind d ty =>
      match b' as p' return b' = p' -> _ with
      | TypeBind d' ty' => _
      | _               => fun _ _ => None
      end eq_refl

    | DatatypeBind d =>
      match b' as p' return b' = p' -> _ with
      | DatatypeBind d' => _
      | _               => fun _ _ => None
      end eq_refl

    | TermBind s v t =>
      match b' as p' return b' = p' -> _ with
      | TermBind s' v' t' => _
      | _               => fun _ _ => None
      end eq_refl

  end eq_refl
); intros; subst.

- refine ( _
  <$> sumbool_to_optionl (Strictness_dec s s')
  <*> sumbool_to_optionl (VDecl_dec v v')
  <*> is_r_term t t' _
); intros; subst.
  refine (C_TermBind R X); constructor. (* Constructing tts for Tys*)
  (* Prove that the terms are smaller *)
  apply Nat.add_lt_mono; apply termbind_struct.

- refine (_
  <$> sumbool_to_optionl (TVDecl_dec d d')
  <*> sumbool_to_optionl (Ty_dec ty ty')
); intros;subst; constructor.

- refine (_
  <$> sumbool_to_optionl (DTDecl_dec d d')
); intros;subst;constructor.
Qed.


Fixpoint is_compat_bindings bs bs' R
(is_R_term_bs : forall (t t' : Term), term_size t + term_size t' < bindings_size bs + bindings_size bs'
  -> option (R t t'))
{struct bs}
  : option (Compat_Bindings R bs bs').
Proof.
refine (
  match bs as p return bs = p -> _ with

    | (b :: bs) => match bs' as p' return bs' = p' -> _ with
      | (b' :: bs') => ?[cons]
      | _           => fun _ _ => None
      end eq_refl

    | nil             => match bs' as p' return bs' = p' -> _ with
      | nil         => ?[nil]
      | _           => fun _ _ => None
      end eq_refl

    end eq_refl
).
Show Existentials.
[nil]: {
  intros. refine (Some _); constructor.
}

[cons]: {
  intros. subst.
  refine (
    ?[Compat_cons] <$> is_compat_binding b b' R ?[b_smaller]
                 <*> is_compat_bindings bs bs' R ?[bs_smaller]
  ).
  [Compat_cons]: { constructor; assumption. }
  [b_smaller]: { intros. apply is_R_term_bs.
    assert (L : binding_size b + binding_size b' < bindings_size (b :: bs) + bindings_size (b' :: bs')).
      - unfold bindings_size. simpl. intuition.
      - refine (Nat.lt_trans _ _ _ H L).
  }
  [bs_smaller]: {
    intros. apply is_R_term_bs.
    assert (L : bindings_size bs + bindings_size bs' <= bindings_size (b :: bs) + bindings_size (b' :: bs')).
      - unfold bindings_size. repeat rewrite -> map_cons. simpl. intuition.
    - eapply (Nat.lt_le_trans). exact H. exact L.
  }
}
Qed.

Definition is_compat (t t' : Term) R
  (is_R_term : forall (s s' : Term), Smaller s s' t t' -> option (R s s'))
  : option (Compat R t t').
Proof.
refine (
  match t as p return t = p -> _ with

  | Let r bs t   => match t' as p' return t' = p' -> _ with
    | Let r' bs' t' => _
    | _           => fun _ _ => None
    end eq_refl

  | Apply s t   => match t' as p' return t' = p' -> _ with
    | Apply s' t' => _
    | _           => fun _ _ => None
    end eq_refl

  | Var m       => match t' as p' return t' = p' -> _ with
    | Var n => _
    | _     => fun _ _ => None
    end eq_refl

  | TyAbs n k t => match t' as p' return t' = p' -> _ with
    | TyAbs n' k' t' => _
    | _              => fun _ _ => None
    end eq_refl

  | LamAbs n ty t => match t' as p' return t' = p' -> _ with
    | LamAbs n' ty' t' => _
    | _              => fun _ _ => None
    end eq_refl

  | TyInst t ty => match t' as p' return t' = p' -> _ with
    | TyInst t' ty' => _
    | _              => fun _ _ => None
    end eq_refl

  | IWrap ty1 ty2 t => match t' as p' return t' = p' -> _ with
    | IWrap ty1 ty2 t' => _
    | _              => fun _ _ => None
    end eq_refl

  | Unwrap t => match t' as p' return t' = p' -> _ with
    | Unwrap t' => _
    | _              => fun _ _ => None
    end eq_refl

  | Constant c => match t' as p' return t' = p' -> _ with
    | Constant c' => _
    | _              => fun _ _ => None
    end eq_refl

  | Builtin f => match t' as p' return t' = p' -> _ with
    | Builtin f' => _
    | _          => fun _ _ => None
    end eq_refl

  | Error ty => match t' as p' return t' = p' -> _ with
    | Error ty' => _
    | _          => fun _ _ => None
    end eq_refl

  end eq_refl
)
; intros; subst. (* Use all the equalities of pattern matching *)

(* Let*)
- refine (
  ?[cstr] <$> sumbool_to_optionl (Recursivity_dec r r')
    <*> is_compat_bindings R ?[is_R_term]
    <*> is_R_term t t' ?[smaller]
).
[cstr] : {
  intro; subst r.
  apply C_Let.
}
[is_R_term] : {
  intros; apply is_R_term.
  assert (forall r bs t, bindings_size bs <= term_size (Let r bs t)).
    {intros. unfold term_size, Folds.foldTermUse, Folds.foldTerm. simpl.
      unfold bindings_size. info_auto with arith. }
  assert (bindings_size bs + bindings_size bs' <= term_size (Let r bs t) + term_size (Let r' bs' t')).
    {auto using H0, Nat.add_le_mono. }
  unfold Smaller; eauto using H, H1, Nat.lt_le_trans.
}
[smaller] : {
  unfold Smaller. auto using Nat.add_lt_mono, let_struct.
}


(* Var case*)
- refine (
  eq_rect m (fun x => Compat R (Var m) (Var x))
      (@C_Var R m) n
      <$> sumbool_to_optionl (string_dec m n)

).

(* TyAbs Case*)
- refine
  (_ <$> sumbool_to_optionl (string_dec n n')
     <*> sumbool_to_optionl (Kind_dec k k')
     <*> is_R_term t t' _); intros; subst.
  {refine (
    C_TyAbs R X
    ).
  }
 {unfold Smaller. apply Plus.plus_lt_compat; apply tyabs_struct. }

(* LamAbs *)
- refine
  (_ <$> sumbool_to_optionl (string_dec n n')
     <*> sumbool_to_optionl (Ty_dec ty ty')
     <*> is_R_term t t' _); intros; subst.
  {refine (
    C_LamAbs R X
    ).
  }
 {unfold Smaller. apply Plus.plus_lt_compat; apply lamabs_struct. }


(* Apply case *)
-  refine (
    C_Apply R <$> is_R_term s s' _ <*> is_R_term t t' _ (* The obligations will show that s s' and t t' are smaller*)
  ).
 {unfold Smaller. apply Plus.plus_lt_compat; apply app_struct_l. }
 {unfold Smaller. apply Plus.plus_lt_compat; apply app_struct_r. }

(* Constant *)
- refine (_ <$> sumbool_to_optionl (some_dec c c'))
  ; intros; subst; constructor.

(* Builtin*)
- refine (_ <$> sumbool_to_optionl (func_dec f f'))
  ; intros;subst; constructor.


(* TyInst *)
- refine (
  _ <$> sumbool_to_optionl (Ty_dec ty ty')
    <*> is_R_term t t' _); intros; subst.
  refine (
    C_TyInst R X
  ).
 {unfold Smaller. apply Plus.plus_lt_compat; apply tyinst_struct. }

(* Error *)
- refine (_ <$> sumbool_to_optionl (Ty_dec ty ty'))
  ; intros; subst; constructor.

(* IWrap *)
- refine (
  _ <$> sumbool_to_optionl (Ty_dec ty1 ty3)
    <*> sumbool_to_optionl (Ty_dec ty2 ty4)
    <*> is_R_term t t' _); intros; subst.
  refine (
    C_IWrap R X
  ).
 {unfold Smaller. apply Plus.plus_lt_compat; apply iwrap_struct. }

(* Unwrap *)
- refine (
  _ <$> is_R_term t t' _); intros; subst.
  refine (
    C_Unwrap R X
  ).
 {unfold Smaller. apply Plus.plus_lt_compat; apply unwrap_struct. }

Show Proof.
Defined.



(*

(*
Writing is_compat with Program Fixpoint gives a lot of obligations about impossible
patterns, tedious to solve.
*)

Program Fixpoint is_compat' (t t' : Term) R
  (f : forall (s s' : Term), Smaller s s' t t' -> option (R s s'))
  : option (Compat R t t') :=
  match t, t' with
  | Apply s t, Apply s' t'    => C_Apply R <$> f s s' _ <*> f t t' _ (* The obligations will show that s s' and t t' are smaller*)
  | Var m, Var n              => eq_rect m (fun x => Compat R (Var m) (Var x))
      (@C_Var R m) n
      <$> sumbool_to_optionl (string_dec m n)
  (* | Let r bs t, Let r' bs' t' => _ *)
  | _, _                      => None
  end
.


Next Obligation.
  unfold Smaller. apply Plus.plus_lt_compat; apply app_struct_l.
Qed.

Next Obligation.
  unfold Smaller. apply Plus.plus_lt_compat; apply app_struct_r.
Qed.

Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.
Next Obligation. intuition; congruence. Qed.

(* Why doesn't this work instead?

Solve Obligations of is_compat with (intros; intuition; congruence).*)

*)



Program Fixpoint is_inline (env : Env) (t t' : Term) {measure (term_size t + term_size t')}
  : option (Inline env t t') :=
  match t, t' with
  | t, t' => Inl_Compat <$> (@is_compat t t' (Inline env) (fun s s' H => is_inline env s s'))
  end
.


Open Scope string_scope.
Definition test := (Apply (Var "n") (Var "m")).
Eval cbv in is_inline nil test test.
