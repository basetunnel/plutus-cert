From Coq Require Import
  Strings.String
  Lists.List
.
From PlutusCert Require Import
  Util
  Util.List
  PlutusIR.

Import ListNotations.

Definition ctx := list (string * string).

Reserved Notation "Δ ⊢* s '~' t" (at level 40).
Reserved Notation "Δ ,, Γ ⊢ s '~' t" (at level 40).
Reserved Notation "Δ ,, Γ ⊢b s '~' t" (at level 40).

Inductive alpha_lookup : ctx -> string -> string -> Prop :=


  (* This rule seems unnecessary as long as (x,x) is recorded in the
   * environment. I guess it makes it possible to define alpha equivalent terms
   * as those related under the empty environment. The alternative is to define
   * it for open terms by constructing an identity environment for all free
   * variables.
   *)
  (*
  | AL_refl x :
      alpha_lookup [] x x
  *)

  | AL_cons x y xs :
      alpha_lookup ((x, y) :: xs) x y

  | AL_diff x y z w xs :
      x <> z ->
      y <> w ->
      alpha_lookup xs z w ->
      alpha_lookup ((x, y) :: xs) z w
.


Module TY.

  Inductive ty_alpha : list (string * string) -> ty -> ty -> Prop :=

    | A_TyVar X X' Δ :
        alpha_lookup Δ X X' ->
        Δ ⊢* Ty_Var X ~ Ty_Var X'

    | A_TyLam X X' K T T' Δ :
        ((X, X') :: Δ) ⊢* T ~ T' ->
        Δ ⊢* Ty_Lam X K T ~ Ty_Lam X' K T'

    | A_TyApp T1 T2 T1' T2' Δ :
        Δ ⊢* T1 ~ T1' ->
        Δ ⊢* T2 ~ T2' ->
        Δ ⊢* Ty_App T1 T2 ~ Ty_App T1' T2'

    | A_TyFun T1 T2 T1' T2' Δ :
        Δ ⊢* T1 ~ T1' ->
        Δ ⊢* T2 ~ T2' ->
        Δ ⊢* Ty_Fun T1 T2 ~ Ty_Fun T1' T2'

    | A_TyIFix T1 T2 T1' T2' Δ :
        Δ ⊢* T1 ~ T1' ->
        Δ ⊢* T2 ~ T2' ->
        Δ ⊢* Ty_IFix T1 T2 ~ Ty_IFix T1' T2'

    | A_TyForall X X' K T T' Δ :
        ((X, X') :: Δ) ⊢* T ~ T' ->
        Δ ⊢* Ty_Forall X K T ~ Ty_Forall X' K T'

    | A_TyBuiltin Δ U :
        Δ ⊢* Ty_Builtin U ~ Ty_Builtin U

    | A_TySOP Δ Tss Tss':
        ForallSetPair2 (fun T T' => Δ ⊢* T ~ T') Tss Tss' ->
        Δ ⊢* Ty_SOP Tss ~ Ty_SOP Tss'

    where "Δ ⊢* s '~' t" := (ty_alpha Δ s t)
  .



  Definition ctx_refl (xs : ctx) := Forall (fun '(x, y) => x = y) xs.

  Lemma alpha_refl xs t :
    ctx_refl xs ->
    xs ⊢* t ~ t.
  Proof.
  Admitted.


  Inductive pair_sym : string * string -> string * string -> Prop :=
    | PS_pair x y : pair_sym (x, y) (y, x)
  .

  Definition ctx_sym (xs ys : ctx) : Prop := Forall2 pair_sym xs ys.

  Lemma alpha_sym xs ys t t':
    ctx_sym xs ys ->
    xs ⊢* t ~ t' ->
    ys ⊢* t' ~ t.
  Proof.
  Admitted.

  Inductive pair_trans : string * string -> string * string -> string * string -> Prop :=
    | PT_pair x y z : pair_trans (x, y) (y, z) (x, z)
  .

  Definition ctx_trans (xs ys zs : ctx) : Prop := Forall3 pair_trans xs ys zs.

  Lemma alpha_trans xs ys zs t t' t'':
    ctx_trans xs ys zs ->
    xs ⊢* t ~ t' ->
    ys ⊢* t' ~ t'' ->
    ys ⊢* t ~ t''
    .
  Proof.
  Admitted.


End TY.

Import PIRNotations. Open Scope pir_scope.
Import TY.

Inductive alpha
  (Δ : list (string * string))
  (Γ : list (string * string))
  : term -> term -> Prop :=

  | A_Var x x' :
      alpha_lookup Γ x x' ->
      Δ ,, Γ ⊢ `x ~ `x'

  | A_LamAbs x x' T t t' :
      Δ ,, ((x, x') :: Γ) ⊢ t ~ t' ->
      Δ ,, Γ ⊢ λ x T t ~ λ x' T t'

  | A_Apply t1 t2 t1' t2' :
      Δ ,, Γ ⊢ t1 ~ t1' ->
      Δ ,, Γ ⊢ t2 ~ t2' ->
      Δ ,, Γ ⊢ (t1 ⋅ t2) ~ (t1' ⋅ t2')

  | A_Let r bs t bs' t' :
      Δ ,, Γ ⊢ t ~ t' ->
      Δ ,, Γ ⊢ Let r bs t ~ Let r bs' t'

  | A_TyAbs X K t X' t':
      ((X, X') :: Δ) ,, Γ ⊢ t ~ t' ->
      Δ ,, Γ ⊢ (Λ X K t) ~ (Λ X' K t')

  | A_Constant c :
      Δ ,, Γ ⊢ Constant c ~ Constant c

  | A_Builtin f :
      Δ ,, Γ ⊢ Builtin f ~ Builtin f

  | A_TyInst t T t' T' :
      Δ ⊢* T ~ T' ->
      Δ ,, Γ ⊢ t ~ t' ->
      Δ ,, Γ ⊢ TyInst t T ~ TyInst t' T'

  | A_Error T T' :
      Δ ⊢* T ~ T' ->
      Δ ,, Γ ⊢ Error T ~ Error T'

  | A_IWrap S S' T T' t t' :
      Δ ⊢* S ~ S' ->
      Δ ⊢* T ~ T' ->
      Δ ,, Γ ⊢ t ~ t' ->
      Δ ,, Γ ⊢ IWrap S T t ~ IWrap S' T' t'

  | A_Unwrap t t' :
      Δ ,, Γ ⊢ t ~ t' ->
      Δ ,, Γ ⊢ Unwrap t ~ Unwrap t'

  | A_Constr T i ts T' ts' :
      Δ ⊢* T ~ T' ->
      Forall2 (fun t t' => Δ ,, Γ ⊢ t ~ t') ts ts' ->
      Δ ,, Γ ⊢ Constr T i ts ~ Constr T' i ts'

  | A_Case T t ts T' t' ts' :
      Δ ⊢* T ~ T' ->
      Δ ,, Γ ⊢ t ~ t' ->
      Forall2 (fun t t' => Δ ,, Γ ⊢ t ~ t') ts ts' ->
      Δ ,, Γ ⊢ Case T t ts ~ Case T' t' ts'

  where "Δ ',,' Γ ⊢ s '~' t" := (alpha Δ Γ s t)

with alpha_binding
  (Δ : list (string * string))
  (Γ : list (string * string))
  : binding -> binding -> Prop :=

  | A_TermBind s x T t x' T' t' :
    Δ ,, ((x, x') :: Γ) ⊢ t ~ t' ->
    Δ ,, Γ ⊢b (TermBind s (VarDecl x T) t) ~ (TermBind s (VarDecl x' T') t')

  | A_TypeBind X K T X' T' :
    ((X, X') :: Δ) ⊢* T ~ T' ->
    Δ ,, Γ ⊢b (TypeBind (TyVarDecl X K) T) ~ (TypeBind (TyVarDecl X' K) T')

  (* TODO
  | A_DatatypeBind X K T X' T' :
    Δ ,, Γ ⊢b  ~
  *)

  where "Δ ',,' Γ ⊢b b '~' b'" := (alpha_binding Δ Γ b b')
.


Definition ctx_refl (xs : ctx) := Forall (fun '(x, y) => x = y) xs.

Lemma alpha_refl Δ Γ t :
  ctx_refl Δ ->
  ctx_refl Γ ->
  Δ ,, Γ ⊢ t ~ t.
Proof.
Admitted.


Inductive pair_sym : string * string -> string * string -> Prop :=
  | PS_pair x y : pair_sym (x, y) (y, x)
.
Definition ctx_sym (xs ys : ctx) : Prop := Forall2 pair_sym xs ys.

Lemma alpha_sym Δ Δ' Γ Γ' t t':
  ctx_sym Δ Δ' ->
  ctx_sym Γ Γ' ->
  Δ ,, Γ ⊢ t ~ t' ->
  Δ' ,, Γ' ⊢ t' ~ t.
Proof.
Admitted.
