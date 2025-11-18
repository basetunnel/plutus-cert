From PlutusCert Require Import
  PlutusIR
  Transform.Compat
.


Reserved Notation "t₁ ▷-unwrap t₂" (at level 30).

Inductive unwrap_cancel : term -> term -> Prop :=

  | uc_cancel : forall ty1 ty2 t t',
      t ▷-unwrap t' ->
      Unwrap (IWrap ty1 ty2 t) ▷-unwrap t'

  | uc_compat : forall t t',
      Compat unwrap_cancel t t' ->
      t ▷-unwrap t'

  where "t1 ▷-unwrap t2" := (unwrap_cancel t1 t2)
  .
