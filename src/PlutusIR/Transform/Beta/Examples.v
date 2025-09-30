From Coq Require Import
  Lists.List
  Strings.String.
From PlutusCert Require Import
  PlutusIR
  Compat
  LetMergeNR
  Beta.Spec
  Beta.Dec
.

Import ListNotations.
Open Scope string.

Definition ty_unit := (Ty_Builtin DefaultUniUnit).
Definition lam x t := LamAbs x ty_unit t.
Definition unit := (Constant (ValueOf DefaultUniUnit tt)).

Definition s :=
  Apply
    (Apply
      (lam "x"
        (lam "y" (Var "x"))
      )
      unit
    )
    unit
.

Definition s' :=
  Let NonRec
    [ TermBind Strict (VarDecl "x" ty_unit) unit;
      TermBind Strict (VarDecl "y" ty_unit) unit
    ]
    (Var "x")
.


Goal betas [] (split s) (split s').
  simpl.
  apply beta_Apply.
  apply beta_Apply.
  apply beta_LamAbs.
  apply beta_LamAbs;
  repeat constructor. (* Why does auto using betas, Compat not work? *)
  repeat constructor.
  constructor.
  simpl. intro. assumption.
  constructor.
Qed.

Goal dec [] (split s) (split s') = true.
Proof.
  reflexivity.
Qed.

Import PIRNotations.
Import ListNotations.
Open Scope pir_scope.

Definition u := (Λ "X" ★ unit) @ ty_unit.

Definition v :=
  let_
    [type ("X" :* ★) = ty_unit]
    unit
.

Goal betas [] u v.
  apply beta_TyInst_TyAbs.
  repeat constructor. (* Why does auto using betas, Compat not work? *)
Qed.

Goal dec [] u v = true.
simpl.
reflexivity.
Qed.

(* Multi type lets is not allowed *)
Definition w :=
  (Λ "X" ★ (λ "y" (Ty_Var "X") `"y")) @ ty_unit ⋅ unit.

Definition x :=
  let_
    [type "X" :* ★ = ty_unit]
    let_
      ["y" : (Ty_Var "X") != unit]
      `"y"
.

Unset Printing Notations.

Goal betas [] w x.
  unfold w, x.
  constructor.
  Fail constructor.
Abort.

Goal dec [] w x = false.
reflexivity.
Qed.
