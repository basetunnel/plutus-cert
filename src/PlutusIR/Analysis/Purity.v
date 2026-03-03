From Coq Require Import
  Strings.String
  Lists.List
.

From PlutusCert Require Import
  PlutusIR
  Semantics.Dynamic.Values
  Semantics.Static.Auxiliary
  Util.List
  Util
  Analysis.BoundVars
  .

Import ListNotations.

Open Scope bool_scope.

Inductive binder_info :=
  | let_bound : strictness -> binder_info
  | lambda_bound
.


(* The following is the old version, which does not state the property over the
 * whole term *)

Definition ctx := list (string * binder_info).

(* Pure terms include values or variables that are known to be bound to values *)
Inductive is_pure (Γ : ctx) : term -> Type :=

  | is_pure_result : forall t,
      result t ->
      ~(is_error t) ->
      is_pure Γ t

  | is_pure_var_let : forall x,
      Lookup x (let_bound Strict) Γ ->
      is_pure Γ (Var x)

  | is_pure_var_lambda : forall x,
      Lookup x lambda_bound Γ ->
      is_pure Γ (Var x)
.


Lemma dec_is_error_not_is_error : forall t,
  is_error_beq t = false -> ~ is_error t.
Proof.
  intros t H.
  destruct t; intros H1; inversion H1.
  inversion H.
Qed.


Definition is_pureb (Γ : ctx) (t : term) : bool :=
  match t with
  | Var x =>
    match lookup x Γ with
      | Datatypes.Some lambda_bound => true
      | Datatypes.Some (let_bound Strict) => true
      | Datatypes.Some (let_bound NonStrict) => false
      | _ => false
    end
  | _     => if result_dec t then true else false && negb (is_error_beq t)
  end
.

(* An approximation of bindings that are pure, they will not diverge when evaluated *)
Inductive pure_binding (Γ : ctx) : binding -> Prop :=

  | pb_term_non_strict : forall vd t,
      pure_binding Γ (TermBind NonStrict vd t)

  | pb_term_strict_val : forall vd t,
      is_pure Γ t ->
      pure_binding Γ (TermBind Strict vd t)

  | pb_data : forall dtd,
      pure_binding Γ (DatatypeBind dtd)

  | pb_type : forall tvd ty,
      pure_binding Γ (TypeBind tvd ty)
.

Definition dec_pure_binding (Γ : ctx) (b : binding) : bool :=
    match b with
      | TermBind NonStrict vd t => true
      | TermBind Strict vd t    => result_beq t
      | DatatypeBind dtd        => true
      | TypeBind tvd ty         => true
    end
.

Lemma sound_dec_pure_binding : forall Γ b, dec_pure_binding Γ b = true -> pure_binding Γ b.
Admitted.

Module Analysis.

(* Experimental relation to approximate purity of terms. Considers more terms
 * and maintains the environment.
*)

Inductive purity := pure | unknown | impure.

Definition min : purity -> purity -> purity :=
  fun x y => match x , y with
  | impure , _ => impure
  | unknown , impure => impure
  | unknown , _ => unknown
  | pure , pure => pure
  | pure , p => p
  end.

Fixpoint minimum (xs : list purity) : purity :=
  match xs with
  | x :: xs => min x (minimum xs)
  | [] => pure
  end.

Definition env := list (string * purity).

Section Relation.

Context
  {Γ Γ' : env}
  {s t : term}
  {bs : list binding}
  {p : purity}
  {x X : string}
  {T : ty}
  {K : kind}
  {c : constant}
  {f : DefaultFun}
.

(* WIP, given a purity environment, approximate if a term is pure *)
Inductive has_purity : env -> term -> purity -> Type :=
  | P_TyAbs :
      has_purity Γ (TyAbs X K t) pure

  (* Pure, regardless of its body *)
  | P_LamAbs :
      has_purity Γ (LamAbs x T t) pure

  | P_Constant :
      has_purity Γ (Constant c) pure

  | P_Let :
      bindings_has_purity Γ bs Γ' ->
      has_purity (Γ' ++ Γ) t p ->
      has_purity Γ (Let NonRec bs t) (minimum (p :: map snd Γ))

  (* Conservative about letrec (purity unknown), unclear how to deal with
   * e.g. letrec !x = x in x
   * which is not pure
   *)
  | P_LetRec :
      has_purity Γ (Let Rec bs t) unknown

  | P_Var :
      lookup x Γ = Some p ->
      has_purity Γ (Var x) p


  | P_Apply :
      has_purity Γ (Apply s t) unknown

  | P_Builtin  :
      has_purity Γ (Builtin f) unknown

  (*
  | P_
  | P_TyInst   : term -> ty -> term
  | P_Error    : ty -> term
  | P_IWrap    : ty -> ty -> term -> term
  | P_Unwrap   : term -> term
  | P_Constr   : ty -> nat -> list term -> term
  | P_Case     : ty -> term -> list term -> term
  *)
with

  (* The purity of all bound (term) variables in a binding *)
  binding_has_purity : env -> binding -> env -> Type :=

  | P_TermBind_Strict : forall {Γ x T t p},
      has_purity Γ t p ->
      binding_has_purity Γ (TermBind Strict (VarDecl x T) t) [(x, p)]

  (* Non-strict bindings are always pure *)
  | P_TermBind_NonStrict : forall {Γ x T t p},
      binding_has_purity Γ (TermBind NonStrict (VarDecl x T) t) [(x, p)]

  | P_TypeBind : forall {Γ tvd T},
      binding_has_purity Γ (TypeBind tvd T) []

  (* Constructors and destructors are always pure *)
  | P_DatatypeBind : forall {Γ d},
      binding_has_purity Γ (DatatypeBind d)
        (map (fun x => (x, pure)) (bvb (DatatypeBind d)))
with
  bindings_has_purity : env -> list binding -> env -> Prop :=
  | bte_nil : bindings_has_purity [] [] []

  | bte_cons : forall {b bs Γ Γs},
      binding_has_purity Γ b Γ ->
      bindings_has_purity Γ bs Γs ->
      bindings_has_purity Γ (b :: bs) (Γs ++ Γ) (* ++ Γ results in a reversed env, to match binding order of a Let *)
.

End Relation.

End Analysis.
