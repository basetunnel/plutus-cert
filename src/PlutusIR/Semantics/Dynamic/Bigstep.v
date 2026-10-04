Require Import PlutusCert.PlutusIR.
Import PlutusNotations.
Require Export PlutusCert.PlutusIR.Semantics.Static.Builtins.Arity.
Require Export PlutusCert.PlutusIR.Semantics.Dynamic.Builtins.
Require Export PlutusCert.PlutusIR.Semantics.Dynamic.AnnotationSubstitution.
Require Export PlutusCert.PlutusIR.Semantics.Dynamic.Datatypes.
Require Export PlutusCert.PlutusIR.Semantics.Dynamic.Substitution.
Require Export PlutusCert.PlutusIR.Semantics.Dynamic.Values.

Require Import Arith.
Local Open Scope nat_scope.

Require Import Lists.List.
Import ListNotations.
(** * Big-step operational semantics *)

(** ** Implementation of big-step semantics as an inductive datatype *)
Reserved Notation "t '=[' j ']=>' v"(at level 40).
Reserved Notation "t '=η=>' v"(at level 40).
Reserved Notation "t '=[' j ']=>nr' v"(at level 40).
Reserved Notation "t '=[' j ']=>r' v 'WITH' bs0"(at level 40).

(* Make bindings non-strict so they can be used in strict let-rec
 *)
Inductive bindings_nonstrict : list binding -> list binding -> Prop :=
  | BNS_nil :
      bindings_nonstrict [] []
  | BNS_cons s vd t bs bs' :
      bindings_nonstrict bs bs' ->
      bindings_nonstrict (TermBind s vd t :: bs) (TermBind NonStrict vd t :: bs')
.

Inductive eval : term -> term -> nat -> Prop :=
  | E_LamAbs : forall j x T t,
      j = 0 ->
      LamAbs x T t =[j]=> LamAbs x T t
  | E_Apply : forall j t1 t2 x T t0 v2 v0 j1 j2 j0,
      j = j1 + j2 + 1 + j0 ->
      t1 =[j1]=> LamAbs x T t0 ->
      t2 =[j2]=> v2 ->
      ~ is_error v2 ->
      <{ [x := v2 ] t0 }> =[j0]=> v0 ->
      Apply t1 t2 =[j]=> v0
  (** Universal types *)
  | E_TyAbs : forall j X K t,
      j = 0 ->
      TyAbs X K t =[j]=> TyAbs X K t
  | E_TyInst : forall j t1 T2 X K t0 v0 j1 j0,
      j = j1 + 1 + j0 ->
      t1 =[j1]=> TyAbs X K t0 ->
      <{ :[X := T2] t0 }> =[j0]=> v0 ->
      TyInst t1 T2 =[j]=> v0
  (** Recursive types *)
  | E_IWrap : forall F T t0 v0 j0,
      t0 =[j0]=> v0 ->
      ~ is_error v0 ->
      IWrap F T t0 =[j0]=> IWrap F T v0
  | E_Unwrap : forall j t0 F T v0 j0,
      j = j0 + 1 ->
      t0 =[j0]=> IWrap F T v0 ->
      Unwrap t0 =[j]=> v0
  (** Constants *)
  | E_Constant : forall j a,
      j = 0 ->
      Constant a =[j]=> Constant a
  (** Constructors *)
  | E_Constr_nil : forall j i T,
      j = 0 ->
      Constr T i nil =[j]=> Constr T i nil
  | E_Constr_cons : forall j i T k_t k_ts t ts v vs,
      j = k_t + k_ts ->
      t =[k_t]=> v ->
      ~ is_error v ->
      Constr T i ts =[k_ts]=> Constr T i vs ->
      Constr T i (t :: ts) =[j]=> Constr T i (v :: vs)

  (** Builtins: partial application *)
  | E_Builtin j f :
      j = 0 ->
      arity f > 0 ->
      Builtin f =[j]=> Builtin f
  | E_Apply_Builtin_Partial : forall j f s t vb v j0 j1,
      j = j0 + j1 ->
      s =[j0]=> vb ->
      applied f vb ->
      t =[j1]=> v ->
      value v ->
      args_len (Apply vb v) < arity f ->
      Apply s t =[j]=> Apply vb v
  | E_TyInst_Builtin_Partial : forall t T j0 f vb,
      t =[j0]=> vb ->
      applied f vb ->
      args_len (TyInst vb T) < arity f -> (* Applying to one more argument is still a partial application *)
      TyInst t T =[j0]=> TyInst vb T

  (* Builtins fully applied *)
  | E_Apply_Builtin_Full : forall j f s t vb v j0 j1 r,
      j = j0 + j1 + 1 ->
      s =[j0]=> vb ->
      applied f vb ->
      t =[j1]=> v ->
      value v ->
      args_len (Apply vb v) = arity f ->
      r = eval_builtin (Apply vb v) ->
      Apply s t =[j]=> r
  | E_TyInst_Builtin_Full : forall j t T f vb j0 r,
      j = j0 + 1 ->
      t =[j0]=> vb ->
      applied f vb ->
      args_len (TyInst vb T) = arity f ->
      r = eval_builtin (TyInst vb T) ->
      TyInst t T =[j]=> r

  (* Errors and their propagation *)
  | E_Error : forall j T,
      j = 0 ->
      Error T =[j]=> Error T
  | E_Error_Apply1 : forall j t1 t2 j1 T,
      j = j1 + 1 ->
      t1 =[j1]=> Error T ->
      Apply t1 t2 =[j]=> Error T
  | E_Error_Apply2 : forall j t1 t2 j2 T,
      j = j2 + 1 ->
      t2 =[j2]=> Error T ->
      Apply t1 t2 =[j]=> Error T
  | E_Error_TyInst : forall j t1 T2 j1 T,
      j = j1 + 1 ->
      t1 =[j1]=> Error T ->
      TyInst t1 T2 =[j]=> Error T
  | E_Error_IWrap : forall j F T t0 j0 T',
      j = j0 + 1 ->
      t0 =[j0]=> Error T' ->
      IWrap F T t0 =[j]=> Error T'
  | E_Error_Unwrap : forall j t0 j0 T,
      j = j0 + 1 ->
      t0 =[j0]=> Error T ->
      Unwrap t0 =[j]=> Error T
  | E_Constr_Error : forall j i T k_t k_ts t ts T',
      j = k_t + k_ts ->
      t =[k_t]=> Error T' ->
      Constr T i (t :: ts) =[j]=> Error T'

  (** let (non-recursive)*)
  | E_Let : forall bs t v j,
      Let NonRec bs t =[j]=>nr v ->
      Let NonRec bs t =[j]=> v

  (* letrec (terms)
   * ------
   * Strict bindings need to evaluate with the rest of the let-bindings treated
   * as non-strict. Therefore we pass a list of bindings that are
   * non-strictified
   * TODO: find out how the compilation of mutually recursive strict terms
   * exactly works in Plutus
   *)
  | E_LetRec : forall bs bs' t v j ,
      bindings_nonstrict bs bs' ->
      Let Rec bs t =[j]=>r v WITH bs' ->
      Let Rec bs t =[j]=> v

  (* letrec (data)
   * Plutus does not allow mutually recursive ADTs, so we can require there is
   * only one binding in the let group.
   *)
  | E_LetRec_Data : forall j dtd X K tvds matchf cs t ty t_match t_cs v j0 ,
      j = j0 + 1 ->
      dtd = Datatype (TyVarDecl X K) tvds matchf cs ->
      (ty, t_match, t_cs) = compile_data Rec dtd ->

      (substA X ty
        (msubst t_cs
          (subst matchf t_match
            t))) =[j]=> v ->
      Let Rec [DatatypeBind dtd] t =[j]=> v


with eval_bindings_nonrec : term -> term -> nat -> Prop :=
  | E_Let_Nil : forall j t0 v0 j0,
      j = j0 + 1 ->
      t0 =[j0]=> v0 ->
      Let NonRec nil t0 =[ j ]=>nr v0
  | E_Let_TermBind_Strict : forall j x T t1 j1 v1 j2 v2 bs t0,
      j = j1 + 1 + j2 ->
      t1 =[j1]=> v1 ->
      ~ is_error v1 ->
      <{ [x := v1] ({Let NonRec bs t0}) }> =[j2]=>nr v2 ->
      Let NonRec ((TermBind Strict (VarDecl x T) t1) :: bs) t0 =[j]=>nr v2
  | E_Let_DatatypeBind : forall j dtd X K tvds matchf X_ty matchf_term cs_subst cs bs t i v,
      j = i + 1 ->

      dtd = Datatype (TyVarDecl X K) tvds matchf cs ->
      (X_ty, matchf_term, cs_subst) = compile_data NonRec dtd ->

      (substA X X_ty
        (msubst cs_subst
          (subst matchf matchf_term
            (Let NonRec bs t)))) =[i]=> v ->
      (*-----------------------------------------*)
      Let NonRec (DatatypeBind dtd :: bs) t =[j]=>nr v

  | E_Let_TypeBind : forall j X K T bs t0 j1 v1,
      j = j1 + 1 ->
      <{ :[X := T] ({Let NonRec bs t0}) }> =[j1]=> v1 ->
      Let NonRec ((TypeBind (TyVarDecl X K) T) :: bs) t0 =[j]=>nr v1
  (* Error propagation *)
  | E_Error_Let_TermBind : forall j x T t1 j1 T' bs t0,
      j = j1 + 1 ->
      t1 =[j1]=> Error T' ->
      Let NonRec ((TermBind Strict (VarDecl x T) t1) :: bs) t0 =[j]=>nr Error T'


with eval_bindings_rec : list binding -> term -> term -> nat -> Prop :=
  | E_LetRec_Nil : forall j bs0 t0 v0 j0,
      j = j0 + 1 ->
      t0 =[j0]=> v0 ->
      Let Rec nil t0 =[j]=>r v0 WITH bs0

  | E_LetRec_TermBind_NonStrict : forall j bs0 x T bs t0 t1 v1 j1,
      j = j1 + 1 ->
      <{ [ x := {Let Rec bs0 t1}] {Let Rec bs t0} }> =[j1]=>r v1 WITH bs0 ->
      Let Rec ((TermBind NonStrict (VarDecl x T) t1) :: bs) t0 =[j]=>r v1 WITH bs0

  | E_LetRec_TermBind_Strict : forall j bs0 x T bs t0 t1 v1 v2 j1 j2,
      j = j2 + 1 ->
      Let Rec bs0 t0 =[j1]=> v1 ->
      ~ is_error v1 ->
      <{ [ x := v1] {Let Rec bs t0} }> =[j2]=>r v2 WITH bs0 ->
      Let Rec ((TermBind Strict (VarDecl x T) t1) :: bs) t0 =[j]=>r v2 WITH bs0

where "t '=[' j ']=>' v" := (eval t v j)
and "t '=[' j ']=>nr' v" := (eval_bindings_nonrec t v j)
and "t '=[' j ']=>r' v 'WITH' bs0" := (eval_bindings_rec bs0 t v j).

Scheme eval__ind := Minimality for eval Sort Prop
  with eval_bindings_nonrec__ind := Minimality for eval_bindings_nonrec Sort Prop
  with eval_bindings_rec__ind := Minimality for eval_bindings_rec Sort Prop.

Combined Scheme eval__multind from
  eval__ind,
  eval_bindings_nonrec__ind,
  eval_bindings_rec__ind.

Create HintDb hintdb__eval_no_error.

#[export] Hint Resolve
  E_LamAbs
  E_Apply
  E_TyAbs
  E_TyInst
  E_IWrap
  E_Unwrap
  E_Constant
  E_Builtin
  E_Apply_Builtin_Partial
  E_TyInst_Builtin_Partial
  E_Apply_Builtin_Full
  E_TyInst_Builtin_Full
  E_Let
  E_LetRec
  E_Let_Nil
  E_Let_DatatypeBind
  E_Let_TermBind_Strict
  E_Let_TypeBind
  E_LetRec_Nil
  E_LetRec_TermBind_NonStrict
  : hintdb__eval_no_error.

Create HintDb hintdb__eval_with_error.

#[export] Hint Constructors
  eval
  eval_bindings_nonrec
  eval_bindings_rec
  : hintdb__eval_with_error.


Definition terminates t := exists v j, t =[ j ]=> v.
Notation "t '⇓'" := (terminates t) (at level 101).
