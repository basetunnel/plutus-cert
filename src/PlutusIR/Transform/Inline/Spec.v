Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import PeanoNat.

Import ListNotations.
From Equations Require Import Equations.
Require Import Program.
Require Import Lia.

From PlutusCert Require Import
  Util
  Util.List
  PlutusIR
  .


(*
Inlining considers:

  let nonrec Term bindings
  let Type bindings

The plutus compiler will _unconditionally_ inline, meaning that it will inline all occurences
and then remove the remaining dead binding.

We consider the more general case where some occurences may be inlined, but not others. As a consequence,
this pass does not consider binder elimination.

*)

(* Context of all let-bound term variables in scope *)

Inductive var_info :=
  | bound_LamAbs : var_info
  | bound_Constructor : var_info
  | bound_match : var_info
  | bound_TermBind : term -> var_info
.

Inductive tyvar_info :=
  | bound_TypeBind : ty -> tyvar_info
  | bound_TyAbs : tyvar_info

  | bound_Datatype_TyVar : tyvar_info
  | bound_Datatype : tyvar_info
  | bound_Forall : tyvar_info
  | bound_TyLam : tyvar_info
  .

Definition ctx := list (string * var_info).
Definition ty_ctx := list (string * tyvar_info).

Definition Binding_to_ctx (b : binding) : ctx :=
  match b with
    | TermBind _ (VarDecl v _) t => [(v, bound_TermBind t)]
    | DatatypeBind (Datatype _ _ mfunc cs) => (mfunc, bound_match) :: map (fun '(VarDecl x _) => (x, bound_Constructor)) cs
    | TypeBind _ _ => []
  end
.
Definition Binding_to_ty_ctx (b : binding) : ty_ctx :=
  match b with
    | TypeBind (TyVarDecl α _) τ => [(α, bound_TypeBind τ)]
    | TermBind _ _ _ => []
    | DatatypeBind (Datatype (TyVarDecl x _) _ _ _) => [(x, bound_Datatype)]
  end
.

Definition Bindings_to_ctx (bs : list binding) : ctx :=
  rev (concat (map Binding_to_ctx bs)).

Definition Bindings_to_ty_ctx (bs : list binding) : ty_ctx :=
  rev (concat (map Binding_to_ty_ctx bs)).

Local Open Scope list_scope.

Inductive inline_Ty (Δ : ty_ctx) : ty -> ty -> Prop :=

   | inl_Ty_Var_1 : forall α τ τ',
      Lookup α (bound_TypeBind τ) Δ ->
      inline_Ty Δ τ τ' ->
      inline_Ty Δ (Ty_Var α) τ

   | inl_Ty_Var_2 : forall α τ τ',
      Lookup α (bound_TypeBind τ) Δ -> (* See Note [Inlining and well-scopedness] *)
      inline_Ty Δ τ τ' ->
      inline_Ty Δ (Ty_Var α) (Ty_Var α)

   | inl_Ty_Fun : forall σ τ σ' τ',
      inline_Ty Δ σ σ' ->
      inline_Ty Δ τ τ' ->
      inline_Ty Δ (Ty_Fun σ τ) (Ty_Fun σ' τ')

   | inl_Ty_IFix : forall σ τ σ' τ',
      inline_Ty Δ σ σ' ->
      inline_Ty Δ τ τ' ->
      inline_Ty Δ (Ty_IFix σ τ) (Ty_IFix σ' τ')

   | inl_Ty_Forall : forall α k τ τ',
      inline_Ty ((α, bound_Forall) :: Δ) τ τ' ->
      inline_Ty Δ (Ty_Forall α k τ) (Ty_Forall α k τ')

   | inl_Ty_Builtin : forall t,
      inline_Ty Δ (Ty_Builtin t) (Ty_Builtin t)

   | inl_Ty_Lam : forall α k τ τ',
      inline_Ty Δ τ τ' ->
      inline_Ty Δ (Ty_Lam α k τ) (Ty_Lam α k τ')

   | Ty_App : forall σ τ σ' τ',
      inline_Ty Δ σ σ' ->
      inline_Ty Δ τ τ' ->
      inline_Ty Δ (Ty_App σ τ) (Ty_App σ' τ')
   .

(*
This relation relates terms where inlining of let-bound variables may
have taken place. Note that the PIR inliner may also remove the let binding
when all of its occurrences have been inlined (dead code). This is not taken into account here.


Note [Inline and well-scopedness]
~~~
The constructors inl_Var_2 requires that the variable must appear in Γ. This
ensures that Δ and Γ always contain the free variables of the related terms.
The inline relation implies well-scopedness of both pre- and post-term.

This makes it easier to prove semantics preservation: we need to reuse that fact
that substitution on a closed term is the identity.

*)
Inductive inline (Δ : ty_ctx) (Γ : ctx) : term -> term -> Prop :=
  | inl_Var_1 : forall v t_v,
      Lookup v (bound_TermBind t_v) Γ ->
      inline Δ Γ (Var v) t_v

  | inl_Var_2 : forall v info,
      Lookup v info Γ -> (* See Note [Inline and well-scopedness] *)
      inline Δ Γ (Var v) (Var v)

  | inl_Let_Rec : forall Γ_bs Δ_bs bs bs' t t',
      Γ_bs = Bindings_to_ctx bs ->
      Δ_bs = Bindings_to_ty_ctx bs ->
      inline_Bindings_Rec (Δ_bs ++ Δ) (Γ_bs ++ Γ) (Let Rec bs t) (Let Rec bs' t') ->
      inline Δ Γ (Let Rec bs t) (Let Rec bs' t')

  | inl_Let_NonRec : forall bs bs' t t',
      inline_Bindings_NonRec Δ Γ (Let NonRec bs t) (Let NonRec bs' t') ->
      inline Δ Γ (Let NonRec bs t) (Let NonRec bs' t')

  (* Compatibility cases *)
  | inl_TyInst_compat   : forall t t' τ τ',
      inline Δ Γ t t' ->
      inline_Ty Δ τ τ' ->
      inline Δ Γ (TyInst t τ) (TyInst t' τ')
  | inl_TyAbs    : forall α k t t',
      inline ((α, bound_TyAbs) :: Δ) Γ t t' ->
      inline Δ Γ (TyAbs α k t) (TyAbs α k t')
  | inl_LamAbs   : forall x τ τ' t t',
      inline Δ ((x, bound_LamAbs) :: Γ) t t' ->
      inline_Ty Δ τ τ' ->
      inline Δ Γ (LamAbs x τ t) (LamAbs x τ' t')
  | inl_Apply    : forall s s' t t',
      inline Δ Γ s s' ->
      inline Δ Γ t t' ->
      inline Δ Γ (Apply s t) (Apply s' t')
  | inl_Constant : forall c,
      inline Δ Γ (Constant c) (Constant c)
  | inl_Builtin  : forall f,
      inline Δ Γ (Builtin f) (Builtin f)
  | inl_Error    : forall τ τ',
      inline Δ Γ (Error τ) (Error τ')
  | inl_IWrap    : forall σ σ' τ τ' t t',
      inline_Ty Δ τ τ' ->
      inline_Ty Δ σ σ' ->
      inline Δ Γ (IWrap σ τ t) (IWrap σ' τ' t')
  | inl_Unwrap   : forall t t',
      inline Δ Γ (Unwrap t) (Unwrap t')

  (* We closely follow the structure of eval so the semantic proof lines up
     more easily *)
  with inline_Bindings_NonRec (Δ : ty_ctx) (Γ : ctx) : term -> term -> Prop :=

  | inl_Binding_NonRec_cons : forall b b' bs bs' t t',
      inline_Binding Δ Γ b b' ->
      inline_Bindings_NonRec (Binding_to_ty_ctx b ++ Δ) (Binding_to_ctx b ++ Γ)
        (Let NonRec bs t)
        (Let NonRec bs' t') ->
      inline_Bindings_NonRec Δ Γ
        (Let NonRec (b :: bs) t)
        (Let NonRec (b' :: bs') t')

  | inl_Binding_NonRec_nil  : forall t t',
      inline Δ Γ t t' ->
      inline_Bindings_NonRec Δ Γ (Let NonRec [] t) (Let NonRec [] t')

  with inline_Bindings_Rec (Δ : ty_ctx) (Γ : ctx) : term -> term -> Prop :=

    | inl_Binding_Rec_cons : forall b b' bs bs' t t',
        inline_Binding Δ Γ b b' ->
        inline_Bindings_Rec Δ Γ (Let Rec bs t) (Let Rec bs' t') ->
        inline_Bindings_Rec Δ Γ (Let Rec (b :: bs) t) (Let Rec (b' :: bs') t')

    | inl_Binding_Rec_nil : forall t t',
        inline Δ Γ t t' ->
        inline_Bindings_Rec Δ Γ (Let Rec [] t) (Let Rec [] t')

with inline_Binding (Δ : ty_ctx) (Γ : ctx) : binding -> binding -> Prop :=

  | inl_TermBind  : forall s x τ τ' tb tb',
      inline Δ Γ tb tb' -> (* Δ and Γ need not be extended, in case of LetRec, x is already in Γ, otherwise it is not in scope *)
      inline_Binding Δ Γ
        (TermBind s (VarDecl x τ) tb)
        (TermBind s (VarDecl x τ') tb')

  | inl_DatatypeBind_NonRec : forall d,
      (* TODO: add bindings and inline_Ty premises, should probably distinguish
      * between Rec and NonRec binding *)
      inline_Binding Δ Γ (DatatypeBind d) (DatatypeBind d)

  | inl_TypeBind_NonRec : forall tvd τ τ',
      inline_Ty Δ τ τ' -> (* Cannot be recursive *)
      inline_Binding Δ Γ (TypeBind tvd τ) (TypeBind tvd τ')
.
