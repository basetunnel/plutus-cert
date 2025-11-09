(*

This version of dead code elimination:

  [x] removes empty lets
  [x] let rec
  [x] re-ordering bindings in let group
        (but this is not needed for the compiler spec)

implementation
  - uses Compat
  - uses pre-post conditions to ensure code was actually dead

This is the definition presented in the SCP paper

*)
From Coq Require Import
  Strings.String
  Lists.List
  Utf8_core
.

From Equations Require Import Equations.

From PlutusCert Require Import
  Util
  Util.List
  PlutusIR
  PlutusIR.Analysis.FreeVars
  PlutusIR.Analysis.Equality
  PlutusIR.Analysis.Purity
  PlutusIR.Analysis.WellScoped
  PlutusIR.Analysis.NoShadow
  PlutusIR.Transform.Compat
  PlutusIR.Semantics.Dynamic.Values
.

Import ListNotations.

Set Implicit Arguments.
Set Equations Transparent.




(* The primary name that is bound by the binding.
   Note: this is different than the variables bound by a binding (bvb), since
   DatatypeBind binds more names, but this  suffices for detecting whether
   a binding is removed
*)
Definition name (b : binding) :=
  match b with
    | TermBind s (VarDecl x _) t => x
    | TypeBind (TyVarDecl x _) ty => x
    | DatatypeBind (Datatype (TyVarDecl x _) _ _ _) => x
  end.


(* Whether *)
Definition name_removed b bs : Prop :=
  ¬ (In (name b) (map name bs)).

Inductive elim : term -> term -> Prop :=
  | elim_compat : forall t t',
      Compat elim t t' ->
      elim t t'

  | elim_delete_let : forall rec bs t t',
      elim t t' ->
      Forall (pure_binding []) bs ->
      elim (Let rec bs t) t'

  | elim_delete_bindings : forall rec bs bs' t t',
      elim t t' ->
      elim_bindings bs bs' ->
      elim (Let rec bs t) (Let rec bs' t')

with elim_bindings : list binding -> list binding -> Prop :=
  | elim_bindings_pure : forall bs bs',

      (* any removed binding is a pure binding *)
      (∀ b, In b bs ->
        name b ∉ map name bs' -> pure_binding [] b
      ) ->

      (* Any resulting binding has a (related) binding in the original group *)
      (∀ b', In b' bs' ->
         ∃ b, In b bs /\
           name b = name b' /\
           elim_binding b b'
      ) ->
      elim_bindings bs bs'

with elim_binding : binding -> binding -> Prop :=

  | elim_term_bind_compat : forall s vd t t',
      elim t t' ->
      elim_binding (TermBind s vd t) (TermBind s vd t')

  | elim_binding_refl : forall b,
      elim_binding b b
  .

Definition dead_code t t' :=
  no_shadow [] [] t /\
  elim t t' /\
  well_scoped [] [] t'.

Lemma elim_sym : forall t, elim t t.
Admitted.
