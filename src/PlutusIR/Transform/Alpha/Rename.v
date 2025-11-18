From Coq Require Import
  String
  Lists.List
  .
From PlutusCert Require Import
  Util
  Util.List
  Transform.Compat
  Analysis.FreeVars
  AFI
  .
From PlutusCert Require Import
  PlutusIR
  .

Import ListNotations.
Import AFI.

(* Rename context*)
Definition ctx := list (string * string).


(* Note [Renaming Translation Relation]

When renaming variables, it is crucial to avoid capturing/shadowing:

  λ x . λ y . x + y
       ̸▷
  λ z . λ z . z + z

When defining a renaming, we therefore need to consider the free variables in a
term. In the translation relation we keep track of free variables using contexts
Δ and Γ (for type- and term-level variables respectively). This means that only
closed terms can be related at the top-level, as there is no rule that relates
free variables that do not occur in Γ or Δ.

Suppose we have these two terms:

  pre-term:  (λ x. t)
  post-term: (λ z. t[z/x])

as well as a context Γ with all free term variables in t. This is valid if no
free variable in Γ is being renamed to z.

We can loosen that condition: x can be safely renamed to z if for any other (y,
z) in Γ, there are no occurrences of y in the pre-term. That way, we allow some safe
forms of shadowing. For example:

  λ x . map (\y -> y + 1) x
    ▷
  λ z . map (\z -> z + 1) z

*)


(* A variable name x is safe (usable for renaming), when it does not capture free
** variables in the pre-term. However, since those free variables may have other
** names in the post-term, we need to take into account the context Γ (or Δ).
*)
Definition safe_var x (Γ : ctx) t_pre :=
  forall z, In (z, x) Γ -> ~ AFI.Term.appears_free_in z t_pre.

Definition safe_tyvarA α (Δ : ctx) t_pre :=
  forall β, In (β, α) Δ -> ~ AFI.Annotation.appears_free_in β t_pre.

Definition safe_tyvar α (Δ : ctx) τ_pre :=
  forall β, In (β, α) Δ -> ~ AFI.Ty.appears_free_in β τ_pre.


Inductive rename_tvs (Δ : ctx) (cs : list vdecl) : list tvdecl -> list tvdecl -> ctx -> Prop :=

  | rn_tvs_nil :
      rename_tvs Δ cs [] [] []

  | rn_tvs_cons : forall α tvs k β tvs' Δ_tvs,
      (* check that the bound tyvar does not capture other renamed vars in the
         type signatures of the constructors *)
      Forall (fun '(VarDecl _ cty) => safe_tyvar β Δ cty) cs ->
      rename_tvs ((α, β) :: Δ) cs tvs tvs' Δ_tvs ->
      rename_tvs Δ cs (TyVarDecl α k :: tvs) (TyVarDecl β k :: tvs') ((α, β) :: Δ_tvs)
.

Inductive rename_ty (Δ : ctx) : ty -> ty -> Prop :=


   (* Note: it is important to use lookup, not In, since only the most recently
      bound variable can be renamed *)
   | rn_Ty_Var : forall α α',
      lookup α Δ = Some α' ->
      rename_ty Δ (Ty_Var α) (Ty_Var α')

   | rn_Ty_Fun : forall σ τ σ' τ',
      rename_ty Δ σ σ' ->
      rename_ty Δ τ τ' ->
      rename_ty Δ (Ty_Fun σ τ) (Ty_Fun σ' τ')

   | rn_Ty_IFix : forall σ τ σ' τ',
      rename_ty Δ σ σ' ->
      rename_ty Δ τ τ' ->
      rename_ty Δ (Ty_IFix σ τ) (Ty_IFix σ' τ')

   | rn_Ty_Forall : forall α α' k τ τ',
      rename_ty ((α, α') :: Δ) τ τ' ->
      safe_tyvar α Δ τ ->
      rename_ty Δ (Ty_Forall α k τ) (Ty_Forall α' k τ')

   | rn_Ty_Builtin : forall t,
      rename_ty Δ (Ty_Builtin t) (Ty_Builtin t)

   | rn_Ty_Lam : forall α α' k τ τ',
      rename_ty ((α, α') :: Δ) τ τ' ->
      safe_tyvar α Δ τ ->
      rename_ty Δ (Ty_Lam α k τ) (Ty_Lam α' k τ')

   | Ty_App : forall σ τ σ' τ',
      rename_ty Δ σ σ' ->
      rename_ty Δ τ τ' ->
      rename_ty Δ (Ty_App σ τ) (Ty_App σ' τ')
.

Inductive rename (Δ Γ: ctx) : term -> term -> Prop :=
  | rn_Var : forall x x',
      lookup x Γ = Some x' ->
      rename Δ Γ (Var x) (Var x')

  | rn_Let_Rec : forall bs bs' t t',
      forall Γ_bs Δ_bs,
      rename_bindings_Rec (Δ_bs ++ Δ) (Γ_bs ++ Γ) Δ_bs Γ_bs bs bs' ->
      rename (Δ_bs ++ Δ) (Γ_bs ++ Γ) t t' ->

      (* All bound type- and term variables in the bindings should not capture _in the body_.

         Alternatively, this could have been implemented by adding `Let NonRec bs t` as
         an index in rename_binding and putting a simple safe_var at the actual binding *)
      Forall (fun '(_, x') => safe_var x' Γ t) Γ_bs ->
      Forall (fun '(_, α') => safe_tyvarA α' Δ t) Δ_bs ->

      (* All bound (type) variables have to be unique in the binding group *)
      NoDup (bvbs bs') ->
      NoDup (btvbs bs') ->

      rename Δ Γ (Let Rec bs t) (Let Rec bs' t')

  (* If the decision procedure becomes problematic because of not structurally smaller terms,
     these two rules should be refactored into a relation similar to rename_bindings_Rec *)
  | rn_Let_NonRec_nil : forall t t',
      rename Δ Γ t t' ->
      rename Δ Γ (Let NonRec [] t) (Let NonRec [] t')

  | rn_Let_NonRec_cons : forall Γ_b Δ_b b b' bs bs' t t',
      rename_binding Δ Γ Γ_b Δ_b b b' ->
      rename (Δ_b ++ Δ) (Γ_b ++ Γ) (Let NonRec bs t) (Let NonRec bs' t') ->

      (* All bound (type) variables in the let should not capture.

         Alternatively, add `Let NonRec bs t` as index in rename_binding
         and put a simple safe_var at the actual binding *)
      Forall (fun '(_, x') => safe_var x' Γ (Let NonRec bs t)) Γ_b ->
      Forall (fun '(_, α') => safe_tyvarA α' Δ (Let NonRec bs t)) Δ_b ->

      rename Δ Γ (Let NonRec (b :: bs) t) (Let NonRec (b' :: bs') t')

  | rn_TyAbs : forall α α' k t t',
      rename ((α, α') :: Δ) Γ t t' ->
      safe_tyvarA α' Δ t ->
      rename Δ Γ (TyAbs α k t) (TyAbs α' k t')

  | rn_LamAbs : forall x x' τ τ' t t',
      rename_ty Δ τ τ' ->
      rename Δ ((x, x') :: Γ) t t' ->
      safe_var x' Γ t ->
      rename Δ Γ (LamAbs x τ t) (LamAbs x' τ' t')

  | rn_Apply : forall s t s' t',
      rename Δ Γ s s' ->
      rename Δ Γ t t' ->
      rename Δ Γ (Apply s t) (Apply s' t')

  | rn_Constant : forall c,
      rename Δ Γ (Constant c) (Constant c)

  | rn_Builtin : forall b,
      rename Δ Γ (Builtin b) (Builtin b)

  | rn_TyInst : forall t t' τ τ',
      rename Δ Γ t t' ->
      rename_ty Δ τ τ' ->
      rename Δ Γ (TyInst t τ) (TyInst t' τ')

  | rn_Error : forall τ τ',
      rename_ty Δ τ τ' ->
      rename Δ Γ (Error τ) (Error τ')

  | rn_IWrap σ τ σ' τ' t t':
      rename_ty Δ σ σ' ->
      rename_ty Δ τ τ' ->
      rename Δ Γ t t' ->
      rename Δ Γ (IWrap σ τ t) (IWrap σ' τ' t')

  | rn_Unwrap : forall t t',
      rename Δ Γ t t' ->
      rename Δ Γ (Unwrap t) (Unwrap t')

with rename_binding (Δ Γ : ctx) : ctx -> ctx -> binding -> binding -> Prop :=

  | rn_TermBind : forall s x x' τ τ' t t',
      rename_ty Δ τ τ' ->
      rename Δ Γ t t' ->
      rename_binding Δ Γ [(x, x')] [] (TermBind s (VarDecl x τ) t) (TermBind s (VarDecl x' τ') t')

  | rn_TypeBind : forall α α' k τ τ',
      rename_ty Δ τ τ' ->
      rename_binding Δ Γ [] [(α, α')] (TypeBind (TyVarDecl α k) τ) (TypeBind (TyVarDecl α' k) τ')

  | rn_DatatypeBind : forall α α' k tvs tvs' elim elim' cs cs',
      forall Δ_tvs Γ_cs Γ_b Δ_b,

      (* Renamings of bound ty-vars, which may be used in constructor types *)
      rename_tvs Δ cs' tvs tvs' Δ_tvs ->
      (* Constructor types are renamed and return any renamed constructor names *)
      rename_constrs ((α, α') :: Δ_tvs ++ Δ) Γ cs cs' Γ_cs ->

      (* Renamings for the rest of the program *)
      Γ_b = (elim, elim') :: Γ_cs ->
      Δ_b = [(α, α')] ->


      rename_binding Δ Γ Γ_b Δ_b
        (DatatypeBind (Datatype (TyVarDecl α k) tvs elim cs))
        (DatatypeBind (Datatype (TyVarDecl α' k) tvs' elim' cs'))

(*
  rename_bindings_Rec is also indexed over contexts Γ_bs, Δ_bs, which are respectively
  the bound term and type variables of the recursive bindings.
*)
with rename_bindings_Rec (Δ Γ : ctx) : ctx -> ctx -> list binding -> list binding -> Prop :=

  | rn_Bindings_Rec_nil :
      rename_bindings_Rec Δ Γ [] [] [] []

  | rn_Bindings_Rec_cons : forall b b' bs bs',
      forall Δ_b Δ_bs Γ_b Γ_bs,
      rename_binding Δ Γ Δ_b Γ_b b b' ->
      rename_bindings_Rec Δ Γ Δ_bs Γ_bs bs bs' ->
      rename_bindings_Rec Δ Γ (Δ_b ++ Δ_bs) (Γ_b ++ Γ_bs) (b :: bs) (b' :: bs')

(*
  rename_constrs is also indexed over context Γ_cs, which are
  the renamings of the constructors
*)
with rename_constrs (Δ Γ : ctx) : list vdecl -> list vdecl -> ctx -> Prop :=

  | rn_constrs_nil :
      rename_constrs Δ Γ [] [] []

  | rn_constrs_cons : forall x x' τ τ' cs cs' Γ_cs,
      rename_ty Δ τ τ' ->
      rename_constrs Δ Γ cs cs' Γ_cs ->
      rename_constrs Δ Γ
        (VarDecl x τ :: cs)
        (VarDecl x' τ' :: cs')
        ((x, x') :: Γ_cs)
  .

Scheme rename__ind := Minimality for rename Sort Prop
  with rename_constrs__ind := Minimality for rename_constrs Sort Prop
  with rename_bindings_Rec__ind := Minimality for rename_bindings_Rec Sort Prop
  with rename_binding__ind := Minimality for rename_binding Sort Prop
.

Combined Scheme rename__multind from
  rename__ind,
  rename_constrs__ind,
  rename_bindings_Rec__ind,
  rename_binding__ind
.

(* MetaCoq Run (run_print_rules rename). *)

From PlutusCert Require Import Dynamic.Substitution.
From PlutusCert Require Import Dynamic.Bigstep.

Require Import PlutusCert.PlutusIR.
Import PlutusNotations.

(* safe_var facts *)

Lemma safe_var__subst x Γ v y t :
  closed v ->
  safe_var x Γ <{ [y := v] t }>
.
Admitted.

Lemma safe_tyvarA__subst α Γ v y t :
  closed v ->
  safe_tyvarA α Γ <{ [y := v] t }>
.
Admitted.


(* rename facts *)

Lemma rename_closed_l t t' : rename [] [] t t' -> closed t.
Admitted.

Lemma rename_closed_r t t' : rename [] [] t t' -> closed t.
Admitted.

Lemma rename_is_error {Δ Γ v v'} : rename Δ Γ v v' -> is_error v <-> is_error v'.
Admitted.

Notation "Γ '|--' x '~>' y" := (@lookup string x Γ = Some y) (at level 10).

Fixpoint delete {A} (k : string) (xs : list (string * A)) : list (string * A) :=
  match xs with
  | [] => []
  | (k', v) :: xs => if String.eqb k k' then xs else (k', v) :: delete k xs
  end
.

Lemma lookup_uniq Γ x y z :
  Γ |-- x ~> y ->
  Γ |-- x ~> z ->
  y = z
.
Proof.
  intros.
  rewrite H in H0.
  inversion H0.
  reflexivity.
Qed.

Lemma lookup_weaken Γ x x' y y' :
  x <> y ->
  Γ |-- x ~> x' ->
  ((y, y') :: Γ) |-- x ~> x'.
Proof.
Admitted.

Lemma lookup_In {A} k (v : A) xs :
  lookup k xs = Some v ->
  In (k, v) xs
.
Admitted.

Lemma lookup_head : forall x y z Γ,
  ((x, y) :: Γ) |-- x ~> z <-> y = z.
Admitted.

Require Import Coq.Program.Equality.
Lemma rename_afi Δ Γ x x' t t' :
  rename Δ Γ t t' ->
  Γ |-- x ~> x' ->
  Term.appears_free_in x t -> Term.appears_free_in x' t'
.
Proof.
  intros H_ren H_x_x' H_afi_x_t.
  dependent induction H_ren.
    all: try (solve [inversion H_afi_x_t; subst; auto]).
    - (* Var *)
      rename x0 into y.
      rename x'0 into y'.
      inversion H_afi_x_t; subst.
      assert (x' = y') by eauto using lookup_uniq.
      subst x'.
      constructor.
    - (* Let Rec *)
      admit.
    - (* Let NonRec nil *)
      admit.
    - (* Let NonRec cons *)
      admit.
    -  (* LamAbs *)
      rename x0 into y, x'0 into y'.
      destruct (string_dec x y).
      + subst y.
        inversion H_afi_x_t; subst.
        contradiction.
      + unfold safe_var in *.
        constructor.
        * intros H_eq; subst y'.
           inversion H_afi_x_t; subst.
           match goal with
             H : Term.appears_free_in x t |- _ => contradict H
           end.
           auto using lookup_In.
        * inversion H_afi_x_t; subst.
          auto using lookup_weaken.
Admitted.

Lemma rename_afi_rev {Δ Γ x x' t t'} :
  rename Δ Γ t t' ->
  Γ |-- x ~> x' ->
  Term.appears_free_in x' t' -> Term.appears_free_in x t
.
Admitted.

Lemma rename_weaken : forall Δ Γ t t',
  rename [] [] t t' ->
  rename Δ Γ t t'.
Admitted.

Lemma rename_strengthen : forall Γ Δ x y z,
  x <> y ->
  rename Δ Γ (Var y) (Var z) ->
  rename Δ (delete x Γ) (Var y) (Var z)
.
Admitted.

Lemma subst_neq x t y :
  x <> y ->
  subst x t (Var y) = Var y.
Proof.
  simpl.
  intros.
  rewrite <- String.eqb_neq in H. rewrite H.
  reflexivity.
Qed.


Lemma rename_subst : forall t t' Δ Γ v v' x x',
  Γ |-- x ~> x' ->
  rename Δ Γ t t' ->
  rename [] [] v v' ->
  rename Δ (delete x Γ) <{ [x := v] t }> <{[ x' := v'] t'}>
.
Proof.
  induction t; intros t'' Δ Γ v v' x x' H_lookup H_ren_t H_ren_v.
  all: inversion H_ren_t; subst.
  -  (* Let Rec *)
    rewrite subst_unfold.
    admit.
  - (* NonRec nil *)
    simpl.
    constructor.
    apply IHt; assumption.
  - (* NonRec cons *)
    admit.
  - (* Var *)
    destruct (string_dec x n).
    + rename x'0 into y.
      subst n.
      assert (x' = y) by eauto using lookup_uniq.
      subst x'.
      simpl.
      rewrite String.eqb_refl.
      rewrite String.eqb_refl.
      auto using rename_weaken.
    + rewrite subst_neq; auto.
      assert ( x' <> x'0 ). {
        intros H. subst x'0.
        assert (H : Term.appears_free_in x (Var n)). {
          apply (rename_afi_rev H_ren_t H_lookup).
          constructor.
          }
        inversion H; contradiction.
      }
      rewrite subst_neq; auto.
      eapply rename_strengthen in H_ren_t; eauto.
  - simpl.
    constructor; auto.
    apply safe_tyvarA__subst.
    eauto using rename_closed_l.
  - (* LamAbs *)
    simpl.
    admit.
  - simpl. eauto using rename.
  - simpl. eauto using rename.
  - simpl. eauto using rename.
  - simpl. eauto using rename.
  - simpl. eauto using rename.
  - simpl. eauto using rename.
  - simpl. eauto using rename.
Admitted.



Lemma rename_eval t t' v n:
  rename [] [] t t' ->
  eval t v n ->
  exists v',
    eval t' v' n /\ rename [] [] v v'.
Proof.
  intros H_ren H_eval.
  revert t' H_ren.
  dependent induction H_eval; intros t' H_ren.
  - (* E_LamAbs *)
    inversion H_ren; subst.
    eexists.
    split.
    + econstructor. reflexivity.
    + assumption.
  - (* E_Apply *)
    rename t1 into s, t2 into t, t0 into u, v0 into r.
    rename v2 into t_v.
    inversion H_ren; subst.
    rename t'0 into t'.
    (*
    specialize (IHH_eval1 _ H2) as [s'_v [ eval_s' H_ren_s_v]]. clear H2.
    inversion H_ren_s_v; subst.
    rename τ' into T', t'0 into u'.
    specialize (IHH_eval2 _ H4) as [t'_v [ eval_t' H_ren_t']]. clear H4.

    assert ( rename [] [] <{ [t_v / x] u }> <{ [t'_v / x'] u'}>). {
      (* Needed to apply rename_subst *)
      assert (H_empty : delete x [(x, x')] = []). {
        simpl. rewrite eqb_refl. reflexivity.
      }
      rewrite <- H_empty at 2.
      eapply rename_subst; auto.
      rewrite  lookup_head.
      reflexivity.
    }

    specialize (IHH_eval3 _ H0) as [r' [H_eval_subst H_ren_r]]. clear H0.
    eexists.
    split.
    + econstructor; eauto.
      intro H_er.
      apply (rename_is_error H_ren_t') in H_er.
      contradiction.
    + eauto.
  - (* TyAbs *)
  *)
Admitted.
