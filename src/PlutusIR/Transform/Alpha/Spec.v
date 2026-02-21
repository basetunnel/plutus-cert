From Coq Require Import
  Strings.String
  Lists.List
  Program.Equality
.
From PlutusCert Require Import
  Util
  Util.List
  PlutusIR.

Import ListNotations.

Definition ctx := list (string * string).

Reserved Notation "Δ ⊢* s '~' t" (at level 40).
Reserved Notation "s '~a' t" (at level 40).
Reserved Notation "Δ ⊢vds s '~' t" (at level 40).
Reserved Notation "Δ ,, Γ ⊢ s '~' t" (at level 40).
Reserved Notation "Δ ,, Γ ⊢b s '~' t" (at level 40).

(* In a renaming context Δ, `alpha_lookup Δ x y` asserts that:
 *   - x is renamed to y
 *   - no other variable, bound after `x` is renamed to y
 * Both are enforced by the AL_diff constructor.
**)
Inductive alpha_lookup : ctx -> string -> string -> Prop :=

  | AL_cons x y xs :
      alpha_lookup ((x, y) :: xs) x y

  | AL_diff x y z w xs :
      x <> z ->
      y <> w ->
      alpha_lookup xs z w ->
      alpha_lookup ((x, y) :: xs) z w
.

Lemma alpha__lookup Δ x y : alpha_lookup Δ x y -> lookup x Δ = Some y.
Admitted.

Lemma alpha__lookup_inv Δ x y : alpha_lookup Δ x y -> lookup_inv y Δ = Some x.
Admitted.

Module TY.

  (* ty_rename Δ T T' relates types T and T', where free variables are
   * renamed according to Δ.
  *)
  Inductive ty_rename : list (string * string) -> ty -> ty -> Prop :=

    | R_TyVar X X' Δ :
        alpha_lookup Δ X X' ->
        Δ ⊢* Ty_Var X ~ Ty_Var X'

    | R_TyLam X X' K T T' Δ :
        ((X, X') :: Δ) ⊢* T ~ T' ->
        Δ ⊢* Ty_Lam X K T ~ Ty_Lam X' K T'

    | R_TyApp T1 T2 T1' T2' Δ :
        Δ ⊢* T1 ~ T1' ->
        Δ ⊢* T2 ~ T2' ->
        Δ ⊢* Ty_App T1 T2 ~ Ty_App T1' T2'

    | R_TyFun T1 T2 T1' T2' Δ :
        Δ ⊢* T1 ~ T1' ->
        Δ ⊢* T2 ~ T2' ->
        Δ ⊢* Ty_Fun T1 T2 ~ Ty_Fun T1' T2'

    | R_TyIFix T1 T2 T1' T2' Δ :
        Δ ⊢* T1 ~ T1' ->
        Δ ⊢* T2 ~ T2' ->
        Δ ⊢* Ty_IFix T1 T2 ~ Ty_IFix T1' T2'

    | R_TyForall X X' K T T' Δ :
        ((X, X') :: Δ) ⊢* T ~ T' ->
        Δ ⊢* Ty_Forall X K T ~ Ty_Forall X' K T'

    | R_TyBuiltin Δ U :
        Δ ⊢* Ty_Builtin U ~ Ty_Builtin U

    | R_TySOP Δ Tss Tss':
        ForallSetPair2 (fun T T' => Δ ⊢* T ~ T') Tss Tss' ->
        Δ ⊢* Ty_SOP Tss ~ Ty_SOP Tss'

    where "Δ ⊢* s '~' t" := (ty_rename Δ s t)
  .

  (* Rename free variables according to a context Δ *)
  Definition rename_free : ctx -> ty -> ty := fix ren (Δ : ctx) T :=
    match T with
    | Ty_Var X        =>
        match lookup X Δ with
        | Some X' => Ty_Var X'
        | None    => Ty_Var X
        end

    (* binders*)
    | Ty_Lam X K T    => Ty_Lam X K (ren (drop X Δ) T)
    | Ty_Forall X K T => Ty_Forall X K (ren (drop X Δ) T)

    | Ty_Fun U T      => Ty_Fun (ren Δ U) (ren Δ T)
    | Ty_App U T      => Ty_App (ren Δ U) (ren Δ T)
    | Ty_IFix U T     => Ty_IFix (ren Δ U) (ren Δ T)
    | Ty_Builtin B    => Ty_Builtin B
    | Ty_SOP TTU      => Ty_SOP (map (map (ren Δ)) TTU)
    end
    .

  (*
  Alpha-equivalence, e.g.

    λx . x ~ λy. y

  *)
  Inductive ty_alpha : ty -> ty -> Prop :=

    | A_TyVar X :
        Ty_Var X ~a Ty_Var X

    | A_LamAbs K X T X' T' :
        (rename_free [(X, X')] T) ~a T' ->
        Ty_Lam X K T ~a Ty_Lam X' K T'

    | A_Apply S T S' T' :
        S ~a S' ->
        T ~a T' ->
        Ty_App S T ~a Ty_App S' T'

    where "s '~a' t" := (ty_alpha s t)
  .

  Lemma rename__alpha Δ S T :
    Δ ⊢* S ~ T ->
    rename_free Δ S ~a T.
  Proof.
    intros H.
    dependent induction H.
  Admitted.

  Lemma alpha__rename Δ S T :
    rename_free Δ S ~a T ->
    Δ ⊢* S ~ T.
  Admitted.
  (* Not sure if this holds? this direction may not be necessary for the
   * decision procedure (which is only neede for the alpha_rename relation)  *)


  Lemma alpha_refl S :
    S ~a S.
  Admitted.

  Lemma alpha_sym S T :
    S ~a T ->
    T ~a S.
  Admitted.

  Lemma alpha_trans S T U :
    S ~a T ->
    T ~a U ->
    S ~a U.
  Admitted.





  Open Scope string_scope.


  Lemma alpha__rename Δ T T' :
    Δ ⊢* T ~ T' -> [] ⊢* (rename_free Δ T) ~ T'.
  Admitted.

  (* Symmetric contexts *)
  Definition ctx_refl (xs : ctx) := Forall (fun '(x, y) => x = y) xs.

  From PlutusCert Require Import FreeVars Util.
  Import FreeVars.Ty.

  Definition ftv_ctx : ty -> ctx :=
    fun T => let xs := ftv T in zip xs xs.

  Lemma ftv_ctx_equation
     : forall T : ty,
       ftv_ctx T =
       match T with
       | Ty_Var X => [(X,X)]
       | Ty_IFix F T0 => ftv_ctx F ++ ftv_ctx T0
       | Ty_Builtin _ => []
       | Ty_Forall X _ T' | Ty_Lam X _ T' => remove (prod_dec string_dec string_dec) (X, X) (ftv_ctx T')
       | Ty_Fun T1 T2 | Ty_App T1 T2 => ftv_ctx T1 ++ ftv_ctx T2
       | Ty_SOP Tss => flatmap2 ftv_ctx Tss
       end
    .
  Admitted.

  Lemma ftv_ctx__Ty_Fun S T :
    ftv_ctx (Ty_Fun S T) = ftv_ctx S ++ ftv_ctx T.
  Admitted.

  Lemma ftv_cx__refl T : ctx_refl (ftv_ctx T).
  Proof.
    cbv [ ctx_refl ].
    induction T; simpl.
    - cbv. auto.
    -
  Admitted.




  Lemma alpha_refl T :
    ftv_ctx T ⊢* T ~ T.
  Proof.
    induction T.
    - admit.
    - unfold ftv_ctx, zip in *. simpl in *.
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

(* Renaming environments obtained point-wise *)


Inductive tvdecls_env : list tvdecl -> list tvdecl -> ctx -> Prop :=
| TVDE_nil :
    tvdecls_env [] [] []
| TVDE_cons X K X' tvds tvds' Δ :
    tvdecls_env tvds tvds' Δ ->
    tvdecls_env (TyVarDecl X K :: tvds) (TyVarDecl X' K :: tvds') ((X, X') :: Δ)
.


Inductive vdecls_env : list vdecl -> list vdecl -> ctx -> Prop :=
| VDE_nil :
    vdecls_env [] [] []
| VDE x T x' T' vds vds' Γ :
    vdecls_env vds vds' Γ ->
    vdecls_env (VarDecl x T :: vds) (VarDecl x' T' :: vds') ((x, x') :: Γ)
.

Inductive alpha_vds
  (Δ : list (string * string))
  : list vdecl -> list vdecl -> Prop :=

  | AV_cons X T X' T' vds vds' :
      Δ ⊢* T ~ T' ->
      Δ ⊢vds vds ~ vds' ->
      Δ ⊢vds (VarDecl X T :: vds) ~ (VarDecl X' T' :: vds')

  | AV_nil :
      Δ ⊢vds [] ~ []

  where "Δ ⊢vds s '~' t" := (alpha_vds Δ s t)
.



Inductive alpha
  (Δ : list (string * string))
  (Γ : list (string * string))
  : term -> term -> Prop :=

  | A_Var x x' :
      alpha_lookup Γ x x' ->
      Δ ,, Γ ⊢ `x ~ `x'

  | A_LamAbs x x' T T' t t' :
      Δ ⊢* T ~ T' ->
      Δ ,, ((x, x') :: Γ) ⊢ t ~ t' ->
      Δ ,, Γ ⊢ λ x T t ~ λ x' T' t'

  | A_Apply t1 t2 t1' t2' :
      Δ ,, Γ ⊢ t1 ~ t1' ->
      Δ ,, Γ ⊢ t2 ~ t2' ->
      Δ ,, Γ ⊢ (t1 ⋅ t2) ~ (t1' ⋅ t2')

  | A_LetNil r t t' :
      Δ ,, Γ ⊢ t ~ t' ->
      Δ ,, Γ ⊢ Let r [] t ~ Let r [] t'

  | A_LetTermBind s x T t x' T' t' bs bs' tb tb':
      Δ ,, ((x, x') :: Γ)
        ⊢ Let NonRec bs  tb
        ~ Let NonRec bs' tb' ->
      Δ ,, Γ
        ⊢ Let NonRec (TermBind s (VarDecl x  T)  t  :: bs ) tb
        ~ Let NonRec (TermBind s (VarDecl x' T') t' :: bs') tb'

  | A_LetTypeBind X K T X' T' bs bs' tb tb':
      ((X, X') :: Δ) ,, Γ
        ⊢ Let NonRec bs  tb
        ~ Let NonRec bs' tb' ->
      Δ ,, Γ
        ⊢ Let NonRec (TypeBind (TyVarDecl X  K) T :: bs ) tb
        ~ Let NonRec (TypeBind (TyVarDecl X' K) T' :: bs') tb'

  | A_LetDatatypeBind Δ' Γ' bs bs' tb tb' X X' K tvs tvs' m m' cs cs':
      tvdecls_env tvs tvs' Δ' ->
      vdecls_env cs cs' Γ' ->
      ([(X, X')] ++ Δ' ++ Δ) ,, ([(m, m')] ++ Γ' ++ Γ)
        ⊢ Let NonRec bs  tb ~ Let NonRec bs' tb' ->

      Δ ,, Γ ⊢ Let NonRec (DatatypeBind (Datatype (TyVarDecl X K) tvs m cs) :: bs ) tb
             ~ Let NonRec (DatatypeBind (Datatype (TyVarDecl X' K) tvs m' cs') :: bs') tb'

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
