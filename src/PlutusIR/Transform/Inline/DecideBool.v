From Coq Require Import
  String
  List
  Bool
  Program
  Utf8_core
.

From PlutusCert Require Import
  Util
  PlutusIR
  PlutusIR.Analysis.Equality
  PlutusIR.Transform.Compat
  PlutusIR.Transform.Inline.Spec
.

Import ListNotations.

(* TODO *)
Axiom some_eqb : some valueOf -> some valueOf -> bool.
Axiom some_eqb_eq : ∀ x y, some_eqb x y = true -> x = y.

Section Bindings.

  Context (dec_Term : ctx -> Term -> Term -> bool).
  Context (dec_Term_sound : ∀ Γ s t, dec_Term Γ s t = true -> inline Γ s t).
  Context (strictness_eqb_eq : ∀ s s0, strictness_eqb s s0 = true -> s = s0).
  Context (VDecl_eqb_eq : ∀ v v0, VDecl_eqb v v0 = true -> v = v0).

  Fixpoint dec_Bindings_Rec (Γ : ctx) (bs bs' : list Binding) : bool := match bs, bs' with
    | (TermBind s vdecl t :: bs), (TermBind s' vdecl' t' :: bs') =>
           strictness_eqb s s'
        && VDecl_eqb vdecl vdecl'
        && dec_Term Γ t t'
        && dec_Bindings_Rec Γ bs bs'

    | (TypeBind tvdecl ty :: bs), (TypeBind tvdecl' ty' :: bs') =>
           TVDecl_eqb tvdecl tvdecl'
        && Ty_eqb ty ty'
        && dec_Bindings_Rec Γ bs bs'

    | (DatatypeBind dtd :: bs) , (DatatypeBind dtd' :: bs')     =>
          DTDecl_eqb dtd dtd'
        && dec_Bindings_Rec Γ bs bs'

    | []       , []          => true
    | _        , _           => false
    end
  .


  Lemma dec_Bindings_Rec_sound : ∀ Γ bs bs',
    dec_Bindings_Rec Γ bs bs' = true -> inline_Bindings_Rec Γ bs bs'.
  Proof with eauto.
  intros Γ bs.
  induction bs.
  all: intros bs' H_true.
  (* bs = [] *)
  - destruct bs'.
    + constructor.
    + inversion H_true.
  (* bs = b :: bs*)
  - destruct bs', a.
    1, 2, 3: inversion H_true.
    all: destruct b.
    + simpl in H_true.
      repeat (apply andb_true_iff in H_true; destruct H_true as [?H_true ?]).
      assert (H_v0_v1 : v = v0)...
      assert (H_s0_s1 : s = s0)...
      subst.
      destruct v0.
      constructor.
      * eapply inl_TermBind...
      assert (H_ : v = v0)...
      assert ()
      let (H_v_v0 : v0 = v1) _.
      constructor.
        *  econstructor.

    + destruct b.
      2, 3: inversion H_true.
      * inversion H_true.
      * inversion H_true.
      all: inversion H_true.
      * inversion H_true.
    destruct a.
    + simpl in H_true.
  simpl in H_true.

  Fixpoint dec_Bindings_NonRec (Γ : ctx) (bs bs' : list Binding) : bool := match bs, bs' with
    | (b :: bs), (b' :: bs') =>
        dec_Bindings_NonRec (Binding_to_ctx b ++ Γ) bs bs' &&
        match b, b' with
        | (TermBind s vdecl t), (TermBind s' vdecl' t') =>
             strictness_eqb s s'
          && VDecl_eqb vdecl vdecl'
          && dec_Term Γ t t'

        | (TypeBind tvdecl ty), (TypeBind tvdecl' ty') =>
           TVDecl_eqb tvdecl tvdecl'
        && Ty_eqb ty ty'

        | (DatatypeBind dtd) , (DatatypeBind dtd')     =>
              DTDecl_eqb dtd dtd'

        | _ , _ => false
        end

    | []       , []          => true
    | _        , _           => false
    end
  .

End Bindings.

Fixpoint dec_Term (Γ : ctx) (x y : Term) {struct x} : bool := match x, y with
  (*| Var n          , t                  =>*)

  | Var n          , Var m              => String.eqb n m

  | Let NonRec bs t   , Let NonRec bs' t' =>
      let Γ_bs := Bindings_to_ctx bs in
         dec_Bindings_NonRec dec_Term Γ bs bs'
      && dec_Term (Γ ++ Γ_bs) t t'

  | Let Rec bs t   , Let Rec bs' t' =>
      let Γ_bs := Bindings_to_ctx bs in
         dec_Bindings_Rec dec_Term (Γ ++ Γ_bs) bs bs'
      && dec_Term (Γ ++ Γ_bs) t t'

  | TyAbs n k t    , TyAbs n' k' t'     => String.eqb n n' && Kind_eqb k k' && dec_Term Γ t t'
  | LamAbs n ty t  , LamAbs n' ty' t'   => String.eqb n n' && Ty_eqb ty ty' && dec_Term Γ t t'
  | Apply s t      , Apply s' t'        => dec_Term Γ s s' && dec_Term Γ t t'
  | Constant c     , Constant c'        => some_eqb c c'
  | Builtin f      , Builtin f'         => func_eqb f f'
  | TyInst t ty    , TyInst t' ty'      => dec_Term Γ t t' && Ty_eqb ty ty'
  | Error ty       , Error ty'          => Ty_eqb ty ty'
  | IWrap ty1 ty2 t, IWrap ty1' ty2' t' => Ty_eqb ty1 ty1' && Ty_eqb ty2 ty2' && dec_Term Γ t t'
  | Unwrap t       , Unwrap t'          => dec_Term Γ t t'

  | _, _ => false
  end


.
