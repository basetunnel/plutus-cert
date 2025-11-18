Require Import
  Lists.List
  Strings.String
.
From PlutusCert Require Import
  Util
  PlutusIR
  PlutusIR.Analysis.Equality
  DeadCode.Spec2
  Compat
  Purity
  Size
  Analysis.BoundVars
.

Import ListNotations.

Require Import
  Arith.


Section Bindings.
  Context (mk : term -> term -> option term).

  Definition mk_Binding  (b b' : binding) : option binding :=
    match b, b' with
      | TermBind s vd t, TermBind s' vd' t' =>
          if strictness_eqb s s' &&
            VDecl_eqb vd vd'
          then TermBind s vd <$> mk t t'
          else None
      | DatatypeBind dtd, DatatypeBind dtd' =>
          if DTDecl_eqb dtd dtd'
            then pure (DatatypeBind dtd)
            else None
      | TypeBind tvd ty, TypeBind tvd' ty' =>
          if TVDecl_eqb tvd tvd' &&
            Ty_eqb ty ty'
          then pure (TypeBind tvd ty)
          else None
      | _, _ => None
    end
  .

  Fixpoint match_Bindings
    (bs bs' : list binding)
    : bool :=
      match bs, bs' with

      | b :: bs, b' :: bs' =>
          match mk_Binding b b' with
          | None => (* Binding was removed *)
              match_Bindings bs (b' :: bs')
          | Some _ => (* Binding matches *)
              match_Bindings bs bs'
          end
      | _ , [] => (* All were removed *)
          true
      | [] , _ :: _ => (* Some bindings that didn't exist: the whole block in the pre-term was removed *)
          false
      end
  .
  End Bindings.

  Fixpoint mk (t t' : term) {struct t} : option term :=
    match t, t' with
    | Let rec bs t
    , Let rec' bs' t' =>
        if recursivity_eqb rec rec'
          then
            if match_Bindings mk bs bs'
              then Let rec bs' <$> mk t t'
              else
                (* Whole let block was removed *)
                Let rec [] <$> mk t t'
          else
            (* Whole let block was removed *)
            Let rec [] <$> mk t t'
    | Let rec bs t
    , t' => (* Whole block was removed *)
        Let rec [] <$> mk t t'
    | LamAbs n ty t
    , LamAbs n' ty' t' =>
        if String.eqb n n' &&
          Ty_eqb ty ty'
        then LamAbs n ty <$> mk t t'
        else None
    | Var n, Var n' =>
        if String.eqb n n'
          then Some (Var n)
          else None
    | TyAbs n k t, TyAbs n' k' t' =>
        if String.eqb n n' &&
           Kind_eqb k k'
        then TyAbs n k <$> mk t t'
        else None
    | Apply s t, Apply s' t' =>
        Apply <$> mk s s' <*> mk t t'
    | TyInst t ty, TyInst t' ty' =>
        if Ty_eqb ty ty'
        then TyInst <$> (mk t t') <*> pure ty
        else None
    | IWrap ty1 ty2 t, IWrap ty1' ty2' t' =>
        if Ty_eqb ty1 ty1' &&
           Ty_eqb ty2 ty2'
        then IWrap ty1 ty2 <$> mk t t'
        else None
    | Unwrap t, Unwrap t' =>
        Unwrap <$> mk t t'
    | Error ty, Error ty' =>
        if Ty_eqb ty ty'
          then pure (Error ty)
          else None
    | Constant c, Constant c' =>
        if constant_eqb c c'
          then pure (Constant c)
          else None
    | Builtin f, Builtin f' =>
        if func_eqb f f'
          then pure (Builtin f)
          else None
    | Constr T i ts, Constr T' i' ts' =>
        if Nat.eqb i i' && Ty_eqb T T'
          then Constr T i <$> sequence_options (zip_with mk ts ts')
          else None
    | Case T t ts, Case T' t' ts' =>
        if Ty_eqb T T' then
          Case T <$> mk t t' <*> sequence_options (zip_with mk ts ts')
        else
          None
    | _, _ => None
   end.
