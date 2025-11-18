
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import PeanoNat.

Import ListNotations.
From Equations Require Import Equations.
Require Import Program.
Require Import Lia.

Set Implicit Arguments.
Set Equations Transparent.

From PlutusCert Require Import Util.
From PlutusCert Require Import PlutusIR.Transform.Inline.Spec.
From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import PlutusIR.Analysis.FreeVars.
From PlutusCert Require Import PlutusIR.Transform.Compat.
From PlutusCert Require Import PlutusIR.Examples.
From PlutusCert Require Import PlutusIR.Optimizer.DeadCode.Spec.

Tactic Notation "step" hyp(n) :=
  destruct n;
  [ exact Nothing
  | refine (_ )
  ].


Definition is_inline_term : forall (n : nat) (t t' : Term) (env : Env),
  option (Inline env t t').
Proof.

(* The mutually recursive structure *)
refine (
  fix is_inline_term (n : nat) : forall t t' env, option (Inline env t t') :=

    let is_inline_compat (n : nat) : forall t t' env, option (Inline env t t')
      := ?[is_inline_compat] in
    let is_inline_var (n : nat) : forall t t' env, option (Inline env t t')
      := ?[is_inline_var] in
    let is_inline_let (n : nat) : forall t t' env, option (Inline env t t')
      := ?[is_inline_let] in

    fun t t' env =>
          is_inline_var n t t' env
      <|> is_inline_let n t t' env
      <|> is_inline_compat n t t' env

  with is_inline_binding (n : nat) : forall b b' env, option (Inline_Binding env b b') :=
    ?[is_inline_binding]

  with is_inline_bindings (n : nat) : forall bs bs' env, option (Inline_Bindings env bs bs') :=
    ?[is_inline_bindings]

  with is_compat (n : nat) : forall t t' env, option (Compat (Inline env) t t') :=
    ?[is_compat]

  with is_compat_binding (n : nat) : forall b b' env, option (Compat_Binding (Inline env) b b') :=
    ?[is_compat_binding]

  with is_compat_bindings (n : nat) : forall bs bs' env, option (Compat_Bindings (Inline env) bs bs') :=
    ?[is_compat_bindings]

  for is_inline_term
).

[is_inline_var]: {.
intros t_var t' env.
step n.

refine(
    match t_var as x return t_var = x -> _ with
      | Var v => fun eq_t =>
        match lookup string_dec v env with
          | Some (existT _ t in_env) => Inl_Var in_env <$> is_inline_term n t t' env
          | Nothing => Nothing
        end
      | _     => fun _ => Nothing
    end eq_refl
).
}

[is_inline_let]: {.
clear is_inline_var. (* so noisy *)
intros t t' env.
step n.

refine (
  match t as p return t = p -> _ with
  | Let r bs b  => fun H1 => match t' as p' return t' = p' -> _ with
    | Let r' bs' b' => fun H2 => match Recursivity_dec r r' with
      | left rH => _
      | _ => Nothing
      end
    | _             => fun _  => Nothing
    end eq_refl
  | _ => fun _ => Nothing
  end eq_refl
); subst.
refine (
  (@Inl_Let _ bs env bs' b b' r' eq_refl)
    <$> is_inline_bindings n bs bs' _ (* infers that env' = bindingsToEnv bs ++ env*)
    <*> is_inline_term n b b' _
).
}
Show Proof.
[is_inline_compat] : {.
  intros t t' env.
  step n.

  refine (
    Inl_Compat <$> is_compat n t t' env
  ).
}

[is_inline_bindings]: {.
  intros bs bs' env.
  step n.

  refine (
    (* Coq is clever, do not have to carry eq_refls around*)
    match bs, bs' with
    | (b :: bs), (b' :: bs') => ?[cons]
    | nil      , nil         => ?[nil]
    | _        , _           => Nothing
    end
  ).

  [cons]: {.
    refine (
      Inl_Binding_cons
        <$> is_inline_binding n b b' env
        <*> is_inline_bindings n bs bs' env
    ).
  }

  [nil]: {.
    refine (Some Inl_Binding_nil).
  }
}

[is_inline_binding]: {.
  intros b b' env.
  step n.

  refine (
    match b, b' with
      | TermBind s v t, TermBind s' v' t' => match Strictness_dec s s' with
        | left Hs => match VDecl_dec v v' with
          | left Hv => ?[termbinds]
          | right _ => Nothing
          end
        | right _ => Nothing
        end

      | TypeBind v ty, TypeBind v' ty' => match TVDecl_dec v v', Ty_dec ty ty' with
        | left Hv, left Hty => ?[tyty]
        | _, _ => Nothing
        end

      | DatatypeBind d, DatatypeBind d' => match DTDecl_dec d d' with
        | left Hd => ?[dtdt]
        | _ => Nothing
        end
      | _, _ => Nothing
      end
  ).

  [termbinds]: {.
    subst.
    refine (Inl_TermBind <$> is_inline_term n t t' env).
  }
  [tyty]: {.
    subst.
    refine (Some Inl_OtherBind).
  }
  [dtdt]: {.
    subst.
    refine (Some Inl_OtherBind).
  }
}

[is_compat]: {.
  intros t t' env.
  step n.

  refine (
  match t, t' as p with
  | Let r bs t, Let r' bs' t' => ?[letlet]
          <$> (sumbool_to_optionl (Recursivity_dec r r'))
          <*> is_compat_bindings n bs bs' env
          <*> is_inline_term n t t' env

  | Apply s t, Apply s' t' => C_Apply _
          <$> is_inline_term n s s' env
          <*> is_inline_term n t t' env

  | Var n, Var m => ?[vars] <$> sumbool_to_optionl (string_dec n m)

  | TyAbs v k t
  , TyAbs v' k' t' => match string_dec v v', Kind_dec k k' with
    | left Hs, left Hk => ?[tyabs]
    | _, _ => Nothing
    end

  | LamAbs v ty t
  , LamAbs v' ty' t' => match string_dec v v', Ty_dec ty ty' with
    | left Hs, left Ht => ?[lamabs]
    | _, _ => Nothing
    end

  | TyInst t ty
  , TyInst t' ty' => match Ty_dec ty ty' with
    | left Hty => ?[tyinst]
    | _ => Nothing
    end

  | IWrap ty1 ty2 t
  , IWrap ty1' ty2' t' => match Ty_dec ty1 ty1', Ty_dec ty2 ty2' with
    | left Hty1, left Hty2 => ?[iwrap]
    | _, _ => Nothing
    end
  | Unwrap t,
    Unwrap t' => ?[unwrap]

  | Constant c,
    Constant c' => match some_dec c c' with
      | left Hs => ?[constant]
      | _ => Nothing
      end

  | Builtin f,
    Builtin f' => match func_dec f f' with
      | left Hb => ?[builtin]
      | _ => Nothing
      end

  | Error ty
  , Error ty' => match Ty_dec ty ty' with
      | left Hty => ?[error]
      | _ => Nothing
      end

  | _, _ => Nothing
  end
  ).

  [letlet]: {.
  intros. subst. constructor; assumption.
  }

  [vars]: {.
  intros. subst. constructor.
  }

  [lamabs]: {.
    subst.
    refine (
      C_LamAbs _ <$> is_inline_term n t t' env
    ).
  }
  [tyabs]: {.
    subst.
    refine (
      C_TyAbs _ <$> is_inline_term n t t' env
    ).
  }
  [tyinst]: {.
    subst.
    refine (
      C_TyInst _ <$> is_inline_term n t t' env
    ).
  }
  [iwrap]: {.
    subst.
    refine (
      C_IWrap _ <$> is_inline_term n t t' env
    ).
  }
  [unwrap]: {.
    subst.
    refine (
      C_Unwrap _ <$> is_inline_term n t t' env
    ).
  }
  [constant]: {.
    subst.
    refine (
      Some (C_Constant _)
    ).
  }
  [builtin]: {.
    subst.
    refine (
      Some (C_Builtin _)
    ).
  }

  [error]: {.
    subst.
    refine (
      Some (C_Error _)
    ).
  }
}

[is_compat_binding]: {.
  intros b b' env.
  step n.

  refine(
  match b, b' with
    | TermBind s  v  t
    , TermBind s' v' t' => match Strictness_dec s s', string_dec v v' with
      | left Hs, left Hv => ?[termbind]
      | _, _ => Nothing
      end

    | TypeBind v ty
    , TypeBind v' ty' => match TVDecl_dec v v', Ty_dec ty ty' with
      | left Hv, left Hty => ?[typebind]
      | _, _ => Nothing
      end

    | DatatypeBind d
    , DatatypeBind d' => match DTDecl_dec d d' with
      | left Hd => ?[datatypebind]
      | _ => Nothing
      end

    | _, _ => Nothing
    end
  ).

  [termbind]: {.
    subst.
    refine (C_TermBind _ <$> is_inline_term n t t' env); exact tt. (* fake types*)
    }
  [typebind]: {.
    subst. refine (Some _). constructor.
  }
  [datatypebind]: {.
    subst. refine (Some _). constructor.
  }
}

[is_compat_bindings]: {.
  intros bs bs' env.
  step n.

  refine (
    match bs, bs' with
    | (b :: bs), (b' :: bs') => ?[cons]
    | nil      , nil         => ?[nil]
    | _        , _           => Nothing
    end
  ).

  [cons]: {.
    refine (
      Compat_Bindings_Cons (R := Inline env)
        <$> is_compat_binding n b b' env
        <*> is_compat_bindings n bs bs' env
    ).
  }

  [nil]: {.
    refine (Some (Compat_Bindings_Nil _)).
  }
}
Defined.

Definition is_inline (t t' : Term) : option (Inline nil t t')
  := is_inline_term (Nat.max (term_size t) (term_size t')) t t' nil.
