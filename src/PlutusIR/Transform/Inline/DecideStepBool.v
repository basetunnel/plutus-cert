Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import PeanoNat.
Require Import Bool.

Import ListNotations.
From Equations Require Import Equations.
Require Import Program.
Require Import Lia.

Set Implicit Arguments.
Set Equations Transparent.

From PlutusCert Require Import Util.
From PlutusCert Require Import PlutusIR.Transform.Inline.
From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import PlutusIR.Analysis.FreeVars.
From PlutusCert Require Import PlutusIR.Analysis.Equality.
From PlutusCert Require Import PlutusIR.Transform.Compat.
From PlutusCert Require Import PlutusIR.Transform.DeadCode.Spec.

Tactic Notation "step" hyp(n) :=
  destruct n;
  [ exact false
  | refine (_ )
  ].


(*
TODO: update decision procedure with new inline definition


Definition is_inline' : forall (n : nat) (t t' : Term) (env : Env),
  bool.
Proof.

(* The mutually recursive structure *)
refine (
  fix is_inline (n : nat) : forall t t' env, bool :=

    let is_inline_compat (n : nat) : forall t t' env, bool
      := ?[is_inline_compat] in
    let is_inline_var (n : nat) : forall t t' env, bool
      := ?[is_inline_var] in
    let is_inline_let (n : nat) : forall t t' env, bool
      := ?[is_inline_let] in

    fun t t' env => is_inline_var n t t' env || is_inline_let n t t' env || is_inline_compat n t t' env

  with is_inline_binding (n : nat) : forall b b' env, bool :=
    ?[is_inline_binding]

  with is_inline_bindings (n : nat) : forall bs bs' env, bool :=
    ?[is_inline_bindings]

  with is_compat (n : nat) : forall t t' env, bool :=
    ?[is_compat]

  with is_compat_binding (n : nat) : forall b b' env, bool :=
    ?[is_compat_binding]

  with is_compat_bindings (n : nat) : forall bs bs' env, bool :=
    ?[is_compat_bindings]

  for is_inline
).

[is_inline_var]: {
intros t_var t' env.
step n.

refine(
    match t_var with
      | Var v =>
        match lookup string_dec v env with
          | Some (existT _ t _) => is_inline n t t' env
          | Nothing => false
        end
      | _     => false
    end
).
}

[is_inline_let]: {
clear is_inline_var. (* so noisy *)
intros t t' env.
step n.

refine (
  match t with
  | Let r bs b  => match t' with
    | Let r' bs' b' => match Recursivity_dec r r' with
      | left rH => is_inline_bindings n bs bs' env && is_inline n b b' env
      | _ => false
      end
    | _             => false
    end
  | _ => false
  end
).

[is_inline_compat] : {
  intros t t' env.
  step n.

  refine (
    is_compat n t t' env
  ).
}
}

[is_inline_bindings]: {
  intros bs bs' env.
  step n.

  refine (
    (* Coq is clever, do not have to carry eq_refls around*)
    match bs, bs' with
    | (b :: bs), (b' :: bs') => ?[cons]
    | nil      , nil         => ?[nil]
    | _        , _           => false
    end
  ).

  [cons]: {
    refine (
        is_inline_binding n b b' env
        && is_inline_bindings n bs bs' env
    ).
  }

  [nil]: {
    refine true.
  }
}

[is_inline_binding]: {
  intros b b' env.
  step n.

  refine (
    match b, b' with
      | TermBind s v t, TermBind s' v' t' => match Strictness_dec s s' with
        | left Hs => match VDecl_dec v v' with
          | left Hv => ?[termbinds]
          | right _ => false
          end
        | right _ => false
        end

      | TypeBind v ty, TypeBind v' ty' => match TVDecl_dec v v', Ty_dec ty ty' with
        | left Hv, left Hty => ?[tyty]
        | _, _ => false
        end

      | DatatypeBind d, DatatypeBind d' => match DTDecl_dec d d' with
        | left Hd => ?[dtdt]
        | _ => false
        end
      | _, _ => false
      end
  ).

  [termbinds]: {
    subst.
    refine (is_inline n t t' env).
  }
  [tyty]: {
    subst.
    refine (true).
  }
  [dtdt]: {
    subst.
    refine (true).
  }
}

[is_compat]: {
  intros t t' env.
  step n.

  refine (
  match t, t' as p with
  | Let r bs t, Let r' bs' t' =>
          (sumbool_to_bool (Recursivity_dec r r'))
          && is_compat_bindings n bs bs' env
          && is_inline n t t' env

  | Apply s t, Apply s' t' =>
          is_inline n s s' env
          && is_inline n t t' env

  | Var n, Var m => sumbool_to_bool (string_dec n m)

  | TyAbs v k t
  , TyAbs v' k' t' => match string_dec v v', Kind_dec k k' with
    | left Hs, left Hk => ?[tyabs]
    | _, _ => false
    end

  | LamAbs v ty t
  , LamAbs v' ty' t' => match string_dec v v', Ty_dec ty ty' with
    | left Hs, left Ht => ?[lamabs]
    | _, _ => false
    end

  | TyInst t ty
  , TyInst t' ty' => match Ty_dec ty ty' with
    | left Hty => ?[tyinst]
    | _ => false
    end

  | IWrap ty1 ty2 t
  , IWrap ty1' ty2' t' => match Ty_dec ty1 ty1', Ty_dec ty2 ty2' with
    | left Hty1, left Hty2 => ?[iwrap]
    | _, _ => false
    end
  | Unwrap t,
    Unwrap t' => ?[unwrap]

  | Constant c,
    Constant c' => match some_valueOf_dec c c' with
      | left Hs => ?[constant]
      | _ => false
      end

  | Builtin f,
    Builtin f' => match func_dec f f' with
      | left Hb => ?[builtin]
      | _ => false
      end

  | Error ty
  , Error ty' => match Ty_dec ty ty' with
      | left Hty => ?[error]
      | _ => false
      end

  | _, _ => false
  end
  ).


  [lamabs]: {
    refine (is_inline n t t' env).
  }
  [tyabs]: {
    refine (
      is_inline n t t' env
    ).
  }
  [tyinst]: {
    refine (
      is_inline n t t' env
    ).
  }
  [iwrap]: {
    refine (
     is_inline n t t' env
    ).
  }
  [unwrap]: {
    refine (
      is_inline n t t' env
    ).
  }
  [constant]: {
    refine (
      true
    ).
  }
  [builtin]: {
    refine (
      true
    ).
  }

  [error]: {
    refine (
      true
    ).
  }
}

[is_compat_binding]: {
  intros b b' env.
  step n.

  refine(
  match b, b' with
    | TermBind s  v  t
    , TermBind s' v' t' => match Strictness_dec s s', VDecl_dec v v' with
      | left Hs, left Hv => ?[termbind]
      | _, _ => false
      end

    | TypeBind v ty
    , TypeBind v' ty' => match TVDecl_dec v v', Ty_dec ty ty' with
      | left Hv, left Hty => ?[typebind]
      | _, _ => false
      end

    | DatatypeBind d
    , DatatypeBind d' => match DTDecl_dec d d' with
      | left Hd => ?[datatypebind]
      | _ => false
      end

    | _, _ => false
    end
  ).

  [termbind]: {
    refine (is_inline n t t' env).
    }
  [typebind]: {
    refine (true).
  }
  [datatypebind]: {
    refine (true).
  }
}

[is_compat_bindings]: {
  intros bs bs' env.
  step n.

  refine (
    match bs, bs' with
    | (b :: bs), (b' :: bs') => ?[cons]
    | nil      , nil         => ?[nil]
    | _        , _           => false
    end
  ).

  [cons]: {
    refine (
        is_compat_binding n b b' env
        && is_compat_bindings n bs bs' env
    ).
  }

  [nil]: {
    refine (true).
  }
}
Defined.



Definition is_inline n t t' := is_inline' n t t' nil.
*)
