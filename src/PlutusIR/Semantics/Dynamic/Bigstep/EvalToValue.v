Require Import PlutusCert.PlutusIR.

Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.


Lemma eval_builtin__result : forall t,
    result (eval_builtin t).
Proof.
  intros t.
  destruct t; simpl.
  (* TODO: redo for new built-ins *)
  admit.
Admitted.


Lemma eval_to_result :
    (forall t v k, t =[k]=> v -> result v) /\
    (forall t v k, t =[k]=>nr v -> result v) /\
    (forall bs0 t v k, t =[k]=>r v WITH bs0 -> result v).
Proof with (eauto with hintdb__eval_no_error).
  apply eval__multind.
  all: intros.
  all: try (solve [subst; eauto using
    result__value, eval_builtin__result]).
  - (* E_Unwrap *)
    apply <- result__IWrap...
Qed.

Corollary eval_to_result__eval : forall t v k,
    t =[k]=> v ->
    result v.
Proof. apply eval_to_result. Qed.

Corollary eval_to_result__eval_bindings_nonrec : forall t v k,
    t =[k]=>nr v ->
    result v.
Proof. apply eval_to_result. Qed.

Corollary eval_to_result__eval_bindings_rec : forall bs0 t v k,
    t =[k]=>r v WITH bs0 ->
    result v.
Proof. apply eval_to_result. Qed.
