Require Import Lists.List.
From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import PlutusIR.Semantics.Static.Typing.Typing.

Import ListNotations.

(* congruence = equivalence relation + context_compatible *)
Definition context_compatible R :=
  forall Δ Γ s t T,
    R Δ Γ s t T ->
    forall (C : context) Δ1 Γ1 T1,
      Δ1 ,, Γ1  |- C : (Δ, Γ, T) ↪ T1 ->
        R Δ1 Γ1 (context_fill C s) (context_fill C t) T1
.
