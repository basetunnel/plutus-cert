From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import Substitution.Free.

From PlutusCert Require Import Bigstep.
From PlutusCert Require Import DeadCode.Spec3.

Require Import Utf8_core.

Definition P_Term t := ∀ t' r i,
  dead_code t t' ->
  eval t r i ->
  ∃ i' r', eval t' r' i'
    /\ dead_code r r' /\ ¬ is_error r'.

From PlutusCert Require Import Language.
From PlutusCert Require Import Language.PIR.
