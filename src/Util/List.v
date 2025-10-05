From Coq Require Import
  Strings.String
  Lists.List
  Bool.Bool
.

Import ListNotations.

Local Open Scope string_scope.
Local Open Scope list_scope.
Import ListNotations.
From QuickChick Require Import QuickChick.
From QuickChick Require Import CheckerProofs.

From PlutusCert Require Import Util.Tactics.

Require Import Utf8_core.

Notation "x ∈ xs" := (In x xs) (at level 40).
Notation "x ∉ xs" := (~ (In x xs)) (at level 40).


Lemma negb_iff b :
  negb b = true <-> b = false.
Proof. destruct b; intuition. Qed.

Function find_index (x : string) (xs : list string) : option nat :=
  match xs with
  | [] => None
  | y :: xs => if x =? y then Some 0 else match find_index x xs with
    | None => None
    | Some y => Some (y + 1)
    end
  end
.

Fixpoint lookup {X:Type} (k : string) (l : list (string * X)) : option X :=
  match l with
  | nil => None
  | (j,x) :: l' => if j =? k then Datatypes.Some x else lookup k l'
  end.

Definition remove_many {A} (A_dec : forall x y : A, {x = y} + {x <> y}) : list A -> list A -> list A :=
  fun xs ys => fold_right (remove A_dec) ys xs.


Definition in_str (x : string) (xs : list string) : bool :=
  if find (eqb x) xs then true else false
.

Lemma in_str__false_hd x y ys : in_str x (y::ys) = false -> x =? y = false.
Proof.
Admitted.

Lemma in_str__false_tl x y ys : in_str x (y::ys) = false -> in_str x ys = false.
Proof.
Admitted.

Lemma in_str__In {x xs} : in_str x xs = true <-> In x xs.
Proof.
  split.
  - induction xs.
    + unfold in_str, find.
      inversion 1.
    + destruct (string_dec x a) as [H_eq | H_neq].
      * subst x. intros. simpl. auto.
      * unfold in_str, find. rewrite <- eqb_neq in H_neq. rewrite H_neq.
        intros H_true. right. auto.
  - induction xs.
    + inversion 1.
    + destruct 1 as [H_eq | H_neq].
      * apply eq_sym in H_eq. rewrite <- eqb_eq in H_eq.
        unfold in_str; simpl.
        rewrite H_eq.
        reflexivity.
      * unfold in_str; simpl.
        destruct (x =? a); auto.
Qed.


Lemma negb_in_str__NotIn x xs :
  negb (in_str x xs) = true ->
  x ∉ xs
.
Proof.
  induction xs.
  - simpl. auto.
  - intros.
    intro H_in.
    rewrite negb_iff in *.
    destruct H_in as [H_eq | H_tail].
    + apply in_str__false_hd in H.
      apply eq_sym, eqb_eq in H_eq.
      congruence.
    + apply in_str__false_tl in H.
      intuition.
Qed.



Lemma app_cons_app_app {A} xs ys (x : A) :
  xs ++ x :: ys = xs ++ [x] ++ ys.
Proof.
  induction xs.
  - reflexivity.
  - simpl.
    rewrite IHxs.
    reflexivity.
Qed.

Lemma cons_app {A} (x :A) xs : x :: xs = [x] ++ xs.
Proof.
  apply app_cons_app_app with (xs := nil).
Qed.

Lemma lookup_eq {X} k (v : X) kvs : lookup k ((k, v) :: kvs) = Some v.
Proof.
  simpl.
  destruct (k =? k) eqn:H_eqb.
  - reflexivity.
  - rewrite eqb_neq in H_eqb.
    contradiction.
Qed.

Lemma lookup_neq {X} k1 k2 (v : X) kvs : k1 <> k2 -> lookup k1 ((k2, v) :: kvs) = lookup k1 kvs.
Proof with auto.
  intros H_neq.
  simpl.
  rewrite eqb_sym.
  rewrite <- eqb_neq in H_neq.
  rewrite H_neq...
Qed.

Lemma In__lookup_append {X : Type} k (kvs : list (string * X)) ys zs :
  In k (map fst kvs) ->
  lookup k (kvs ++ ys) = lookup k (kvs ++ zs).
Proof.
  intros H_In.
  induction kvs.
  - inversion H_In.
  - destruct a.
    destruct (string_dec k s); subst.
    + simpl.
      assert (H : s =? s = true). { rewrite eqb_eq. reflexivity. }
      rewrite H.
      reflexivity.
    + simpl.
      assert (H : s =? k = false). { rewrite -> eqb_sym. rewrite eqb_neq. assumption. }
      rewrite H.
      destruct H_In.
        * destruct H0. contradiction.
        * auto.
Qed.

Lemma notIn__lookup_append {X : Type} k (kvs : list (string * X)) ys :
     ~ In k (map fst ys) -> lookup k (ys ++ kvs) = lookup k kvs.
Proof with auto.
  intros H_notIn.
  induction ys...
  destruct a.
  simpl in H_notIn.
  destruct (string_dec s k).
  - assert (s = k \/ In k (map fst ys)) by auto.
    contradiction.
  - rewrite <- eqb_neq in n.
    simpl.
    rewrite n.
    assert (~ In k (map fst ys))...
Qed.

Lemma lookup_append_cong {X : Type} k (new kvs kvs' : list (string * X)) :
  lookup k kvs = lookup k kvs' ->
  lookup k (new ++ kvs) = lookup k (new ++ kvs').
Proof with auto.
  intros H_kvs_kvs'.
  induction new...
  - destruct a.
    destruct (eqb s k) eqn:H_eqb.
    all: simpl; rewrite H_eqb...
Qed.

Lemma lookup__not_in {K} x (xs : list (string * K)) :
  lookup x xs = None -> ~ In x (map fst xs).
Proof.
  intros H_lookup H_in.
  induction xs.
  - inversion H_in.
  - destruct a as [k v] eqn:H_eq.
    destruct (string_dec x k).
    + subst x.
      rewrite lookup_eq in H_lookup.
      discriminate.
    + rewrite lookup_neq in H_lookup; try assumption.
      simpl in H_in.
      destruct H_in.
      * symmetry in H. auto.
      * auto.
Qed.

Lemma not_in__lookup {K} x (xs : list (string * K)) :
  ~ In x (map fst xs) -> lookup x xs = None.
Admitted.

Definition inclusion {A : Type} (m m' : list (string * A)) :=
  forall x v, lookup x m = Some v -> lookup x m' = Some v.

Lemma inclusion_unfold {A : Type} (m m' : list (string * A)) x v:
  inclusion m m' -> lookup x m = Some v -> lookup x m' = Some v.
Proof.
  auto.
Qed.

Lemma inclusion_tail {A : Type} (x : string * A) m m' :
  inclusion m m' ->
  inclusion (x :: m) (x :: m').
Proof.
  intro H_incl.
  destruct x.
  intros k v.
  destruct (s =? k) eqn:H_eqb.
  all: simpl; rewrite H_eqb; auto.
Qed.

Lemma inclusion_refl {A} (xs : list (string * A)) :
  inclusion xs xs.
Proof with auto.
  unfold inclusion.
  intros.
  induction xs...
Qed.

Lemma inclusion_trans : forall A (m1 m2 m3 : list (string * A)), inclusion m1 m2 ->
  inclusion m2 m3 -> inclusion m1 m3.
Proof with auto.
  unfold inclusion...
Qed.

Lemma inclusion_cons A (m m' : list (string * A)) kv :
  inclusion m m' -> inclusion (kv :: m) (kv :: m').
Proof with auto.
  intros H_incl.
  unfold inclusion.
  intros y vy H_lookup_y.
  destruct kv as [x v].
  destruct (eqb x y) eqn:H_eqb.
  all: simpl in *; rewrite H_eqb in *...
Qed.

Lemma inclusion_append {A} m m' (kvs : list (string * A)) :
  inclusion m m' -> inclusion (kvs ++ m) (kvs ++ m').
Proof with auto.
  intros H_incl.
  induction kvs...
  unfold inclusion. intros.
  destruct a.
  destruct (eqb s x) eqn:H_eqb.
  all: simpl in *;
    rewrite H_eqb in *...
Qed.

Lemma inclusion_no_shadow {K} x k (xs ys : list (string * K)) :
  inclusion xs ys -> ~ In x (map fst xs) -> inclusion xs ((x, k):: ys).
Admitted.

Lemma inclusion_contra {K} x (xs ys : list (string * K)) :
  inclusion xs ys ->
  lookup x ys = None ->
  lookup x xs = None.
Proof.
  intros H_incl H_ys.
  destruct (lookup x xs) eqn:H_xs.
  - apply H_incl in H_xs.
    rewrite H_ys in H_xs.
    discriminate.
  - reflexivity.
Qed.

Lemma inclusion_swap {A} (x y : string) (K L : A) m  :
  x <> y ->
  inclusion ((x, K) :: (y, L) :: m) ((y, L) :: (x, K) :: m).
Admitted.

(* Second element is shadowed and hence ignored by lookup *)
Lemma inclusion_shadow_left {A} (x : string) (K L : A) m  :
  inclusion ((x, K) :: (x, L) :: m) ((x, K) :: m).
Admitted.

(* Second element is shadowed and hence ignored by lookup *)
Lemma inclusion_shadow_right {A} (x : string) (K L : A) m  :
  inclusion ((x, K) :: m) ((x, K) :: (x, L) :: m).
Admitted.

Lemma cons_shadow {A} k (x y : A) xs:
  inclusion ((k, x) :: (k, y) :: xs) ((k, x) :: xs).
Proof with auto.
  unfold inclusion.
  intros l w H_lookup.
  simpl in *.
  destruct (k =? l) eqn:H_eqb...
Qed.

Lemma append_shadow {A} k (v : A) xs ys :
  In k (map fst xs) -> inclusion (xs ++ ((k, v) :: ys)) (xs ++ ys).
Proof.
Admitted.

Lemma cons_permute A (m : list (string * A)) x1 x2 v1 v2 :
  x2 <> x1 -> inclusion ((x1, v1) :: (x2 , v2) :: m) ((x2, v2) :: (x1, v1) :: m).
Proof with auto.
  unfold inclusion.
  intros H_neq x v.
  destruct (x1 =? x) eqn:H_x_x1;
  destruct (x2 =? x) eqn:H_x_x2.
  all: try (simpl; rewrite H_x_x1, H_x_x2; auto).
  assert (x2 = x1).
    { rewrite -> eqb_eq in *.
      apply eq_sym in H_x_x2.
      transitivity x...
    }
  contradiction.
Qed.

Lemma append_permute A (m : list (string * A)) k (v : A) xs ys:
  ~ (In k (map fst xs)) -> inclusion (xs ++ ((k, v) :: ys)) ((k, v) :: xs ++ ys) .
Admitted.

(* Like append_permute, but the rhs list may change up to inclusion *)
Lemma append_permute__inclusion2 A k (v : A) xs ys ys':
  List.inclusion ys ys' -> ~ (In k (map fst xs)) -> List.inclusion ((k, v) :: xs ++ ys) (xs ++ ((k, v)::ys')).
Admitted.

Definition equivalent {A : Type} (m m' : list (string * A)) :=
  inclusion m m' /\ inclusion m' m.

Lemma equivalent_refl : forall A (m : list (string * A)), equivalent m m.
Proof.
  unfold equivalent.
  auto using inclusion_refl.
Qed.

Lemma equivalent_sym : forall A (m m' : list (string * A)), equivalent m m' -> equivalent m' m.
Proof.
  unfold equivalent, inclusion.
  intros.
  easy.
Qed.

Lemma equivalent_trans : forall A (m1 m2 m3 : list (string * A)), equivalent m1 m2 ->
  equivalent m2 m3 -> equivalent m1 m3.
Proof.
  unfold equivalent, inclusion.
  intros.
  destruct H, H0.
  auto.
Qed.

Require Import Coq.Classes.RelationClasses.

Global Instance inclusion_reflexive : forall (A : Type), Reflexive (@inclusion A) := @inclusion_refl.
Global Instance inclusion_transitive : forall (A : Type), Transitive (@inclusion A) := inclusion_trans.

Global Instance equivalent_reflexive : forall (A : Type), Reflexive (@equivalent A) := equivalent_refl.
Global Instance equivalent_symmetric : forall (A : Type), Symmetric (@equivalent A) := equivalent_sym.
Global Instance equivalent_transitive : forall (A : Type), Transitive (@equivalent A) := equivalent_trans.
Global Instance equivalent_equivalence : forall (A : Type), Equivalence (@equivalent A) := { }.

(*
Add Parametric Relation (A : Type) : (list (string * A)) (equivalent)
  reflexivity proved by (equivalent_refl A)
  symmetry proved by (equivalent_sym A)
  transitivity proved by (equivalent_trans A) as tests.

Definition my_setoid : Setoid := _.
Global Instance equivalent_Setoid : forall (A : Type), Setoid (@equivalent A) := _.
*)

Definition subset {A} (xs ys : list A) := forall x, In x xs -> In x ys.

Notation "xs \ ys" := (remove_many string_dec ys xs) (at level 10).

Notation "xs ⊆  ys" := (subset xs ys) (at level 70).


Section DISJOINT.

Context {A : Set}.

Definition disjoint (xs ys : list A) : Prop :=
  Forall (fun v => ~ In v ys) xs.


Lemma disjoint_nil_l ys :
  disjoint ys [].
Proof. Admitted.

Lemma disjoint_nil_r ys :
  disjoint ys [].
Proof. Admitted.

Lemma disjoint_cons_l x xs ys :
  x ∉ ys ->
  disjoint xs ys ->
  disjoint (x::xs) ys
.
Proof. Admitted.

Lemma disjoint_app_r xs ys zs :
  disjoint xs ys ->
  disjoint xs zs ->
  disjoint xs (ys ++ zs)
.
Proof. Admitted.

Lemma disjoint_app_l xs ys zs :
  disjoint xs zs ->
  disjoint ys zs ->
  disjoint (xs ++ ys) zs
.
Proof. Admitted.

Lemma disjoint_cons_r y xs ys :
  y ∉ xs ->
  disjoint xs ys ->
  disjoint xs (y :: ys)
.
Proof.
Admitted.


Lemma disjoint_uncons_l x xs ys :
  disjoint (x::xs) ys ->
  disjoint xs ys
.
Proof. Admitted.


Lemma disjoint_uncons_r y xs ys :
  disjoint xs (y::ys) ->
  disjoint xs ys
.
Proof. Admitted.

Lemma disjoint_comm xs ys :
  disjoint xs ys ->
  disjoint ys xs
.
Proof.
Admitted.

End DISJOINT.

Section Subset.

(* TODO: This should subsume `inclusion` and its lemmas, see if they can be
   unified *)

  Lemma subset_refl {A} {xs : list A} :
    xs ⊆ xs.
  Admitted.
  Lemma subset_trans {A} {xs ys zs : list A} :
    xs ⊆ ys ->
    ys ⊆ zs ->
    xs ⊆ zs.
  Admitted.

  Lemma In_append_or {A} {x} {xs ys : list A} :
    x ∈ xs \/ x ∈ ys <->
    x ∈ (xs ++ ys).
  Admitted.

  Lemma subset_or {A} {xs ys zs : list A} :
    (∀ x, x ∈ xs -> x ∈ ys \/ x ∈ zs) <->
    xs ⊆ ys ++ zs.
  Admitted.

  Lemma subset_cons {A} {xs ys} {x : A}:
   xs ⊆ (x :: ys) ->
   x ∉ xs ->
   xs ⊆ ys.
  Admitted.

  Lemma remove_subset {xs ys} {x : string}:
   xs ⊆ ys ->
   (remove string_dec x xs) ⊆ ys.
  Admitted.

  Lemma subset_append {A} {xs ys zs : list A} :
    xs ⊆ zs ->
    ys ⊆ zs ->
    (xs ++ ys) ⊆ zs.
  Admitted.

  Lemma subset_closed_append {A} {xs ys zs ws : list A} :
    xs ⊆ ys ->
    zs ⊆ ws ->
    xs ++ zs ⊆ ys ++ ws.
  Admitted.

  Lemma subset_closed_append_l {A} {xs ys zs : list A} :
    xs ⊆ ys ->
    zs ++ xs ⊆ zs ++ ys.
  Admitted.

  Lemma subset_closed_append_r {A} {xs ys zs : list A}:
    xs ⊆ ys ->
    xs ++ zs ⊆ ys ++ zs.
  Admitted.


  Lemma subset_append_l {A} (xs ys zs : list A) :
    xs ⊆ ys ->
    xs ⊆ zs ++ ys.
  Admitted.

  Lemma subset_append_r {A} (xs ys zs : list A) :
    xs ⊆ ys ->
    xs ⊆ ys ++ zs.
  Admitted.

  Lemma subset_cons_remove {A} (x : A) xs eq_dec :
    xs ⊆ (x :: remove eq_dec x xs).
  Admitted.

  Lemma empty_subset {A} {xs : list A} :
    [] ⊆ xs.
  Admitted.

  Lemma in_remove x y xs :
    x ∈ xs /\ x ≠ y <->
    x ∈ remove string_dec y xs.
  Proof.
  split; intros.
  - apply in_in_remove; intuition.
  - eapply in_remove.
    exact H.
  Qed.

  Lemma not_in_remove : ∀ x y xs,
    x ∉ xs \/ x = y <->
    x ∉ remove string_dec y xs.
  Proof.
  split; intros.
  -
    destruct H.
    + induction xs; auto.
      intros.
      simpl.
      destruct (string_dec y a).
      * intuition.
      * rewrite not_in_cons in *.
        intuition.
    + unfold not.
      intros.
      induction xs.
      * intuition.
      * rewrite <- in_remove in H0.
        intuition.
  - induction xs.
    + intuition.
    + simpl in H.
      destruct (string_dec y a).
      * subst a.
        apply IHxs in H. clear IHxs.
        destruct H.
        ** destruct (string_dec x y).
          *** intuition.
          *** left.
              rewrite not_in_cons.
              intuition.
        ** intuition.
      *
        rewrite not_in_cons in H.
        rewrite not_in_cons.
        destruct H.
        apply IHxs in H0. clear IHxs.
        intuition.
  Qed.

  Lemma not_in_app : ∀ A (x : A) xs xs',
    x ∉ (xs ++ xs') <->
    x ∉ xs /\ x ∉ xs'.
  Proof.
    split.
    - intuition.
    - intros.
      unfold not. intros.
      destruct H.
      apply in_app_or in H0.
      intuition.
  Qed.

  Lemma in_remove_many x xs ys :
    x ∈ xs /\ x ∉ ys <->
    x ∈ xs \ ys.
  Proof.
    split; intros.
    - induction ys.
      + intuition.
      + rewrite not_in_cons in H.
        simpl.
        rewrite <- in_remove.
        intuition.
    - induction ys.
      + intuition.
      + simpl in H.
        rewrite <- in_remove in H.
        rewrite not_in_cons.
        intuition.
  Qed.

  Lemma in_singleton_eq {A} {x y : A} :
    x ∈ [y] ->
    x = y.
  Proof.
    intros H_In.
    inversion H_In.
    - symmetry. assumption.
    - contradiction.
  Qed.

  Lemma In_singleton {A} {x : A} :
    x ∈ [x].
  Proof.
    constructor.
    reflexivity.
  Qed.


  Lemma subset_remove_many_append xs ys :
    xs ⊆ (ys ++ xs \ ys).
  Admitted.

  Lemma subset_remove_many xs ys zs :
    xs ⊆ (ys ++ zs) ->
    xs \ ys  ⊆ zs.
  Admitted.

  Lemma subset_rev_l {A} (xs ys : list A) :
    xs ⊆ ys <-> rev xs ⊆ ys.
  Admitted.

  Lemma subset_rev_r {A} (xs ys : list A) :
    xs ⊆ ys <-> xs ⊆ rev ys.
  Admitted.

  Lemma subset_rev_append_l A (xs ys zs : list A):
    xs ⊆ rev ys ++ zs ->
    xs ⊆ ys ++ zs.
  Admitted.

  Lemma subset_rev_append_l' A (xs ys zs : list A):
    xs ⊆ ys ++ zs ->
    xs ⊆ rev ys ++ zs.
  Admitted.

  Lemma subset_remove_many_l xs ys zs :
    xs ⊆ zs ->
    xs \ ys ⊆ zs.
  Admitted.

  Lemma remove_many_app_comm : ∀ xs ys zs, xs \ (ys ++ zs) = xs \ (zs ++ ys).
  Admitted.

  Lemma remove_many_app_r : ∀ xs ys zs, xs \ (ys ++ zs) = (xs \ ys) \ zs.
  Admitted.

  Lemma remove_many_app : ∀ xs ys zs, (ys ++ zs) \ xs = ys \ xs ++ zs \ xs.
  Admitted.

  Lemma remove_many_empty : ∀ xs,
    [] \ xs = [].
  Admitted.


End Subset.

Create HintDb subset.
Hint Resolve
  subset_refl
  remove_subset
  subset_append
  subset_remove_many
  subset_remove_many_append
  subset_closed_append_l
  subset_closed_append_r
  subset_append_l
  subset_append_r
  subset_cons_remove
  empty_subset : subset.


Fixpoint lookup' {A X : Type} (A_eqb : A -> A -> bool) (k : A) (l : list (A * X)) : option X :=
  match l with
  | nil => None
  | (j,x) :: l' => if A_eqb j k then Datatypes.Some x else lookup' A_eqb k l'
  end.

Inductive Lookup {A B :Type} (k : A) (v : B) : list (A * B) -> Prop :=
  | Here    : forall {kvs}, Lookup k v ((k, v) :: kvs)
  | There   : forall {k' v' kvs}, ~ (k = k') -> Lookup k v kvs -> Lookup k v ((k', v') :: kvs)
.

Lemma Lookup_lookup : forall A k (v : A) kvs, Lookup k v kvs <-> lookup k kvs = Some v.
Proof.
  intros. generalize dependent k. generalize dependent v.
  induction kvs; split; intros; simpl; inversion H.
    - rewrite eqb_refl. reflexivity.
    - rewrite eqb_sym. apply (eqb_neq k k') in H2. rewrite H2. apply IHkvs. apply H3.
    - destruct a as [k' v']. destruct (k' =? k) eqn:E.
      + apply eqb_eq in E. inversion H1. subst. apply Here.
      + apply There.
        * rewrite eqb_sym in E. apply eqb_neq in E. apply E.
        * apply IHkvs in H1. apply H1.
Qed.


Definition inclusion_empty (A : Type) (m : list (string * A)) : inclusion [] m.
Proof.
  unfold inclusion. intros. inversion H.
Qed.



Lemma Lookup_functional : forall A B (k : A) (v v' : B) kvs,  Lookup k v kvs -> Lookup k v' kvs -> v = v'.
Proof.
  induction kvs; intros; inversion H.
    - subst. inversion H0.
      + reflexivity.
      + exfalso. apply H3. reflexivity.
    - subst. inversion H0.
      + apply H3 in H2. inversion H2.
      + apply IHkvs. apply H4. apply H7.
Qed.

Lemma Lookup_unique : forall A B (k : A) (v : B) kvs (P P' : Lookup k v kvs), P = P'.
Admitted.

Lemma Lookup_In : forall A B (k : A) (v : B) kvs, NoDup kvs -> In (k, v) kvs <-> Lookup k v kvs.
Admitted.

Fixpoint drop {X:Type} (n:string) (nxs:list (string * X)) : list (string * X) :=
  match nxs with
  | nil => nil
  | (n',x) :: nxs' => if n' =? n then drop n nxs' else (n',x) :: (drop n nxs')
  end.

Fixpoint mdrop {X:Type} (ns : list string) (nxs: list (string * X)) : list (string * X) :=
  match ns with
  | nil => nxs
  | n :: ns' =>
      mdrop ns' (drop n nxs)
  end.

Function forall2b {A} (p : A -> A -> bool) (xs : list A) (ys : list A) : bool :=
  match xs, ys with
    | []       , []        => true
    | (x :: xs), (y :: ys) => (p x y && forall2b p xs ys)%bool
    | _        , _         => false
  end.

(* Instead of requiring a general decidable relation dec_R x x' <-> R x x', we require
   that the elements in the list xs have decidable equality. This makes mutual
   inductive proofs possible *)
Definition forall2b_Forall2_Forall
  a R (dec_R : a -> a -> bool) xs xs'
  (H_sound_xs : Forall (fun x => forall x', dec_R x x' = true <-> R x x') xs) :
  forall2b dec_R xs xs' = true <-> Forall2 R xs xs'.
Proof.
  revert xs'.
  induction xs.
  intros xs'.
  - simpl.
    destruct xs'; split; inversion 1.
    + constructor.
    + reflexivity.
  - simpl.
    destruct xs'; split; try solve [inversion 1].
    + intros H_eqb.
      rewrite andb_true_iff in H_eqb. destruct H_eqb.
      inversion_clear H_sound_xs.
      specialize (IHxs H2).
      rewrite H1 in H. subst.
      specialize (IHxs xs').
      destruct IHxs.
      f_equal.
      auto.
    + intros.
      inversion H; subst.
      rewrite andb_true_iff.
      inversion H_sound_xs; subst.
      rewrite H2.
      rewrite IHxs; auto.
Qed.

(* TODO, make this bi-implication *)
Lemma forall2b_Forall2
  (A : Type)
  (f : A -> A -> bool)
  (P : A -> A -> Prop)
  (f_P : forall x y, f x y = true -> P x y)
  (xs ys : list A) :
    forall2b f xs ys = true -> Forall2 P xs ys.
Proof.
  intros.
  revert dependent ys.
  induction xs; intros.
  - simpl. destruct ys.
    + auto.
    + simpl in H. inversion H.
  - intros.
    simpl in H. destruct ys.
    + inversion H.
    + rewrite andb_true_iff in H.
      destruct H as [H_hd H_tl].
      apply f_P in H_hd.
      auto using Forall2.
Qed.


Inductive Forall3 [A B C : Type] (R : A -> B -> C -> Prop) : list A -> list B -> list C -> Prop :=
  | Forall3_nil : Forall3 R [] [] []
  | Forall3_cons : forall (x : A) (y : B) (z : C) (l : list A) (l' : list B) (l'' : list C),
                   R x y z -> Forall3 R l l' l'' -> Forall3 R (x :: l) (y :: l') (z :: l'').

Arguments Forall3_nil [A B C]%type_scope R%function_scope.
Arguments Forall3_cons [A B C]%type_scope [R]%function_scope
  x y z [l l' l'']%list_scope _ _.


Lemma mdrop_nil : forall X ns,
    @mdrop X ns nil = nil.
Proof. induction ns; auto. Qed.

Lemma mdrop_app : forall A (xs ys : list string) (zs : list (string * A)),
  mdrop (xs ++ ys) zs = mdrop ys (mdrop xs zs).
Proof.
  intros A xs ys.
  induction xs.
  - reflexivity.
  - simpl.
    eauto.
Qed.

Lemma drop_idempotent : forall X x (ns : list (string * X)), drop x (drop x ns) = drop x ns.
Proof with auto.
  intros.
  induction ns...
  - destruct a as [y v].
    destruct (y =?x) eqn:Heqb.
    + simpl; rewrite Heqb...
    + repeat (simpl; rewrite Heqb).
      congruence.
Qed.


Definition elem {A} (A_eqb : A -> A -> bool) (x : A) (xs : list A) :=
  match find (A_eqb x) xs with
    | None   => false
    | Some _ => true
  end.

(* A specialized version of In for names/strings *)
Inductive NameIn (x : string) : list string -> Prop :=
  | NI_Here  : forall {xs}, NameIn x (x :: xs)
  | NI_There : forall {x' xs}, x <> x' -> NameIn x xs -> NameIn x (x' :: xs).

QCDerive DecOpt for (NameIn x xs).

Instance NameIn_DecOpt_sound x xs : DecOptSoundPos (NameIn x xs).
Proof. derive_sound. Qed.

Instance NameIn_DecOpt_complete x xs : DecOptCompletePos (NameIn x xs).
Proof. derive_complete. Qed.

Instance NameIn_DecOpt_monotonic x xs : DecOptSizeMonotonic (NameIn x xs).
Proof. derive_mon. Qed.



Lemma NameIn_In_string_equal : forall xs x, NameIn x xs <-> @In string x xs.
Proof with auto using NameIn.
  induction xs; split; intros; simpl; inversion H; subst...
    - apply IHxs in H3...
    - destruct (string_dec x a); subst...
      apply NI_There...
      apply IHxs...
Qed.


(***** Set/prop trick for In ******)
Inductive InSet {A : Type} (x : A) : list A -> Type :=
| InSet_head : forall l, InSet x (x :: l)
| InSet_tail : forall y l, InSet x l -> InSet x (y :: l).

Lemma in_app_or_set {A} (x : A) (l1 l2 : list A) :
  InSet x (l1 ++ l2) -> sum (InSet x l1) (InSet x l2).
Proof.
    induction l1 as [|h t IH]; simpl; intros H.
  - right; exact H.
  - inversion H; subst; clear H.
    + left; apply InSet_head.
    + destruct (IH X) as [H'|H'].
      * left; apply InSet_tail; exact H'.
      * right; exact H'.
Qed.

Definition in_dec_set {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A) :
  sum (InSet x l) ((InSet x l) -> False).
Proof.
  induction l as [|h t IH].
  - right; intros H; inversion H.
  - destruct (eq_dec x h) as [-> | Hneq].
    + left; apply InSet_head.
    + destruct IH as [Hin | Hnin].
      * left; apply InSet_tail; exact Hin.
      * right; intros H; inversion H; subst; [contradiction | apply Hnin; assumption].
Defined.

Theorem in_set_to_prop {A} {x : A} {l : list A} :
  InSet x l -> In x l.
Proof.
  intros.
  induction l as [|h t IH]; simpl in *.
  - inversion X.
  - inversion X; subst.
    + left; reflexivity.
    + right; apply IH; assumption.
Qed.

Fixpoint in_dec_f {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A) :
  bool:=
  match l with
  | [] => false
  | h :: hs =>
      match eq_dec x h with
      | left _ => true
      | right _ => in_dec_f eq_dec x hs
      end
  end.

Theorem in_dec_f_sound {A} {eq_dec : forall x y : A, {x = y} + {x <> y}} {x : A} {l : list A} :
  in_dec_f eq_dec x l = true -> InSet x l.
Proof.
  induction l as [|h t IH]; simpl; intros H.
  - discriminate H.
  - destruct (eq_dec x h) as [-> | Hneq].
    + apply InSet_head.
    + apply InSet_tail.
      apply IH.
      auto.
Qed.

Theorem in_prop_to_set {x : string} {l : list string} :
  In x l -> InSet x l.
Proof.
  intros.
  destruct (in_dec_f string_dec x l) eqn:BU.
  - eapply in_dec_f_sound; eauto.
  - exfalso.
    induction l.
    + inversion H.
    + inversion H; subst.
      simpl in BU.
      destruct (string_dec x x).
      * discriminate BU.
      * contradiction.
      * assert (in_dec_f string_dec x l = false).
        {
          simpl in BU.
          destruct (string_dec x a).
          - discriminate BU.
          - auto.
        }
        eapply IHl; auto.
Qed.
