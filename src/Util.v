Require Import String.
Require Import List.
Require Import PeanoNat.
Require Import Program.Basics.
Set Implicit Arguments.
Import ListNotations.

From QuickChick Require Import QuickChick.
From QuickChick Require Import CheckerProofs.

Ltac inv H := inversion H; try clear H; try subst.

Section list_rect'.
  Variable (a : Type).
  Variable (res_a : a -> Type).
  Variable (res_list : list a -> Type).

  Context
    (H_cons         : forall x xs, res_a x -> res_list xs -> res_list (x :: xs))
    (H_nil          : res_list nil).

Definition list_rect' (elem_rect': forall (x : a), res_a x) :=
  fix list_rect' xs :=
  match xs return res_list xs with
    | nil       => @H_nil
    | cons x xs => @H_cons x xs (elem_rect' x) (list_rect' xs)
  end.
End list_rect'.

(* Type equivalent of Forall *)
Inductive ForallT (A : Type) (P : A -> Type) : list A -> Type :=
  | ForallT_nil : ForallT P nil
  | ForallT_cons : forall {x : A} {l : list A},
                  P x -> ForallT P l -> ForallT P (x :: l).
Arguments ForallT_nil {_} {_}.
Arguments ForallT_cons {_} {_} {_} {_}.
(* Hint Constructors ForallT : core. *)

Definition ForallT_uncons {A P} {x : A} {xs} : ForallT P (x :: xs) -> (P x * ForallT P xs) :=
  fun ps => match ps with
    | ForallT_cons p ps => (p, ps)
  end.

Definition ForallT_hd {A P} {x : A} {xs} : ForallT P (x :: xs) -> P x :=
  fun ps => match ps with
    | ForallT_cons p _ps => p
  end.

Definition ForallT_tl {A P} {x : A} {xs} : ForallT P (x :: xs) -> ForallT P xs :=
  fun ps => match ps with
    | ForallT_cons p ps => ps
  end.


(* ForallT for Props *)
Inductive ForallP (A : Type) (P : A -> Prop) : list A -> Prop :=
  | ForallP_nil : ForallP P nil
  | ForallP_cons : forall {x : A} {l : list A},
                  P x -> ForallP P l -> ForallP P (x :: l).
Arguments ForallP_nil {_} {_}.
Arguments ForallP_cons {_} {_} {_} {_}.
#[export] Hint Constructors ForallP : core.

Definition ForallP_uncons {A P} {x : A} {xs} : ForallP P (x :: xs) -> (P x * ForallP P xs) :=
  fun ps => match ps with
    | ForallP_cons p ps => (p, ps)
  end.

Definition ForallP_hd {A P} {x : A} {xs} : ForallP P (x :: xs) -> P x :=
  fun ps => match ps with
    | ForallP_cons p _ps => p
  end.

Definition ForallP_tl {A P} {x : A} {xs} : ForallP P (x :: xs) -> ForallP P xs :=
  fun ps => match ps with
    | ForallP_cons p ps => ps
  end.


(* TODO: remove ForallP in favour of Forall *)
Lemma ForallP_Forall : forall A P (xs : list A), ForallP P xs <-> Forall P xs.
Proof with eauto using Forall.
  intros.
  split; intros.
  - induction xs...
    inversion H...
  - induction xs...
    inversion H...
Qed.


(* Prove P or Q depending on x *)
Definition sumboolOut (P Q : Prop) (x : {P} + {Q}) :=
  match x return (if x then P else Q) with
    | left x  => x
    | right x => x
  end
.

(* Prove P or unit *)
Definition optionOut (P : Prop) (x : option P) :=
  match x return (if x then P else unit) with
    | Datatypes.Some x => x
    | None             => tt
  end.


(* Applicative combinators for option type *)
Definition option_app (a b : Type): option (a -> b) -> option a -> option b :=
  fun mf mx => match mf, mx with
    | Datatypes.Some f, Datatypes.Some x => Datatypes.Some (f x)
    | _, _ => None
    end.

Definition pure {a : Type} : a -> option a := @Datatypes.Some a.
Definition option_alt a : option a-> option a-> option a :=
  fun x y => if x then x else y.

Notation "x <*> y" := (option_app x y) (at level 81, left associativity).
Notation "f <$> x" := (option_map f x) (at level 80, right associativity).
Notation "x <|> y" := (option_alt x y) (at level 82, right associativity).

Definition sequence_options {a} : list (option a) -> option (list a) :=
  fun os => fold_right (fun mx mxs => cons <$> mx <*> mxs) (pure nil) os.

Fixpoint cat_options {a} (xs : list (option a)) : (list a) :=
  match xs with
    | nil            => nil
    | (Some x) :: xs => x :: cat_options xs
    | None     :: xs => cat_options xs
    end.


(* sumbool to bool *)
Definition sumbool_to_bool (A : Type) (a b : A) : {a = b} + {a <> b} -> bool
  := fun sb => match sb with
  | left _ => true
  | right _ => false
  end
  .
(* sumbool to option *)
Definition sumbool_to_optionl {a b} (x : sumbool a b) : option a :=
  match x with
    | left p => Datatypes.Some p
    | _      => None
  end.

Definition sumbool_to_optionr {a b} (x : sumbool a b) : option b :=
  match x with
    | right p => Datatypes.Some p
    | _       => None
  end.


Definition prod_dec
  (A B : Type)
  (eqA : forall a1 a2 : A, {a1 = a2} + {a1 <> a2})
  (eqB : forall b1 b2 : B, {b1 = b2} + {b1 <> b2})
  : forall x1 x2 : A * B, {x1 = x2} + {x1 <> x2}.
Proof.
  intros [a1 b1] [a2 b2].
  destruct (eqA a1 a2) as [Ha | Ha]; [subst|].
  - destruct (eqB b1 b2) as [Hb | Hb]; [subst|].
    + left. reflexivity.
    + right. intro H; inversion H; auto.
  - right. intro H; inversion H; auto.
Defined.

Definition string_dec_option := fun x y => sumbool_to_optionl (string_dec x y).

(* lookup with evidence *)
Definition lookup_dec {a b} (dec : forall x1 x2 : a, {x1 = x2} + {x1 <> x2}) :
  forall (x : a) (xs : list (a * b)),
  option ({y & In (x, y) xs}).
  Proof.
  induction xs as [ | p ps ].
  - exact None.
  - refine (match p as x return x = p -> _ with
      | (x', y) => fun H =>
        match dec x x' with
          | left eq => Some (existT _ y _)
          | right _ => _ IHps
        end
      end eq_refl
  ); subst.
  { unfold In. tauto. }
  { refine (fun IH => _ <$> IH).
    destruct 1 as [r in_ps].
    exists r. unfold In in *. tauto.
  }
Defined.

(* decision functions that return option instead of sumbool *)

Definition in_dec_option (x : string) (xs : list string) : option (~(In x xs)) :=
  match in_dec string_dec x xs with
  | left _      => None
  | right proof => Some proof
  end.

Definition negneg : forall (p : Prop), p -> ~~p :=
  fun _ proof f => f proof.

Definition map_right {a b c : Prop} : (b -> c) -> sumbool a b -> sumbool a c :=
  fun f e => match e with
    | right x => right (f x)
    | left  x => left x
    end
    .

(* The conclusion has double negation so I can
   use it for things like Forall (lam x => ~In x ys) xs*)
Definition notIn_dec {a} : forall
  (H : forall (x y : a), {x = y} + {x <> y})
  (x : a)
  (xs : list a), {~ In x xs} + {~~In x xs}.
Proof.
  intros. refine (_ (in_dec H x xs)).
  intros.
  apply Sumbool.sumbool_not in x0.
  refine ((fun nn => _) (negneg (p := In x xs))).
  apply (map_right (negneg (p := In x xs))) in x0.
  assumption.
Qed.
(* Proof search for ~(In x xs). Better to use in_dec instead *)
Ltac notIn := intros H; simpl in H; repeat (destruct H as [l | H]; [try (inversion l) | ]); assumption.

Ltac notIn2 :=
  match goal with
    | [ |- ~(In ?x ?xs)] => exact (sumboolOut (in_dec string_dec x xs))
  end.

Lemma existsb_nexists : forall {A : Type} l (f : A -> bool),
    existsb f l = false <-> ~ exists x, In x l /\ f x = true.
Proof.
  intros.
  split.
  - intros.
    intros Hcon.
    apply existsb_exists in Hcon.
    rewrite H in Hcon.
    discriminate.
  - intros.
    induction l.
    + simpl.
      reflexivity.
    + simpl.
      destruct (f a) eqn:Hf.
      * exfalso.
        apply H.
        exists a.
        split. left. auto. auto.
      * simpl.
        eapply IHl.
        intros Hcon.
        eapply H.
        destruct Hcon as [x [HIn Hfx]].
        exists x.
        split. right. auto. auto.
Qed.

Definition remove_list {A} (dec : forall x y, {x = y} + {x <> y}) : list A -> list A -> list A :=
  fun rs xs => fold_right (remove dec) xs rs.

Fixpoint remove_eqb {a} a_eqb xs : list a :=
  match xs with
    | nil => nil
    | x :: xs => if a_eqb x : bool then remove_eqb a_eqb xs else x :: remove_eqb a_eqb xs
  end
  .

Definition is_cons {A} (xs : list A) : Prop := exists y ys, xs = y :: ys.

Definition zip := combine.
Arguments zip {A B}%type_scope (_ _)%list_scope.
Definition unzip := split.
Arguments unzip {A B}%type_scope (_)%list_scope.

Function zip_from {A} (n : nat) (xs : list A) : list (nat * A) :=
  match xs with
    | [] => []
    | x :: xs => (n, x) :: zip_from (S n) xs
  end
.


Definition zip_with {A B C} (f : A -> B -> C) :=
  fix zipw (xs : list A) (ys : list B) : list C :=
    match xs, ys with
      | []       , [] => []
      | (x :: xs), (y :: ys) => f x y :: zipw xs ys
      | _, _ => []
    end.

From Coq Require Import Strings.String.
Open Scope string_scope.

Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => string_of_nat_aux time' n' acc'
      end
  end.
Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n "".
Close Scope string_scope.

Inductive lt_nat : nat -> nat -> Prop :=
  | LtN_N : forall n,
      lt_nat n (S n)
  | LtN_S : forall n m,
      lt_nat n m -> lt_nat n (S m).

QCDerive DecOpt for (lt_nat n m).

Instance lt_nat_DecOpt_sound n m: DecOptSoundPos (lt_nat n m).
Proof. derive_sound. Qed.

Instance lt_nat_DecOpt_complete n m: DecOptCompletePos (lt_nat n m).
Proof. derive_complete. Qed.

Instance lt_nat_DecOpt_monotonic n m: DecOptSizeMonotonic (lt_nat n m).
Proof. derive_mon. Qed.

Definition map2 {A B : Type} (f : A -> B) (ll : list (list A)) : list (list B) :=
  List.map (List.map f) ll.

Inductive NoneSetPair {A B : Type} (P : A -> B -> Prop) : list A -> list B -> Prop :=
  | NoneSP_nil : NoneSetPair P nil nil
  | NoneSP_cons : forall x y xs ys, ~ (P x y) -> NoneSetPair P xs ys -> NoneSetPair P (x :: xs) (y :: ys).

Inductive ForallSet {A : Type} (P : A -> Type) : list A -> Type :=
| ForallS_nil : ForallSet P nil
| ForallS_cons : forall x xs, P x -> ForallSet P xs -> ForallSet P (x :: xs).


(* ForallT for Props *)
Inductive ForallP22 {A : Type} (P : A -> Prop) : list (list A) -> Prop :=
  | ForallP2_nil : ForallP22 P (nil : list (list A))
  | ForallP2_cons : forall {x : list A} {l : list (list A)},
                  ForallP P x -> ForallP22 P l -> ForallP22 P (x :: l).

Inductive ForallSet2 {A : Type} (P : A -> Set) : list (list A) -> Type :=
| ForallS2_nil : ForallSet2 P nil
| ForallS2_cons : forall x xs, ForallSet P x -> ForallSet2 P xs -> ForallSet2 P (x :: xs).

Inductive ForallSetPair {A B : Type} (P : A -> B -> Type) : list A -> list B -> Type :=
| ForallSP_nil : ForallSetPair P nil nil
| ForallSP_cons : forall x y xs ys, P x y -> ForallSetPair P xs ys -> ForallSetPair P (x :: xs) (y :: ys).

Inductive ForallSetPair2 {A B : Type} (P : A -> B -> Type) : list (list A) -> list (list B) -> Type :=
| ForallSP2_nil : ForallSetPair2 P nil nil
| ForallSP2_cons : forall x y xs ys, ForallSetPair P x y -> ForallSetPair2 P xs ys -> ForallSetPair2 P (x :: xs) (y :: ys).

Definition concat2 {A : Type} (l : list (list (list A))) : list A :=
  List.flat_map (@List.concat A) l.

(* Using convoluted fold_left version so that termination checker has a good time*)
Definition flatmap2 {A B : Type} (f : A -> list B) (l : list (list A)) : list B :=
  fold_right (fun (Ts : (list (A))) (acc : list (B)) => List.app

                    ((fold_right (fun (T : A) (acc2 : list (B))  => List.app (f T) acc2) (nil : list (B) )) Ts) acc
                ) (nil : list (B)) l.

Definition fold_right2 {A B : Type} (f : A -> B -> B) (acc : B) (l : list (list A)) : B :=
  fold_right (fun (Ts : list A) (acc2 : B) => fold_right f acc2 Ts) acc l.


(* Monad maybe*)
(* Define the bind function for option type *)
Definition bind {A B : Type} (xx : option A) (f : A -> option B) : option B :=
  match xx with
  | None => None
  | Some a => f a
  end.

(* Define an infix operator for bind *)
Infix ">>=" := bind (at level 50, left associativity).

Definition inb_string (x : string) (xs : list string) : bool :=
  if in_dec string_dec x xs then true else false.

Lemma inb_string_true_iff (x : string) (xs : list string) :
  inb_string x xs = true <-> In x xs.
Proof.
  unfold inb_string.
  destruct (in_dec string_dec x xs); split; intro H; try easy; try congruence.
Qed.

Lemma inb_string_false_iff (x : string) (xs : list string) :
  inb_string x xs = false <-> ~ In x xs.
Proof.
  unfold inb_string.
  destruct (in_dec string_dec x xs); split; intro H; try easy; try congruence.
Qed.
