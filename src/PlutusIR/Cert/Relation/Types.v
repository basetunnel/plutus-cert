From PlutusCert Require Import
  Equality
  PlutusIR
  Contextual
.

Import Utf8_core.


Record rel_sound : Type :=
  mk_rel_sound {
    rs_rel : term -> term -> Prop;
    rs_decb : term -> term -> bool;
    rs_equiv : ∀ s t,
      rs_decb s t = true -> rs_rel s t;
  }
.

Record rel_decidable : Type :=
  mk_rel_decidable {
    rd_rel : term -> term -> Prop;
    rd_decb : term -> term -> bool;
    rd_equiv : ∀ s t,
      rd_decb s t = true <-> rd_rel s t;
  }
.
(* Every decidable relation is a sound relation *)
Definition rel_decidable__sound : rel_decidable -> rel_sound := fun rd =>
  match rd with
  | mk_rel_decidable R dec equiv => mk_rel_sound R dec (fun s t => proj1 (equiv s t))
  end
.

Definition rd_dec (rd : rel_decidable) (t t' : term) : option (rd_rel rd t t') :=
  match rd_decb rd t t' as b return rd_decb rd t t' = b -> option (rd_rel rd t t') with
    | true  => fun H => Some (proj1 (rd_equiv rd t t') H)
    | false => fun _ => None
  end eq_refl.

Record rel_verified : Type :=
  mk_rel_verified {
    rv_rd : rel_decidable;
    rv_correct : ∀ s t,
      rv_rd.(rd_rel) s t -> ∀ Δ Γ T, Δ ,, Γ |- s =ctx t : T
  }
.

Definition rv_dec (rv : rel_verified) (t t' : term)
: option (∀ Δ Γ T, Δ ,, Γ |- t =ctx t' : T) :=
  match rd_dec (rv_rd rv) t t' with
    | Some deriv => Some (rv_correct rv t t' deriv)
    | None => None
  end
.

Definition dec_correct (rd : rel_verified) t t' :
  rd_decb (rv_rd rd) t t' = true ->
  ∀ Δ Γ T, Δ ,, Γ |- t =ctx t' : T :=
  fun H =>
        let deriv := proj1 (rd_equiv (rv_rd rd) _ _) H in
        let ctx_equiv := (rv_correct rd) _ _ deriv in
        ctx_equiv.

Definition dec_rel (rd : rel_decidable) t t' :
  rd_decb rd t t' = true -> rd_rel rd t t' :=
  fun H => proj1 (rd_equiv rd _ _) H.
