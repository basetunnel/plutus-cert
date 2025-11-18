Require Import
  Lists.List
  Strings.String
.
From PlutusCert Require Import
  Util
  Util.Tactics
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

Definition dec_unused_in (b : binding) (t' : term) : bool :=
  forallb (fun x => negb (existsb (String.eqb x) (fv t'))) (bvb b) &&
  forallb (fun x => negb (existsb (String.eqb x) (ftv t'))) (btvb b)
.

Section Bindings.

  Context (dec_Term : term -> term -> bool).


  (* t' is the post-term let body *)
  Function dec_Bindings_NonRec (bs bs' : list binding) (t' : term) : bool :=
    match bs, bs' with
    | b :: bs, b' :: bs' =>
        if Compat.dec_binding dec_Term b b'
        then dec_Bindings_NonRec bs bs' t'
        else
          dec_pure_binding [] b &&
          dec_unused_in b (Let NonRec bs' t') &&
          dec_Bindings_NonRec bs (b' :: bs') t'
    | [], [] => true
    | b :: bs, [] =>
          dec_pure_binding [] b &&
          dec_unused_in b t' &&
          dec_Bindings_NonRec bs [] t'
    | [], _ => (* Left-over bindings in post-term, impossible *)
        false
    end.

End Bindings.

Function dec_Term (t t' : term) {struct t} :=
  match t, t' with
  | Let NonRec bs t, Let NonRec bs' t' =>
      if dec_Bindings_NonRec dec_Term bs bs' t'
      then dec_Term t t'
      else false
  | _, _ => Compat.dec dec_Term t t'
  end
.

Lemma unused_sound b t' : dec_unused_in b t' = true -> unused_in b t'.
Admitted.

Lemma pure_sound b : dec_pure_binding [] b = true -> pure_binding [] b.
Admitted.

Lemma dec_Bindings_NonRec_sound bs bs' t'
  (dec_Term_sound : forall t t', dec_Term t t = true -> dc t t')
  : dec_Bindings_NonRec dec_Term bs bs' t' = true
  -> dc_NonRec t' bs bs'.
Admitted.

Definition P_Term := fun t => forall t', dec_Term t t' = true -> dc t t'.
Definition P_Binding := fun b => forall b', Compat.dec_binding dec_Term b b' = true -> Compat_Binding dc b b'.

Lemma dec_Term_sound : forall t, P_Term t.
Proof.
  apply term__ind with (P := P_Term) (Q := P_Binding).
  all: intros.
  all: unfold P_Term, P_Binding.

  (* First do all the Term cases *)
  all: match goal with
    | |- (forall (_ : binding), _) => shelve
    | _ => idtac
    end.
  all: intros t'; destruct t'.

  (* Solve impossible cases *)
  all: rewrite dec_Term_equation.
  all: try repeat destruct_match.
  all: try inversion 1.

  - (* Let NonRec *) admit.
  - destruct r; intuition.
    destruct_hypos.
    repeat constructor.
    unfold P_Binding in *.
    all: admit. (* should hold from IH's*)
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.
