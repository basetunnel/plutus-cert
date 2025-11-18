From Coq Require Import
  String
  List
  Bool
  Program
  Utf8_core
.

From PlutusCert Require Import
  Util
  Equality
  Purity
  PlutusIR
  PlutusIR.Analysis.Equality
  PlutusIR.Transform.Compat
  Transform.DeadCode.Spec
  Compat
.

Import ListNotations.

Section Bindings.

  Context (dec_Term : term -> term -> bool).

  Definition dec_Binding (b b' : binding) : bool := match b, b' with
    | TermBind s vd t, TermBind s' vd' t' => strictness_eqb s s' && VDecl_eqb vd vd' && dec_Term t t'
    | b, b' => Binding_eqb b b'
    end.

  Definition dec_removed b bs' :=
    if negb (existsb (String.eqb (name b)) bs')
      then dec_pure_binding [] b
      else true.

  Definition dec_was_present b' bs : bool :=
    match find (λ b, String.eqb (name b) (name b')) bs with
      | Datatypes.Some b => dec_Binding b b'
      | None => false
    end
  .

  (* inlined and specialized `find` for termination checking *)
  Definition find_Binding b' :=
  fix find (bs : list binding) : bool :=
    match bs with
    | []      => false
    | b :: bs => if String.eqb (name b) (name b') then dec_Binding b b' else find bs
    end.

  (* This does not work in the termination checker, it doesn't see that b returned by find
     is a structural subterm.
     It would have to fuse the result of find (an option string) with the resulting, which is
     what I did in the above definition*)
  Definition find_Binding' b' bs :=
    match find (λ b, String.eqb (name b) (name b')) bs with
      | Datatypes.Some b => dec_Binding b b'
      | None => false
    end.


  Definition dec_Bindings (bs bs' : list binding) : bool :=
    let bsn := map name bs in
    let bs'n := map name bs' in
    forallb (fun b => dec_removed b bs'n) bs &&
    forallb (fun b' => find_Binding b' bs) bs'.

  (* this did not pass termination checking *)
  (*
    forallb (fun b' =>
    match find (λ b, String.eqb (name b) (name b')) bs with
      | Datatypes.Some b => dec_Binding b b'
      | None => false
    end
    ) bs'
   *)
End Bindings.

Fixpoint dec_Term (x y : term) {struct x} : bool := match x, y with

  | Let r bs t   , Let r' bs' t' =>
      if dec_Bindings dec_Term bs bs'
      then (* same let block, but bindings were removed *)
        recursivity_eqb r r' && dec_Term t t'
      else (* t' is another let block, the whole block in the pre-term was removed *)
        forallb (dec_pure_binding []) bs && dec_Term t y (* Check whether the whole let was removed *)
  | Let _ bs t   , _ =>
     forallb (dec_pure_binding []) bs && dec_Term t y (* Check whether the whole let was removed *)
  | TyInst (TyAbs α k t) τ , TyInst (TyAbs α' k' t') τ'  =>
     String.eqb α α' &&
     Kind_eqb k k' &&
     Ty_eqb τ τ' &&
     dec_Term t t'
  | _ , _ => Compat.dec dec_Term x y

  end
.

Definition dec_Term' : term -> term -> bool :=
  fun t t' => match dec_Term t t' with
    | true => true
    | false => true
  end
.
Lemma dec_Term'_equiv (t t' : term) : dec_Term' t t' = true <-> elim t t'.
Admitted.

Definition P_Term t := forall t', dec_Term t t' = true -> elim t t'.
Definition P_Binding b := forall b', dec_Binding dec_Term b b' = true -> elim_binding b b'.


#[local]
Hint Constructors
  and
: reflection.

Ltac split_hypos :=
  match goal with
  | H : (?x && ?y)%bool = true |- _ => apply andb_true_iff in H; destruct H; split_hypos
  | _ => idtac
  end.


Lemma H_dec_removed bs bs':
    forallb (fun b => dec_removed b (map name bs')) bs = true ->
    ∀ b : binding, In b bs → name_removed b bs' → pure_binding [] b.
Proof with eauto with reflection.
  intros H_dec.
  intros b H_In H_removed.
  unfold dec_removed in H_dec.
  rewrite forallb_forall in H_dec. (* why did rewrite accept a <-> ? was also possible with eapply -> ..., but generated an existential for x *)
  apply H_dec in H_In as H_dec_andb.
  clear H_dec H_In.

  destruct (negb
    (existsb (String.eqb (name b))
       (map name bs')))
       eqn:H_1.
  + apply sound_dec_pure_binding...

  (* contradiction *)
  + apply negb_false_iff in H_1.
    unfold name_removed in *.
    apply existsb_exists in H_1.
    destruct H_1 as [x [H_in H_name_b_eq_x]].
    apply String.eqb_eq in H_name_b_eq_x.
    subst.
    contradiction.
Qed.

Lemma H_find_binding' bs bs' :
  (∀ b, In b bs -> P_Binding b) ->
    forallb (fun b' => find_Binding dec_Term b' bs) bs' = true ->
    ∀ b', In b' bs' ->
       ∃ x, In x bs /\
         name x = name b' /\
         elim_binding x b'
    .
Proof with eauto with reflection.
  intro H_P_Binding.
  rewrite forallb_forall.
  intros H_dec b' H_In.
  apply H_dec in H_In as H_find_b'.
  clear H_dec.
  induction bs as [ | b ].
  - discriminate H_find_b'.
  - simpl in H_find_b'.
    destruct (name b =? name b')%string
      eqn:H_name_eq.

    (* b related to b' *)
    + exists b.
      repeat split...
      * constructor...
      * assert (H : P_Binding b).
        ++ apply H_P_Binding.
           constructor...
        ++ unfold P_Binding in H...


    (* a not related to b' *)
    + apply IHbs in H_find_b' as H_ex. clear IHbs.
      * destruct H_ex as [x [H_x_In [H_eq_name H_elim]]].
        assert (In x (b :: bs)). { apply in_cons... }
        exists x...
      * intros b0 H_b0_in.
        apply H_P_Binding.
        apply in_cons...
Qed.

Create HintDb Hints_bindings.
#[local]
Hint Resolve
  H_dec_removed : Hints_bindings.
#[local]
Hint Constructors
  elim_bindings : Hints_bindings.
#[local]
Hint Resolve
  H_dec_removed
  H_find_binding' : Hints_bindings.
#[local]
Hint Constructors
  elim
  elim_binding
  elim_bindings
  : reflection.

Lemma dec_Bindings_sound' : ∀ bs bs',
  (∀ b, In b bs -> P_Binding b) ->
  dec_Bindings dec_Term bs bs' = true -> elim_bindings bs bs'.
Proof with eauto with Hints_bindings.
  intros H_P_bs bs bs' H.
  simpl in H.
  unfold dec_Bindings in H.
  split_hypos.
  eapply elim_bindings_pure...
Qed.


Lemma dec_TermBind_sound : ∀ s v t b b',
  b = TermBind s v t ->
  P_Term t ->
  dec_Binding dec_Term b b' = true ->
  elim_binding b b'.
Proof with eauto with reflection.
  intros s v t b b' H_eq H_P_Term H_dec.
  unfold P_Term in *.
  subst.
  simpl in H_dec.
  destruct b'.
  all: try discriminate.
  split_hypos.
  assert (s = s0)...
  assert (v = v0)...
  subst...
Qed.

Lemma dec_TypeBind_sound : ∀ v ty b b',
  b = TypeBind v ty ->
  dec_Binding dec_Term b b' = true ->
  elim_binding b b'.
Proof with eauto with reflection.
  intros v ty b b' H_eq H_dec.
  subst.
  destruct b'.
  all: try discriminate.
  simpl in H_dec.
  rewrite Binding_eqb_eq in H_dec.
  inversion H_dec.
  subst...
Qed.

Lemma dec_DatatypeBind_sound : ∀ dtd b b',
  b = DatatypeBind dtd ->
  dec_Binding dec_Term b b' = true ->
  elim_binding b b'.
Proof with eauto with reflection.
  intros dtd b b' H_eq H_dec.
  subst.
  destruct b'.
  all: try discriminate.
  simpl in H_dec.
  rewrite Binding_eqb_eq in H_dec.
  inversion H_dec.
  subst...
Qed.

Lemma all_pure : ∀ bs,
  forallb (dec_pure_binding []) bs = true ->
  Forall (pure_binding []) bs.
Proof.
  intros bs H_dec.
  apply Forall_forall.
  intros b H_In.
  rewrite forallb_forall in H_dec.
  auto using sound_dec_pure_binding.
Qed.

#[local]
Hint Resolve all_pure : reflection.
#[local]
Hint Resolve dec_Bindings_sound' : reflection.
#[local]
Hint Resolve
  dec_TermBind_sound
  dec_TypeBind_sound
  dec_DatatypeBind_sound
  : reflection.
#[local]
Hint Constructors Compat : reflection.

Theorem dec_Term_Binding_sound :
  (∀ t, P_Term t) /\ (∀ b, P_Binding b).
Proof with eauto with reflection.
  apply term__multind with (P := P_Term) (Q := P_Binding).
  all: intros.

  (* P_Term (Let rec bs t) *)
  - unfold P_Term in *.
    intros t' H_dec_Term.
    simpl in H_dec_Term.
    destruct t'; simpl in H_dec_Term.
    all: split_hypos.
    {
      destruct (dec_Bindings dec_Term bs l) eqn:H_dec_bs.
      all: split_hypos.
      (* H_dec_Term: then branch *)
      * split_hypos.

        assert (H_bindings : elim_bindings bs l).
        {
          apply ForallP_Forall in H.
          rewrite -> Forall_forall in H...
        }
        assert (H_eq_rec : rec = r)... subst.
        eapply elim_delete_bindings...

      (* H_dec_Term: else branch *)
      * eapply elim_delete_let...
    }
    all: try eapply elim_delete_let...

  - unfold P_Term.
    destruct t'.
    all: intro H_dec; try discriminate H_dec.
    assert (s = n)... subst...
  - unfold P_Term.
    destruct t'.
    all: intro H_dec; try discriminate H_dec.
    simpl in H_dec. split_hypos.
    assert (s = b)... subst.
    assert (k = k0)... subst...

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    assert (s = b)...
    assert (t = t1)... subst...
  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    idtac...

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    assert (c = c0)... subst...

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    assert (d = d0)... subst...

  - unfold P_Term; destruct t', t; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    all: admit.
    (* assert (t0 = t1)... subst... *)

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    assert (t = t0)... subst...

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    assert (t = t2)... subst.
    assert (t0 = t3)... subst...

  - unfold P_Term; destruct t'; intro H_dec; try discriminate H_dec; simpl in H_dec; split_hypos.
    idtac...

  - admit. (* TODO: Constr *)
  - admit. (* TODO: Case *)
  - unfold P_Binding...
  - unfold P_Binding...
  - unfold P_Binding...
Admitted.

Corollary dec_Term_sound : ∀ t t', dec_Term t t' = true -> elim t t'.
Proof.
  apply dec_Term_Binding_sound.
Qed.

Corollary dec_Binding_sound : ∀ t t', dec_Term t t' = true -> elim t t'.
Proof.
  apply dec_Term_Binding_sound.
Qed.

Theorem dec_Term_complete : ∀ t t', elim t t' -> dec_Term t t' = true.
(* TODO *)
Admitted.

Corollary dec_Term_equiv (t t' : term) : dec_Term t t' = true <-> elim t t'.
Proof.
  constructor.
  - apply dec_Term_sound.
  - apply dec_Term_complete.
Qed.
