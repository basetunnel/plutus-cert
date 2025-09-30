Require Import Coq.Strings.String.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Bool.BoolEq.
Require Import Ascii.
Require Import Eqdep.

From PlutusCert Require Import Util.
Set Implicit Arguments.


Import ListNotations.


From QuickChick Require Import QuickChick.
(*
  Simplification of the names in the AST

  In the AST that we dump in the plutus compiler, variables are represented with the Name type, which is
  a pair of String and Int, where the Int (newtyped as Unique) is used as a compiler detail for cheap name
  comparisons (see Language.PlutusCore.Name.

  We ignore these details and treat names (both terms and types) as strings. The definitions
  below have the same types as the original AST constructors, but forget the structure and
  map to a string.

  This simplifies the representation and especially recognizing equal subterms (since
  compiler passes may reassign unique numbers).

  Possible future approach: it is preferable to have to complete AST including e.g.
  Uniques, but prove that they do not matter for evaluation and then remove them from
  AST

*)

(** recursivity and strictness *)
Inductive recursivity := NonRec | Rec.

Inductive strictness := NonStrict | Strict.

(** Default universe

In the compiler implementation, this is a GADT: the constructors have an index
for their Haskell interpretation. This enforces that only well-kinded types can be constructed.
Since types may have different kinds (e.g. List vs Integer), the GADT is not directly
annotated with its type, but by its (Haskell) kind and its (Haskell) type. The (Haskell) kind
is not visible though, as it is existentially quantified. For example:

    -- Existential quantification of a kind.
    data Esc = forall k. Esc k

    data DefaultUni =
    ...
    | DefaultUniApply ::
       !(DefaultUni (Esc f)) -> !(DefaultUni (Esc a)) -> DefaultUni (Esc (f a))

This approach makes that one can construct plutus types that are of higher kind, e.g.

  Ty_Builtin (SomeTypeIn DefaultUniList)

This is useful for polymorphic function types (see compiler Note [Representing polymorphism]).

For representing constants of builtin types (which can only have kind * ), the compiler has

  data ValueOf uni a = ValueOf !(uni (Esc a)) !a

Since the last argument a is inferred as kind *, the use of GADT for DefaultUniverse will
only construct values of plutus types with the right kind.

In our Coq encoding, we don't use indexed types, as Coq doesn't always have the same
conveniences for pattern matching, and automatisation such as deriving. Instead we can
have dependently typed functions that compute the right types for constructing values
(see uniType and Constant).
*)
Inductive DefaultUni : Type :=
    | DefaultUniInteger
    | DefaultUniByteString
    | DefaultUniString
    | DefaultUniUnit
    | DefaultUniBool
    | DefaultUniProtoList
    | DefaultUniProtoPair
    | DefaultUniData
    | DefaultUniBLS12_381_G1_Element
    | DefaultUniBLS12_381_G2_Element
    | DefaultUniBLS12_381_MlResult

    | DefaultUniApply : DefaultUni -> DefaultUni -> DefaultUni
    .

QCDerive EnumSized for DefaultUni.


Inductive Data :=
  | DataConstr : Z -> list Data -> Data
  | DataMap : list (Data * Data) -> Data
  | DataList : list Data -> Data
  | DataI : Z -> Data
  | DataB : string -> Data
  .

(** Coq interpretation of plutus built-in types of base kind. If not of
* base-kind (or not well-kinded), returns None.
*)
Fixpoint uniType_option (x : DefaultUni) : option Set :=
  match x with
    | DefaultUniInteger    => Some Z
    | DefaultUniByteString => Some (list byte)
    | DefaultUniString => Some (list byte) (* UTF-8 encoded strings *)
    | DefaultUniUnit => Some unit
    | DefaultUniData => Some Data
    | DefaultUniBLS12_381_G1_Element => Some Z
    | DefaultUniBLS12_381_G2_Element => Some Z
    | DefaultUniBLS12_381_MlResult => Some Z
    | DefaultUniBool => Some bool

    | DefaultUniApply DefaultUniProtoList t =>
      match uniType_option t with
        | None => None
        | Some A => Some (list A)
      end

    | DefaultUniApply (DefaultUniApply DefaultUniProtoPair s) t =>
      match uniType_option s, uniType_option t with
      | Some A, Some B => Some (prod A B)
      | _, _ => None
      end

    | DefaultUniApply _ _ => None
    | DefaultUniProtoList => None
    | DefaultUniProtoPair => None
  end
  .
Functional Scheme uniType_option_rect := Induction for uniType_option Sort Type.


(** Coq interpretation of plutus built-in types of base kind. Used for constructing
constants (See term.Constant). Types that are ill-kinded or do not have base kind are
mapped to the empty type, ensuring that Constants of such type can be constructed.
*)
Definition uniType (x : DefaultUni) : Type :=
  match uniType_option x with
    | None => Empty_set
    | Some ty => ty
  end.

(* Constants are coq values of the interpretation of some type in
   DefaultUni *)
Inductive constant :=
  ValueOf : forall (T : DefaultUni), uniType T -> constant.

(** Built-in functions*)
Inductive DefaultFun :=

    | AddInteger
    | SubtractInteger
    | MultiplyInteger
    | DivideInteger
    | QuotientInteger
    | RemainderInteger
    | ModInteger
    | EqualsInteger
    | LessThanInteger
    | LessThanEqualsInteger
    (* Bytestrings *)
    | AppendByteString
    | ConsByteString
    | SliceByteString
    | LengthOfByteString
    | IndexByteString
    | EqualsByteString
    | LessThanByteString
    | LessThanEqualsByteString
    (* Cryptography and hashes *)
    | Sha2_256
    | Sha3_256
    | Blake2b_256
    | VerifyEd25519Signature  (* formerly verifySignature *)
    | VerifyEcdsaSecp256k1Signature
    | VerifySchnorrSecp256k1Signature
    (* Strings *)
    | AppendString
    | EqualsString
    | EncodeUtf8
    | DecodeUtf8
    (* Bool *)
    | IfThenElse
    (* Unit *)
    | ChooseUnit
    (* Tracing *)
    | Trace
    (* Pairs *)
    | FstPair
    | SndPair
    (* Lists *)
    | ChooseList
    | MkCons
    | HeadList
    | TailList
    | NullList
    (* Data *)
    | ChooseData
    | ConstrData
    | MapData
    | ListData
    | IData
    | BData
    | UnConstrData
    | UnMapData
    | UnListData
    | UnIData
    | UnBData
    | EqualsData
    | SerialiseData
    (* Misc monomorphized constructors. *)
    | MkPairData
    | MkNilData
    | MkNilPairData
    (* BLS12_381 operations *)
    (* G1 *)
    | Bls12_381_G1_add
    | Bls12_381_G1_neg
    | Bls12_381_G1_scalarMul
    | Bls12_381_G1_equal
    | Bls12_381_G1_hashToGroup
    | Bls12_381_G1_compress
    | Bls12_381_G1_uncompress
    (* G2 *)
    | Bls12_381_G2_add
    | Bls12_381_G2_neg
    | Bls12_381_G2_scalarMul
    | Bls12_381_G2_equal
    | Bls12_381_G2_hashToGroup
    | Bls12_381_G2_compress
    | Bls12_381_G2_uncompress
    (* Pairing *)
    | Bls12_381_millerLoop
    | Bls12_381_mulMlResult
    | Bls12_381_finalVerify
    (* Keccak_256, Blake2b_224 *)
    | Keccak_256
    | Blake2b_224
    (* Conversions *)
    | IntegerToByteString
    | ByteStringToInteger
.

Definition name := string.
Definition tyname := string.
Definition binderName := string.
Definition binderTyname := string.

(** kinds *)
Inductive kind :=
  | Kind_Base : kind
  | Kind_Arrow : kind -> kind -> kind.

(** Types *)
Inductive ty :=
  | Ty_Var : tyname -> ty
  | Ty_Fun : ty -> ty -> ty
  | Ty_IFix : ty -> ty -> ty
  | Ty_Forall : binderTyname -> kind -> ty -> ty
  | Ty_Builtin : DefaultUni -> ty
  | Ty_Lam : binderTyname -> kind -> ty -> ty
  | Ty_App : ty -> ty -> ty
  | Ty_SOP : list (list ty) -> ty
.

Section ty__ind.
  Unset Implicit Arguments.

  (* Variable for the property to prove about `ty` *)
  Variable (P : ty -> Prop).

  (* Hypotheses for each constructor of `ty` *)
  Context
    (H_Var : forall (X : tyname), P (Ty_Var X))
    (H_Fun : forall (T1 T2 : ty), P T1 -> P T2 -> P (Ty_Fun T1 T2))
    (H_IFix : forall (F T : ty), P F -> P T -> P (Ty_IFix F T))
    (H_Forall : forall (X : binderTyname) (K : kind) (T : ty), P T -> P (Ty_Forall X K T))
    (H_Builtin : forall (T : DefaultUni), P (Ty_Builtin T))
    (H_Lam : forall (X : binderTyname) (K : kind) (T : ty), P T -> P (Ty_Lam X K T))
    (H_App : forall (T1 T2 : ty), P T1 -> P T2 -> P (Ty_App T1 T2))
    (H_SOP : forall (Tss : list (list ty)), Forall (Forall P) Tss -> P (Ty_SOP Tss)).

  (* Main induction principle for `ty` *)
  Fixpoint ty__ind (T : ty) : P T :=
    match T with
    | Ty_Var X => H_Var X
    | Ty_Fun T1 T2 => H_Fun T1 T2 (ty__ind T1) (ty__ind T2)
    | Ty_IFix F T => H_IFix F T (ty__ind F) (ty__ind T)
    | Ty_Forall X K T => H_Forall X K T (ty__ind T)
    | Ty_Builtin T => H_Builtin T
    | Ty_Lam X K T => H_Lam X K T (ty__ind T)
    | Ty_App T1 T2 => H_App T1 T2 (ty__ind T1) (ty__ind T2)
    | Ty_SOP Tss =>
        H_SOP Tss ((fix list_list_ind (tss : list (list ty)) : Forall (Forall P) tss :=
          match tss with
          | nil => Forall_nil _
          | ts :: tss' =>
              Forall_cons _
                ((fix list_ind (ts : list ty) : Forall P ts :=
                   match ts with
                   | nil => Forall_nil _
                   | t :: ts' =>
                       Forall_cons _ (ty__ind t) (list_ind ts')
                   end) ts)
                (list_list_ind tss')
          end) Tss)
    end.

End ty__ind.

(*
  Note [Simplification of AST representation]

  In the Haskell AST, term is a functor and each constructor may have a field of
  the type parameter `a`. This seems to be used for internal metadata on the
  AST. At the moment we don't use it and don't represent it in the AST.

*)

(** Declarations *)
Inductive vdecl := VarDecl : binderName -> ty -> vdecl.
Inductive tvdecl := TyVarDecl : binderTyname -> kind -> tvdecl.
Inductive dtdecl := Datatype : tvdecl -> list tvdecl -> binderName -> list vdecl -> dtdecl.

(** terms and bindings *)
(* Perhaps parametrize to mimic original AST in haskell more closely? We really only need one instantiation for now. *)
(* Context {func : Type} {uni : Type -> Type} {name : Type} {tyname : Type}. *)
Inductive term :=
  | Let      : recursivity -> list binding -> term -> term
  | Var      : name -> term
  | TyAbs    : binderTyname -> kind -> term -> term
  | LamAbs   : binderName -> ty -> term -> term
  | Apply    : term -> term -> term
  | Constant : constant -> term
  | Builtin  : DefaultFun -> term
  | TyInst   : term -> ty -> term
  | Error    : ty -> term
  | IWrap    : ty -> ty -> term -> term
  | Unwrap   : term -> term
  | Constr   : ty -> nat -> list term -> term
  | Case     : ty -> term -> list term -> term

with binding :=
  | TermBind : strictness -> vdecl -> term -> binding
  | TypeBind : tvdecl -> ty -> binding
  | DatatypeBind : dtdecl -> binding
.


(* AST Annotations *)
Inductive datatype_component :=
  | Constructor
  | ConstructorType
  | Destructor
  | DestructorType
  | DatatypeType
  | PatternFunctor
.

Inductive provenance a :=
  | Original          : a -> provenance a
  | LetBinding        : recursivity -> provenance a -> provenance a
  | TermBinding       : list ascii -> provenance a -> provenance a
  | TypeBinding       : list ascii -> provenance a -> provenance a
  | DatatypeComponent : datatype_component -> provenance a -> provenance a
  | MultipleSources   : list (provenance a) -> provenance a
.

Inductive inline_annot :=
  | AlwaysInline
  | MayInline
.

Inductive src_span :=
  | SrcSpan : list ascii -> nat -> nat -> nat -> nat -> src_span
.

Inductive ann :=
  | Ann : inline_annot -> list src_span -> ann
.

Inductive context :=
  | C_Hole     : context

  | C_LamAbs   : binderName -> ty -> context -> context
  | C_Apply_L    : context -> term -> context
  | C_Apply_R    : term -> context -> context
  .

(* Similar to mkLet in Plutus: for an empty list of bindings it is the identity, otherwise
   it constructs a let with a non-empty list of bindings *)
Definition mk_let (r : recursivity) (bs : list binding) (t : term) : term :=
  match bs with
    | [] => t
    | _  => Let r bs t
  end
.

Fixpoint context_fill (C : context) (t : term) :=
  match C with
    | C_Hole           => t
    | C_LamAbs bn ty C => LamAbs bn ty (context_fill C t)
    | C_Apply_L C t'   => Apply (context_fill C t) t'
    | C_Apply_R t' C   => Apply t' (context_fill C t)
  end
.

Fixpoint context_comp (C C' : context) : context :=
  match C with
    | C_Hole           => C'
    | C_LamAbs bn ty C => C_LamAbs bn ty (context_comp C C')
    | C_Apply_L C t'   => C_Apply_L (context_comp C C') t'
    | C_Apply_R t' C   => C_Apply_R t' (context_comp C C')
  end
.


  Declare Scope contexts.

  #[local]
  Notation "C ∘ C'" := (context_comp C C') (at level 60) : contexts.
  #[local]
  Notation "C @@ t  " := (context_fill C t) (at level 65, right associativity) : contexts .

  #[local]
  Open Scope contexts.

  Lemma context_comp_fill C C' t : (C ∘ C' @@ t) = (C @@ C' @@ t).
  Admitted.


(** ** Trace of compilation *)
Inductive pass :=
  | PassRename
  | PassDeadCode
  | PassThunkRec
  | PassRecSplit
  | PassLetMerge
  | PassFloatIn
  | PassFloatOut
  | PassCompileLetNonStrict
  | PassCompileLetType
  | PassCompileLetData
  | PassCompileLetRec
  | PassCompileLetNonRec

  | PassInline
  | PassUnwrapWrap
  | PassCaseReduce
  | PassCaseOfCase
  | PassBeta
  | PassKnownConstructor
  | PassStrictifyBindings
  | PassEvaluateBuiltins
  | PassRewriteRules

  | PassTypeCheck
  | PassOther : string -> pass
  .

Inductive compilation_trace :=
  | CompilationTrace : term -> list (pass * term) -> compilation_trace.


(* AST Helpers *)

Definition vdecl_name : vdecl -> binderName :=
  fun c => match c with
  | VarDecl n _ => n
  end
  .

Definition vdecl_ty : vdecl -> ty :=
  fun c => match c with
  | VarDecl _ ty => ty
  end
  .

Definition tvdecl_name (tvd : tvdecl) : binderTyname :=
  match tvd with
  | TyVarDecl v K => v
  end.

Section term__ind.

  Unset Implicit Arguments.

  Variable (P : term -> Prop).
  Variable (Q : binding -> Prop).

  Context
    (H_Let     : forall rec bs t, ForallP Q bs -> P t -> P (Let rec bs t))
    (H_Var     : forall s : string, P (Var s))
    (H_TyAbs   : forall (s : string) (k : kind) (t : term), P t -> P (TyAbs s k t))
    (H_LamAbs  : forall (s : string) (t : ty) (t0 : term), P t0 -> P (LamAbs s t t0))
    (H_Apply   : forall t : term, P t -> forall t0 : term, P t0 -> P (Apply t t0))
    (H_Constant : forall (c : constant), P (Constant c))
    (H_Builtin : forall d : DefaultFun, P (Builtin d))
    (H_TyInst  : forall t : term, P t -> forall t0 : ty, P (TyInst t t0))
    (H_Error   : forall t : ty, P (Error t))
    (H_IWrap   : forall (t t0 : ty) (t1 : term), P t1 -> P (IWrap t t0 t1))
    (H_Unwrap  : forall t : term, P t -> P (Unwrap t))
    (H_Constr  : forall T (i : nat) (ts : list term), ForallP P ts -> P (Constr T i ts))
    (H_Case   : forall T (t : term), P t -> forall ts, ForallP P ts -> P (Case T t ts))
    .



  Context
    (H_TermBind : forall s v t, P t -> Q (TermBind s v t))
    (H_TypeBind : forall v ty, Q (TypeBind v ty))
    (H_DatatypeBind : forall dtd, Q (DatatypeBind dtd)).

  Definition bindings__ind (binding__ind : forall (b : binding), Q b) :=
    fix bindings__ind bs :=
    match bs as p return ForallP Q p with
      | nil       => ForallP_nil
      | cons b bs => ForallP_cons (binding__ind b) (bindings__ind bs)
    end.

  Definition terms__ind (term_rect : forall (t : term), P t) :=
    fix terms_rect' ts :=
    match ts as p return ForallP P p with
      | nil       => ForallP_nil
      | cons t ts => ForallP_cons (term_rect t) (terms_rect' ts)
    end.

  Fixpoint term__ind (t : term) : P t :=
    match t with
      | Let rec bs t    => H_Let rec bs t (bindings__ind binding__ind bs) (term__ind t)
      | Var n           => H_Var n
      | TyAbs n k t     => H_TyAbs n k t (term__ind t)
      | LamAbs n ty t   => H_LamAbs n ty t (term__ind t)
      | Apply s t       => H_Apply s (term__ind s) t (term__ind t)
      | TyInst t ty     => H_TyInst t (term__ind t) ty
      | IWrap ty1 ty2 t => H_IWrap ty1 ty2 t (term__ind t)
      | Unwrap t        => H_Unwrap t (term__ind t)
      | Error ty        => H_Error ty
      | Constant c      => H_Constant c
      | Builtin f       => H_Builtin f
      | Constr T i ts     => H_Constr T i ts (terms__ind term__ind ts)
      | Case T t ts      => H_Case T t (term__ind t) ts (terms__ind term__ind ts)
    end
  with binding__ind (b : binding) : Q b :=
    match b with
      | TermBind s v t  => H_TermBind s v t (term__ind t)
      | TypeBind v ty   => H_TypeBind v ty
      | DatatypeBind dtd => H_DatatypeBind dtd
    end.

  Combined Scheme term__multind from term__ind, binding__ind.

End term__ind.


Section term__rect.

  Unset Implicit Arguments.

  Variable (P : term -> Type).
  Variable (Q : binding -> Type).

  Context
    (H_Let     : forall rec bs t, ForallT Q bs -> P t -> P (Let rec bs t))
    (H_Var     : forall s : string, P (Var s))
    (H_TyAbs   : forall (s : string) (k : kind) (t : term), P t -> P (TyAbs s k t))
    (H_LamAbs  : forall (s : string) (t : ty) (t0 : term), P t0 -> P (LamAbs s t t0))
    (H_Apply   : forall t : term, P t -> forall t0 : term, P t0 -> P (Apply t t0))
    (H_Constant : forall (c : constant), P (Constant c))
    (H_Builtin : forall d : DefaultFun, P (Builtin d))
    (H_TyInst  : forall t : term, P t -> forall t0 : ty, P (TyInst t t0))
    (H_Error   : forall t : ty, P (Error t))
    (H_IWrap   : forall (t t0 : ty) (t1 : term), P t1 -> P (IWrap t t0 t1))
    (H_Unwrap  : forall t : term, P t -> P (Unwrap t))
    (H_Constr  : forall T (i : nat) (ts : list term), ForallT P ts -> P (Constr T i ts))
    (H_Case   : forall T (t : term), P t -> forall ts, ForallT P ts -> P (Case T t ts))
    .



  Context
    (H_TermBind : forall s v t, P t -> Q (TermBind s v t))
    (H_TypeBind : forall v ty, Q (TypeBind v ty))
    (H_DatatypeBind : forall dtd, Q (DatatypeBind dtd)).

  Definition bindings__rect (binding__rect : forall (b : binding), Q b) :=
    fix bindings__rect bs :=
    match bs as p return ForallT Q p with
      | nil       => ForallT_nil
      | cons b bs => ForallT_cons (binding__rect b) (bindings__rect bs)
    end.

  Definition terms__rect (term_rect : forall (t : term), P t) :=
    fix terms_rect' ts :=
    match ts as p return ForallT P p with
      | nil       => ForallT_nil
      | cons t ts => ForallT_cons (term_rect t) (terms_rect' ts)
    end.

  Fixpoint term__rect (t : term) : P t :=
    match t with
      | Let rec bs t    => H_Let rec bs t (bindings__rect binding__rect bs) (term__rect t)
      | Var n           => H_Var n
      | TyAbs n k t     => H_TyAbs n k t (term__rect t)
      | LamAbs n ty t   => H_LamAbs n ty t (term__rect t)
      | Apply s t       => H_Apply s (term__rect s) t (term__rect t)
      | TyInst t ty     => H_TyInst t (term__rect t) ty
      | IWrap ty1 ty2 t => H_IWrap ty1 ty2 t (term__rect t)
      | Unwrap t        => H_Unwrap t (term__rect t)
      | Error ty        => H_Error ty
      | Constant c      => H_Constant c
      | Builtin f       => H_Builtin f
      | Constr T i ts     => H_Constr T i ts (terms__rect term__rect ts)
      | Case T t ts      => H_Case T t (term__rect t) ts (terms__rect term__rect ts)
    end
  with binding__rect (b : binding) : Q b :=
    match b with
      | TermBind s v t  => H_TermBind s v t (term__rect t)
      | TypeBind v ty   => H_TypeBind v ty
      | DatatypeBind dtd => H_DatatypeBind dtd
    end.

  Combined Scheme term__multrect from term__rect, binding__rect.

End term__rect.


Section term_rect.
  Variable (P : term -> Type).
  Variable (Q : binding -> Type).
  Variable (R : list binding -> Type).
  Variable (S : list binding -> Type).

  Context
    (* (H_Let     : forall rec bs t, ForallT Q bs -> P t -> P (Let rec bs t)) *)
    (H_LetRec    : forall bs t, R bs -> P t -> P (Let Rec bs t))
    (H_LetNonRec : forall bs t, S bs -> P t -> P (Let NonRec bs t))
    (H_Var     : forall s, P (Var s))
    (H_TyAbs   : forall s (k : kind) (t : term), P t -> P (TyAbs s k t))
    (H_LamAbs  : forall s t (t0 : term), P t0 -> P (LamAbs s t t0))
    (H_Apply   : forall t : term, P t -> forall t0 : term, P t0 -> P (Apply t t0))
    (H_Constant : forall (c : constant), P (Constant c))
    (H_Builtin : forall d : DefaultFun, P (Builtin d))
    (H_TyInst  : forall t : term, P t -> forall t0 : ty, P (TyInst t t0))
    (H_Error   : forall t : ty, P (Error t))
    (H_IWrap   : forall (t t0 : ty) (t1 : term), P t1 -> P (IWrap t t0 t1))
    (H_Unwrap  : forall t : term, P t -> P (Unwrap t))
    (H_Constr  : forall T  (i : nat) (ts : list (term)), ForallT P ts -> P (Constr T i ts))
    (H_Case   : forall T t, P t -> forall ts, ForallT P ts -> P (Case T t ts)).

  Context
    (H_TermBind    : forall s v t, P t -> Q (TermBind s v t))
    (H_TypeBind    : forall v ty, Q (TypeBind v ty))
    (H_DatatypeBind : forall dtd, Q (DatatypeBind dtd)).

  Context
    (H_consRec        : forall b bs, Q b -> R bs -> R (b :: bs))
    (H_nilRec         : R nil).

  Context
    (H_cons      : forall b bs, Q b -> S bs -> S (b :: bs))
    (H_nil       : S nil).

  Definition bindings_rect' (binding_rect' : forall (b : binding), Q b) :=
    fix bindings_rect' bs :=
    match bs return R bs with
      | nil       => @H_nilRec
      | cons b bs => @H_consRec _ bs (binding_rect' b) (bindings_rect' bs)
    end.

  Definition bindings_nonrec_rect' (binding_rect' : forall (b : binding), Q b) :=
    fix bindings_nonrect' bs :=
    match bs return S bs with
      | nil       => @H_nil
      | cons b bs => @H_cons _ bs (binding_rect' b) (bindings_nonrect' bs)
    end.

  Definition terms_rect' (term_rect : forall (t : term), P t) :=
    fix terms_rect' ts :=
    match ts as p return ForallT P p with
      | nil       => ForallT_nil
      | cons t ts => ForallT_cons (term_rect t) (terms_rect' ts)
    end.

  Fixpoint term_rect' (t : term) : P t :=
    match t with
      | Let Rec bs t    => @H_LetRec bs t (bindings_rect' binding_rect' bs) (term_rect' t)
      | Let NonRec bs t => @H_LetNonRec bs t (bindings_nonrec_rect' binding_rect' bs) (term_rect' t)
      | Var n           => @H_Var n
      | TyAbs n k t     => @H_TyAbs n k t (term_rect' t)
      | LamAbs n ty t   => @H_LamAbs n ty t (term_rect' t)
      | Apply s t       => @H_Apply s (term_rect' s) t (term_rect' t)
      | TyInst t ty     => @H_TyInst t (term_rect' t) ty
      | IWrap ty1 ty2 t => @H_IWrap ty1 ty2 t (term_rect' t)
      | Unwrap t        => @H_Unwrap t (term_rect' t)
      | Error ty        => @H_Error ty
      | Constant c      => @H_Constant c
      | Builtin f       => @H_Builtin f
      | Constr T i ts     => @H_Constr T i ts (terms_rect' term_rect' ts)
      | Case T t ts      => @H_Case T t (term_rect' t) ts (terms_rect' term_rect' ts)
    end
  with binding_rect' (b : binding) : Q b :=
    match b with
      | TermBind s v t   => @H_TermBind s v t (term_rect' t)
      | TypeBind v ty    => @H_TypeBind v ty
      | DatatypeBind dtd => @H_DatatypeBind dtd
    end.
End term_rect.

Section ty_fold.

  Context
    (R : Set) (* Result type for ty*)
    (S : Set) (* Result type for list ty (sums in SOP) *)
    (P : Set) (* Result type for list ty (products in SOP) *)
    .

  Context
    (f_Var : name -> R)
    (f_Fun : R -> R -> R)
    (f_IFix : R -> R -> R)
    (f_Forall :  binderName -> kind -> R -> R)
    (f_Builtin : DefaultUni -> R)
    (f_Lam :  binderName -> kind -> R -> R)
    (f_App : R -> R -> R)
    (f_SOP : S -> R)
    (f_SOP_sum_cons : P -> S -> S)
    (f_SOP_sum_nil : S)
    (f_SOP_prod_cons : R -> P -> P)
    (f_SOP_prod_nil : P)
    .

  Definition fold_SOP (fold : ty -> R) : list (list ty) -> S :=
      (fix fold_sum xs := match xs with
        | ts :: xs' =>
          f_SOP_sum_cons
            ((fix fold_prod ts :=
              match ts with
              | ty :: ts' => f_SOP_prod_cons (fold ty) (fold_prod ts')
              | [] => f_SOP_prod_nil
              end
            ) ts)
            (fold_sum xs')
        | [] => f_SOP_sum_nil
      end
      )
      .

  Definition ty_fold := fix fold ty :=
    match ty with
    | Ty_Var v        => f_Var v
    | Ty_Fun t1 t2    => f_Fun (fold t1) (fold t2)
    | Ty_IFix t1 t2   => f_IFix (fold t1) (fold t2)
    | Ty_Forall v k t => f_Forall v k (fold t)
    | Ty_Builtin b    => f_Builtin b
    | Ty_Lam v k t    => f_Lam v k (fold t)
    | Ty_App t1 t2    => f_App (fold t1) (fold t2)
    | Ty_SOP xs       => f_SOP (fold_SOP fold xs)
    end
.

End ty_fold.


Section Folds_Alt.

  Context (R S P : Set).
  (* Alternative formulation where the function types of the algebra are determined
     by the constructor. An algebra can then be given as a function

       forall T, ty_alg T

     See fold_alg for the corresponding algebra.
     *)
  Definition ty_alg (ty : ty) : Set := match ty with
    | Ty_Var _        => tyname -> R
    | Ty_Fun _ _      => R -> R -> R
    | Ty_IFix _ _     => R -> R -> R
    | Ty_Forall _ _ _ => binderName -> kind -> R -> R
    | Ty_Builtin _    => DefaultUni -> R
    | Ty_Lam _ _ _    => binderName -> kind -> R -> R
    | Ty_App _ _      => R -> R -> R
    | Ty_SOP _        =>   (S -> R)
                         * (P -> S -> S)
                         * S
                         * (R -> P -> P)
                         * P
    end.

  Definition fold_alg (alg : forall T, ty_alg T) : ty -> R := fix fold T :=
    match T return ty_alg T -> R with
    | Ty_Var v        => fun f => f v
    | Ty_Fun t1 t2    => fun f => f (fold t1) (fold t2)
    | Ty_IFix t1 t2   => fun f => f (fold t1) (fold t2)
    | Ty_Forall v k t => fun f => f v k (fold t)
    | Ty_Builtin b    => fun f => f b
    | Ty_Lam v k t    => fun f => f v k (fold t)
    | Ty_App t1 t2    => fun f => f (fold t1) (fold t2)
    | Ty_SOP xs       => fun '(f_SOP, f_cons_s, f_nil_s, f_cons_p, f_nil_p)
        => f_SOP (fold_SOP R S P f_cons_s f_nil_s f_cons_p f_nil_p fold xs)
    end (alg T)
  .
End Folds_Alt.

Section REL_SUBTERMS.

(* General pattern for working with relations that are closed/compatible/decomposable/...
 * with the term structure. see section COMPATIBLE for one instantiation
 *)

Context
  (R : Prop * Prop -> Prop) (* could be instantiated to ->, <-, <-> *)
  (P : term -> Prop)
  (Q : binding -> Prop)
.

Definition subterms_bs (rel_sub_b : binding -> Prop) : list binding -> Prop := fix subterms_bs bs :=
  match bs with
  | nil => True
  | b :: bs => rel_sub_b b /\ subterms_bs bs
  end
.

Definition subterms_ts  (rel_sub_t : term -> Prop) : list term -> Prop := fix subterms_ts ts :=
  match ts with
  | nil => True
  | t :: ts => rel_sub_t t /\ subterms_ts ts
  end
.

Fixpoint subterms (t : term) : Prop :=
  match t with
  | Let rec bs t  => subterms_bs subterms_b bs /\ P t
  | Var x         => True
  | TyAbs X K t   => P t
  | LamAbs x T t  => P t
  | Apply s t     => P s /\ P t
  | Constant c    => True
  | Builtin f     => True
  | TyInst t T    => P t
  | Error T       => True
  | IWrap F T t   => P t
  | Unwrap t      => P t
  | Constr T i ts => subterms_ts subterms ts
  | Case T t ts   => P t /\ subterms_ts subterms ts
  end
with subterms_b (b : binding) : Prop :=
  match b with
  | DatatypeBind dtd  => True
  | TypeBind X K      => True
  | TermBind str vd t => subterms t
  end
.

Definition rel_sub_bs  (rel_sub_b : binding -> Prop) : list binding -> Prop := fix rel_sub_bs bs :=
  match bs with
  | nil => True
  | b :: bs => rel_sub_b b /\ rel_sub_bs bs
  end
.

Definition rel_sub_ts  (rel_sub_t : term -> Prop) : list term -> Prop := fix rel_sub_ts ts :=
  match ts with
  | nil => True
  | t :: ts => rel_sub_t t /\ rel_sub_ts ts
  end
.

Fixpoint rel_sub (t : term) : Prop :=
  R
  match t with
  | Let rec bs t  => (P (Let rec bs t)  , rel_sub_bs rel_sub_b bs /\ P t)
  | Var x         => (P (Var x)         , True)
  | TyAbs X K t   => (P (TyAbs X K t)   , P t)
  | LamAbs x T t  => (P (LamAbs x T t)  , P t)
  | Apply s t     => (P (Apply s t)     , P s /\ P t)
  | Constant c    => (P (Constant c)    , True)
  | Builtin f     => (P (Builtin f)     , True)
  | TyInst t T    => (P (TyInst t T)    , P t)
  | Error T       => (P (Error T)       , True)
  | IWrap F T t   => (P (IWrap F T t)   , P t)
  | Unwrap t      => (P (Unwrap t)      , P t)
  | Constr T i ts => (P (Constr T i ts) , rel_sub_ts rel_sub ts)
  | Case T t ts   => (P (Case T t ts)   , P t /\ rel_sub_ts rel_sub ts)
  end
with rel_sub_b (b : binding) : Prop :=
  R
  match b with
  | DatatypeBind dtd  => (Q (DatatypeBind dtd)  ,True)
  | TypeBind X K      => (Q (TypeBind X K)      ,True)
  | TermBind str vd t => (Q (TermBind str vd t) ,rel_sub t)
  end
.



End REL_SUBTERMS.

Section COMPATIBLE.

(* compatibility of terms/bindings with a relation *)

Context
  (P : term -> Prop)
  (Q : binding -> Prop)
.

(* compatibility for term predicates only, e.g.
    compatible P (Apply s t) = P s /\ P t -> P (Apply s t)
*)
Definition compatible (t : term) :=
  rel_sub (fun '(whole, parts) => parts -> whole) P (fun b => True) t.

(* More general version that accepts a predicate on bindings *)
Definition compatible' (t : term) :=
  rel_sub (fun '(whole, parts) => parts -> whole) P Q t.

End COMPATIBLE.

Section DECOMPOSABLE.

  Context
    (P : term -> Prop)
    (Q : binding -> Prop)
  .

  (* e.g. decomposable P (Apply s t) = P (Apply s t) -> P s /\ P t *)
  Definition decomposable (t : term) :=
    rel_sub (fun '(whole, parts) => whole -> parts) P (fun b => True) t.

  Definition decomp (t : term) := P t -> subterms P t.
End DECOMPOSABLE.


(* A transformation algebra returns the original types for ty, sums and products *)
Definition ty_alg_transform T : Set := ty_alg ty (list (list ty)) (list ty) T.
(* Definition ty_alg_transform T : Set := ty_alg ty T. *)

Definition id_alg (T : ty) : ty_alg_transform T :=
  match T return ty_alg_transform T with
    | Ty_Var _        => Ty_Var
    | Ty_Fun _ _      => Ty_Fun
    | Ty_IFix _ _     => Ty_IFix
    | Ty_Forall _ _ _ => Ty_Forall
    | Ty_Builtin _    => Ty_Builtin
    | Ty_Lam _ _ _    => Ty_Lam
    | Ty_App _ _      => Ty_App
    | Ty_SOP _        => (Ty_SOP, cons, nil, cons, nil)
  end
.


(* Extend a partial transformation to a total tranformation (using the identity) *)
Definition to_total :
  (forall T, option (ty_alg_transform T)) ->
  (forall T, (ty_alg_transform T)) :=
fun alg_partial T =>
  match alg_partial T with
    | None => id_alg T
    | Some f => f
  end.



(* Transform a type, recursively applies the transformation before applying the
* provided partial function (or the identity) *)
Definition ty_transform (custom : forall T, option (ty_alg_transform T)) : ty -> ty :=
  fold_alg _ _ _ (to_total custom).

(* Definition ty_transform (custom : forall T, option (ty_alg_transform T)) : ty -> ty :=
  fold_alg _ (to_total custom). *)

Definition unitVal : term := Constant (ValueOf DefaultUniUnit tt).

Definition ty_unit : ty := Ty_Builtin DefaultUniUnit.

(* AST utilities *)
Fixpoint splitTy (T : ty) : list ty * ty :=
  match T with
  | Ty_Fun Targ T' => (cons Targ (fst (splitTy T')), snd (splitTy T'))
  | Tr => (nil, Tr)
  end.

Lemma splitTy__inversion Targs Tr T:
    (Targs, Tr) = splitTy T ->
    T = fold_right (fun targ acc => Ty_Fun targ acc) Tr Targs.
Proof.
  generalize dependent Targs.
  generalize dependent Tr.
  induction T; simpl; intros.
  all: try solve [inversion H; subst; auto].
  inversion H; subst. simpl. f_equal.
  simpl in IHT2.
  eapply IHT2.
  destruct (splitTy T2); auto.
Qed.

Fixpoint returnTy (T : ty) : ty :=
  match T with
  | Ty_Fun _ T' => returnTy T'
  | _           => T
  end.

Lemma splitTy__returnTy T : snd (splitTy T) = returnTy T.
Proof.
  induction T; simpl; intuition.
Qed.

(* Application spine *)
Fixpoint spine (t : term) : term * list (term + ty) :=
  match t with
  | Apply s t  => let '(f, args) := spine s in (f, inl t :: args)
  | TyInst t T => let '(f, args) := spine t in (f, inr T :: args)
  | t          => (t, [])
  end
.




Declare Scope plutus_scope.

Declare Custom Entry plutus_term.
Declare Custom Entry plutus_ty.
Declare Custom Entry plutus_kind.

Module PlutusNotations.

  Notation "<{ e }>" := e (e custom plutus_term at level 99) : plutus_scope.
  Notation "<{{ e }}>" := e (e custom plutus_ty at level 99) : plutus_scope.
  Notation "<{{{ e }}}>" := e (e custom plutus_kind at level 99) : plutus_scope.
  Notation "( x )" := x (in custom plutus_term, x at level 99) : plutus_scope.
  Notation "( x )" := x (in custom plutus_ty, x at level 99) : plutus_scope.
  Notation "( x )" := x (in custom plutus_kind, x at level 99) : plutus_scope.
  Notation "x" := x (in custom plutus_term at level 0, x constr at level 0) : plutus_scope.
  Notation "x" := x (in custom plutus_ty at level 0, x constr at level 0) : plutus_scope.
  Notation "x" := x (in custom plutus_kind at level 0, x constr at level 0) : plutus_scope.
  Notation "{ x }" := x (in custom plutus_term at level 1, x constr) : plutus_scope.
  Notation "{ x }" := x (in custom plutus_ty at level 1, x constr) : plutus_scope.
  Notation "{ x }" := x (in custom plutus_kind at level 1, x constr) : plutus_scope.


  #[global]
  Open Scope plutus_scope.

  (* Term notations *)
  Notation "'λ' x :: ty , body" := (LamAbs x ty body) (in custom plutus_term at level 51, right associativity).
  Notation "'Λ' X :: K , body" := (TyAbs X K body) (in custom plutus_term at level 51, right associativity).
  Notation "t1 ⋅ t2" := (Apply t1 t2) (in custom plutus_term at level 50, left associativity).
  Notation "t @ T" := (TyInst t T) (in custom plutus_term at level 50, left associativity).


  (* Builtin notations *)
  Notation "(+)" := (Builtin AddInteger) (in custom plutus_term).
  Notation "'ifthenelse'" := (Builtin IfThenElse).
  Notation "t1 '==' t2" := (<{ {Builtin EqualsInteger} ⋅ t1 ⋅ t2 }>)
    (in custom plutus_term at level 50, no associativity).
  Notation "t1 '+' t2" := (<{ {Builtin AddInteger} ⋅ t1 ⋅ t2 }>)
    (in custom plutus_term at level 50, left associativity).
  Notation "t1 '-' t2" := (<{ {Builtin SubtractInteger} ⋅ t1 ⋅ t2 }>)
    (in custom plutus_term at level 50, left associativity).
  Notation "t1 '*' t2" := (<{ {Builtin MultiplyInteger} ⋅ t1 ⋅ t2 }>)
    (in custom plutus_term at level 50, left associativity).

  (* / collides with substitution notation *)
  (*
  Notation "t1 '/' t2" := (<{ {Builtin DivideInteger} ⋅ t1 ⋅ t2 }>)
    (in custom plutus_term at level 50, left associativity).
      *)

  (* Constants *)
  Notation "'CInt' x" := (Constant (ValueOf DefaultUniInteger x)) (in custom plutus_term at level 49).
  Notation "'CBool' x" := (Constant (ValueOf DefaultUniBool x)) (in custom plutus_term at level 49).
  Notation "'CBS' xs" := (Constant (ValueOf DefaultUniByteString xs)) (in custom plutus_term at level 49).
  Notation "'()'" := (Constant (ValueOf DefaultUniUnit tt)) (in custom plutus_term).
  Notation "'true'" := (Constant (ValueOf DefaultUniBool true)) (in custom plutus_term).
  Notation "'false'" := (Constant (ValueOf DefaultUniBool false)) (in custom plutus_term).

  (* Built-in types *)
  Notation "'ℤ'" := (Ty_Builtin DefaultUniInteger) (in custom plutus_term).
  Notation "'bool'" := (Ty_Builtin DefaultUniBool) (in custom plutus_term).
  Notation "'unit'" := (Ty_Builtin DefaultUniUnit) (in custom plutus_term).
  Notation "X '→' Y" := (Ty_Fun X Y) (in custom plutus_term at level 49, right associativity).
  Notation "'bytestring'" := (Ty_Builtin DefaultUniByteString) (in custom plutus_term at level 51, right associativity).

  (* String notation for list byte (bytestring and string)

  Pretty-print values of type list byte (used for pir's bytestring and string
  representation) as string literals, for readability.

  The parsing function will always fail, as we won't accept string literal
  notation in the parser, which has different mechanisms in Haskell and Coq
  *)

  (* String Notation requires a monomorphised type *)
  Notation bytes := (list byte) (only parsing).

  Definition parse_bytes (x : bytes) := x.
  Definition print_bytes (x : bytes) := x.

  String Notation bytes parse_bytes print_bytes : plutus_scope.

End PlutusNotations.

Module PIRNotations.


  Declare Scope pir_scope.
  Delimit Scope pir_scope with pir.


  Module Kinds.

    Notation "★" := Kind_Base
      : pir_scope.

    Notation "K1 ⇒ K2" := (Kind_Arrow K1 K2)
    (at level 49, right associativity)
      : pir_scope.

  End Kinds.

  Module Types.

    Notation "'λ*' X K T" :=
      (Ty_Lam X K T)
      (at level 200, X at level 0, K at level 0, T at level 0, no associativity)
      : pir_scope
    .

    Notation "T1 '⋅*' T2" :=
      (Ty_App T1 T2)
      (at level 50, left associativity)
      : pir_scope
    .

    Notation "'`*' X" :=
      (Ty_Var X)
      (at level 35, X at next level )
      : pir_scope
      .

  End Types.

  Module Decls.

    Notation "x : T" :=
      (VarDecl x T)
      (at level 50, no associativity)
      : pir_scope
    .

    Notation "X :* K" :=
      (TyVarDecl X K)
      (at level 50, no associativity)
      : pir_scope
    .

  End Decls.


  Module Bindings.

    Notation "vd '!=' t" :=
      (TermBind Strict vd t)
      (at level 70, t at next level, no associativity)
      : pir_scope
      .

    Notation "vd '~=' t" :=
      (TermBind NonStrict vd t)
      (at level 70, t at next level, no associativity)
      : pir_scope
      .

    Notation "'type' tvd '=' T" :=
      (TypeBind tvd T)
      (at level 70, tvd at next level, T at next level, no associativity)
      : pir_scope
      .

    Notation "data tvd '=' T" :=
      (DatatypeBind Strict tvd T)
      (at level 70, tvd at next level, T at next level, no associativity)
      : pir_scope
      .


  End Bindings.

  Module Terms.

    Notation "'let_' bs t" :=
      (Let NonRec bs t)
      (at level 200, bs at level 0, t at level 0, no associativity)
      : pir_scope
    .

    Notation "'letrec' bs t" :=
      (Let Rec bs t)
      (at level 200, bs at level 0, t at level 0, no associativity)
      : pir_scope
    .

    Notation "'`' x" :=
      (Var x)
      (at level 35, x at next level )
      : pir_scope
      .

    Notation "'λ' x ty t" :=
      (LamAbs x ty t)
      (at level 200, x at level 0, ty at level 0, t at level 0, no associativity)
      : pir_scope
    .
    Notation "'Λ' X K t" :=
      (TyAbs X K t)
      (at level 200, X at level 0, K at level 0, t at level 0, no associativity)
      : pir_scope
      .
    Notation "t1 ⋅ t2" :=
      (Apply t1 t2)
      (at level 50, left associativity)
      : pir_scope
      .
    Notation "t @ T" :=
      (TyInst t T)
      (at level 50, left associativity)
      : pir_scope
      .

  End Terms.

  Module Builtins.

    Import Terms.

    Notation "t1 '==' t2" :=
      (Builtin EqualsInteger ⋅ t1 ⋅ t2)%pir
      (in custom plutus_term at level 50, no associativity)
      : pir_scope
    .

    Notation "(+)" :=
      (Builtin AddInteger)
      : pir_scope.

    Notation "'ifthenelse'" :=
      (Builtin IfThenElse)
      : pir_scope.

    Notation "t1 '+' t2" :=
      (Builtin AddInteger ⋅ t1 ⋅ t2 )%pir
      (at level 50, left associativity)
      : pir_scope
    .
    Notation "t1 '-' t2" :=
      (Builtin SubtractInteger ⋅ t1 ⋅ t2)%pir
      (at level 50, left associativity)
      : pir_scope
    .

    Notation "t1 '*' t2" :=
      (Builtin MultiplyInteger ⋅ t1 ⋅ t2)%pir
      (at level 40, left associativity)
      : pir_scope
      .

  End Builtins.

  Export Kinds Types Decls Bindings Terms Builtins.

  Module Examples.

    Open Scope string_scope.
    Open Scope pir_scope.


    Definition tvd : tvdecl := "x" :* ★.

    Definition s :=
      (λ "x" ty_unit (`"x" + `"x")).

    Definition u :=
      (Λ "x" Kind_Base (`"x" + `"x")) @ ty_unit.

    Definition t :=
      let_
        [ type ("X" :* ★) = ty_unit;
          ("y" : ty_unit) != `"x"
        ]
        s.
  End Examples.

End PIRNotations.
