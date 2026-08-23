From PlutusCert Require Import
  PlutusIR
  Util
  Builtins.Signatures
.
Import PlutusNotations.

Import ZArith.BinInt.
Import Coq.Lists.List.
Import Coq.Strings.String.
Import Coq.Bool.Bool.
Import Coq.Strings.Byte.
Import Ascii.
Require Import Coq.Strings.BinaryString.
From Equations Require Import Equations.
Import ListNotations.

Local Open Scope Z_scope.


Section Eta.
  (*
  Expands e.g.
    +
  to
    λ x y. x + y

  *)

  Definition mk_var : nat -> string :=
    string_of_nat
  .

  From PlutusCert Require Import FreeVars.

  Definition fresh_var (t : term) : string :=
    concat "" (Term.fv t).

  Definition fresh_tyvar (t : term) : string :=
    concat "" (Term.ftv t).

  Fixpoint apps ( b : term) (args : list (term + ty)) : term :=
    match args with
      | [] => b
      | inl t :: xs => <{ {apps <{b ⋅ t}> xs} }>
      | inr T :: xs => <{ {apps <{b @ T}> xs} }>
    end
  .

  Fixpoint eta_expand_sig (s : builtin_sig) (f : DefaultFun) (args : list (term + ty)) (n : nat) : term :=
    match s with
    | BS_Fun T s      => <{ λ {mk_var n} :: T, {eta_expand_sig s f (args ++ [inl (Var (mk_var n))]) (S n)} }>
    | BS_Forall X K s => <{ Λ {mk_var n} :: K, {eta_expand_sig s f (args ++ [inr (Ty_Var X)]) (S n)} }>
    | BS_Result T     => apps (Builtin f) args
    end
  .

  Definition eta_expand (f : DefaultFun) := eta_expand_sig (to_sig f) f [] 0.

  Compute eta_expand IfThenElse.

End Eta.


Section ByteString.

  Local Open Scope Z_scope.

  Definition Z_to_byte (z : Z) : option byte :=
    if (0 <=? z) && (z <=? 255) then Byte.of_nat (Z.to_nat z) else None.


  Definition Z_to_nat (z : Z) : option nat :=
    if (0 <=? z) then Some (Z.to_nat z) else None
  .

  (*
  Returns an Error term if the integer is out of range (Semantic variant 2)
  *)
  Definition cons_bytestring (z : Z) (bs : list byte) : term :=
      match Z_to_byte z with
      | Some b => Constant (ValueOf DefaultUniByteString (b :: bs))
      | None   => Error (Ty_Builtin DefaultUniByteString)
      end
  .

  Local Open Scope list_scope.
  Definition slice_list {A} (s k : Z) (bs : list A) : list A :=
    let i := Z.max s 0 in
    let j := Z.min (s + k - 1) (Z.of_nat (List.length bs) - 1) in
    if j <? i
      then []
      else
        let len := (Z.to_nat j - Z.to_nat i + 1)%nat in
        firstn len (skipn (Z.to_nat i) bs)
  .

  Definition index_bytestring (bs : list byte) (c : Z) : term :=
    match Z_to_nat c with
      | Some n => match nth_error bs n with
        | Some b => <{ CInt {Z.of_nat (Byte.to_nat b)} }>
        | None => Error <{ ℤ }>
        end
      | None => Error <{ ℤ }>
      end
    .

  Axiom verify_Ed25519_signature : list byte -> list byte -> list byte -> bool.
  Axiom sha2_256 : list byte -> list byte.
  Axiom sha3_256 : list byte -> list byte.

End ByteString.


(*
Computes results of fully applied builtin functions where possible. Returns an error if either
- unexpected arguments supplied
- function not formalized
- the semantics of the function fails

*)
Definition eval_builtin (t : term) : term :=
  match t with
  (* Integer operations *)
  | <{ CInt n + CInt m }>  => <{ CInt {n + m} }>
  | <{ CInt n * CInt m }>  => <{ CInt {n * m} }>
  | <{ CInt n - CInt m }>  => <{ CInt {n - m} }>
  | <{ {Builtin DivideInteger} ⋅ CInt n ⋅ CInt m }> => <{ CInt {n / m} }>
  | <{ {Builtin QuotientInteger} ⋅ CInt n ⋅ CInt m }> => <{ CInt {n ÷ m} }>
  | <{ {Builtin RemainderInteger} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin ModInteger} }> => Error <{ unit }> (* TODO *)

  | <{ CInt n == CInt m }> => <{ CBool {n =? m} }>
  | <{ {Builtin LessThanInteger} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin LessThanEqualsInteger} }> => Error <{ unit }> (* TODO *)

  (* ByteString operations *)
  | <{ {Builtin AppendByteString } ⋅ CBS xs ⋅ CBS ys}> => <{ CBS {xs ++ ys} }>
  | <{ {Builtin ConsByteString } ⋅ CInt n ⋅ CBS xs}> => (cons_bytestring n xs)
  | <{ {Builtin SliceByteString } ⋅ CInt n ⋅ CInt m ⋅ CBS xs}> => <{ CBS {slice_list n m xs} }>
  | <{ {Builtin LengthOfByteString } ⋅ CBS xs}> => <{ CInt {Z.of_nat (List.length xs)} }>
  | <{ {Builtin IndexByteString } ⋅ CBS xs ⋅ CInt n}> => (index_bytestring xs n)
  | <{ {Builtin EqualsByteString} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin LessThanByteString} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin LessThanEqualsByteString} }> => Error <{ unit }> (* TODO *)

  | <{ ifthenelse @ T ⋅ CBool b ⋅ s ⋅ t }> => (if b then s else t)

  (* Cryptography primitives *)
  | <{ {Builtin Sha2_256} ⋅ CBS bs }> => <{CBS {sha2_256 bs} }>
  | <{ {Builtin Sha3_256} ⋅ CBS bs }> => <{CBS {sha3_256 bs} }>
  | <{ {Builtin Blake2b_256} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin VerifyEd25519Signature} ⋅ CBS xs ⋅ CBS ys ⋅ CBS zs}> => <{ CBool {verify_Ed25519_signature xs ys zs} }>
  | <{ {Builtin VerifyEcdsaSecp256k1Signature} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin VerifySchnorrSecp256k1Signature} }> => Error <{ unit }> (* TODO *)

  (* Strings *)
  | <{ {Builtin AppendString} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin EqualsString} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin EncodeUtf8} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin DecodeUtf8} }> => Error <{ unit }> (* TODO *)

  (* <{ unit }> *)
  | <{ {Builtin ChooseUnit} }> => Error <{ unit }> (* TODO *)
  (* Tracing *)
  | <{ {Builtin Trace} }> => Error <{ unit }> (* TODO *)
  (* Pairs *)
  | <{ {Builtin FstPair} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin SndPair} }> => Error <{ unit }> (* TODO *)
  (* Lists *)
  | <{ {Builtin ChooseList} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin MkCons} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin HeadList} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin TailList} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin NullList} }> => Error <{ unit }> (* TODO *)
  (* Data *)
  | <{ {Builtin ChooseData} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin ConstrData} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin MapData} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin ListData} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin IData} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin BData} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin UnConstrData} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin UnMapData} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin UnListData} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin UnIData} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin UnBData} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin EqualsData} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin SerialiseData} }> => Error <{ unit }> (* TODO *)
  (* Misc monomorphized constructors. *)
  | <{ {Builtin MkPairData} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin MkNilData} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin MkNilPairData} }> => Error <{ unit }> (* TODO *)
  (* BLS12_381 operations *)
  (* G1 *)
  | <{ {Builtin Bls12_381_G1_add} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin Bls12_381_G1_neg} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin Bls12_381_G1_scalarMul} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin Bls12_381_G1_equal} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin Bls12_381_G1_hashToGroup} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin Bls12_381_G1_compress} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin Bls12_381_G1_uncompress} }> => Error <{ unit }> (* TODO *)
  (* G2 *)
  | <{ {Builtin Bls12_381_G2_add} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin Bls12_381_G2_neg} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin Bls12_381_G2_scalarMul} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin Bls12_381_G2_equal} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin Bls12_381_G2_hashToGroup} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin Bls12_381_G2_compress} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin Bls12_381_G2_uncompress} }> => Error <{ unit }> (* TODO *)
  (* Pairing *)
  | <{ {Builtin Bls12_381_millerLoop} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin Bls12_381_mulMlResult} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin Bls12_381_finalVerify} }> => Error <{ unit }> (* TODO *)
  (* Keccak_256, Blake2b_224 *)
  | <{ {Builtin Keccak_256} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin Blake2b_224} }> => Error <{ unit }> (* TODO *)
  (* Conversions *)
  | <{ {Builtin IntegerToByteString} }> => Error <{ unit }> (* TODO *)
  | <{ {Builtin ByteStringToInteger} }> => Error <{ unit }> (* TODO *)

  | _ => Error <{ unit }> (* Unexpected term *)
  end
.
