From PlutusCert Require Export
  PlutusIR.Transform.Compose
  PlutusIR.Transform.Rename
  PlutusIR.Transform.DeadCode.Spec
  PlutusIR.Transform.Inline
  PlutusIR.Transform.Equal
  PlutusIR.Transform.ThunkRecursions
  PlutusIR.Transform.FloatLet
  PlutusIR.Transform.LetNonRec.Spec
  PlutusIR.Transform.LetNonStrict
  PlutusIR.Transform.LetRec
  PlutusIR.Transform.LetTypes
  PlutusIR.Transform.Compat
.

(*
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.



Definition simplifier : list (Term -> Term -> Type) :=
  [ DBE_Term
  ; Inline []
  ].


(* The sequence of transformations from PIR to Plutus Core*)
Definition pirToCore: list (Term -> Term -> Type) :=
  [ rename [] []
  ; eqT (* typechecking *)
  ]

  ++ simplifier ++

  [ ThunkRecursions
  ; FloatLet
  ; LetNonStrict
  ; LetTypes
  ; LetTermsRec
  ]

  ++ simplifier ++

  [ CNR_Term
  ; eqT (* "lowers" term, changes AST type *)
  ]
.

(*
pir_0_6
     : compose
         [eq;
          eq;
          DBE_Term;

          compose [Inline []; DBE_Term];

          eq;
          compose [LetMerge; LetReorder];
          eq;
          Scott;
          eq;

          DBE_Term;

          eq;
          CNR_Term]

          pir_2_typechecked
          plc_5_compileNonRecTerms
*)
*)
