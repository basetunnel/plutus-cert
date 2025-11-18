From PlutusCert Require Import
  Cert.Relation.Types
  Transform.DeadCode.Spec
  DeadCode.DecideBool
.


Definition rd_deadcode : rel_decidable :=
  mk_rel_decidable
    elim
    dec_Term'
    dec_Term'_equiv
.
