Require Coq.extraction.Extraction.

Module Type AType.
  Parameter a : nat.
  Parameter b : nat.
End AType.

Module Type ATypeFacts (A : AType).
  Axiom a_fact : A.a > 2.
End ATypeFacts.

Module BMod (A : AType).
  Definition foo : nat := 4 + A.a.
  Definition bar : bool := false.
End BMod.

Module BModFacts (A : AType) (AF : ATypeFacts A) (Import B : BMod A).


  Lemma blah : foo > 6.
  Proof. Admitted. 
End BModFacts.

Module AMod <: AType.
  Definition a := 3.
  Definition b := 5.
End AMod.

Module AModFacts <: ATypeFacts AMod.
  Lemma a_fact : AMod.a > 2.
  Proof. Admitted.
End AModFacts.

Module B := BMod AMod.
Module BF := BModFacts AMod AModFacts.
Recursive Extraction B.bar.
Print B.foo.
Print BF.B.foo.

Problem: define things using B.foo, but want to use facts from BF

opts defnd over ULR RzQ

facts talk about (URLF RzQ RzQF).(ULR RzQ)
