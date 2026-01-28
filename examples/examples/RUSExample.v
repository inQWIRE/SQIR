Require Import String.
From SQIR Require Export SQIR.
From SQIR Require Import RC_Syntax RC_Semantics RC_Logic.

Local Open Scope com_scope.
Local Open Scope string_scope.

Section RUS.
  Variable dim : nat.
  Variable q a : nat.
  Variable U V : base_ucom dim.

  Definition RUS_Gate_body : RC_Syntax.base_com dim :=
    CUnitary U ;;
    CMeasure a (CUnitary V ;; CCall "RUS_Gate") CSkip.

  Definition proc_body (p : string) : RC_Syntax.base_com dim :=
    if String.eqb p "RUS_Gate" then RUS_Gate_body else CAbort.

  Definition RUS_Gate : RC_Syntax.base_com dim := CCall "RUS_Gate".

  Definition RUS_eval : Denot dim :=
    eval_recursive proc_body RUS_Gate.

  Definition RUS_unroll (k : nat) : RC_Syntax.base_com dim :=
    approx_unroll proc_body k "RUS_Gate".

  Definition RUS_pre (Q : assert) : assert :=
    (@wp dim proc_body) RUS_Gate Q.

  Definition ancilla0 : assert := AMeas a false.

  Definition RUS_pre_with_ancilla (Q : assert) : assert :=
    AAnd ancilla0 (RUS_pre Q).
End RUS.
