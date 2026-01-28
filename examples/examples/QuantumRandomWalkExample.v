Require Import String.
From SQIR Require Export SQIR.
From SQIR Require Import RC_Syntax RC_Semantics RC_Logic.

Local Open Scope com_scope.
Local Open Scope string_scope.

Section QRW.
  Variable dim : nat.
  Variable Step : base_ucom dim.
  Variable m : nat.

  Definition walk_body : RC_Syntax.base_com dim :=
    CWhile m (CUnitary Step).

  Definition proc_body (p : string) : RC_Syntax.base_com dim :=
    if String.eqb p "QRW" then walk_body else CAbort.

  Definition QRW : RC_Syntax.base_com dim := CCall "QRW".

  Variable InitState : assert.
  Variable TargetReached : assert.

  Definition QRW_pre (Q : assert) : assert :=
    (@wp dim proc_body) QRW Q.

  Definition QRW_reach : assert :=
    IConj (fun i => (@wp_fuel dim proc_body) (S i) QRW TargetReached).

  Definition QRW_spec : Prop :=
    is_valid_triple proc_body InitState QRW TargetReached.
End QRW.
