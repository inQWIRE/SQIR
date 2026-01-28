Require Import String.
From SQIR Require Export SQIR.
From SQIR Require Import RC_Syntax RC_Semantics RC_Logic.

Local Open Scope com_scope.
Local Open Scope string_scope.

Section QFT.
  Variable dim : nat.
  Variable CR : nat -> base_ucom dim.

  Fixpoint qft_name (n : nat) : string :=
    match n with
    | 0 => "QFT_0"
    | S n' => "QFT_S" ++ qft_name n'
    end.

  Fixpoint QFT_body (n : nat) : RC_Syntax.base_com dim :=
    match n with
    | 0 => CSkip
    | S n' =>
        CUnitary (H 0) ;;
        CUnitary (CR n) ;;
        QFT_body n'
    end.

  Parameter decode_qft : string -> option nat.
  Axiom decode_qft_sound : forall n, decode_qft (qft_name n) = Some n.

  Definition proc_body (p : string) : RC_Syntax.base_com dim :=
    match decode_qft p with
    | Some n => QFT_body n
    | None => CAbort
    end.

  Definition QFT (n : nat) : RC_Syntax.base_com dim :=
    CCall (qft_name n).

  Variable InputBasis : assert.
  Variable FourierBasis : assert.

  Definition QFT_spec (n : nat) : Prop :=
    is_valid_triple proc_body InputBasis (QFT n) FourierBasis.
End QFT.
