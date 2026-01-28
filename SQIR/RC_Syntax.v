Require Import String.
From SQIR Require Export SQIR.
Require Import QuantumLib.Matrix.

Local Open Scope com_scope.

(**********************)
(** Commands (com)   **)
(**********************)

Inductive com (U : nat -> Set) (dim : nat) : Set :=
| CSkip : com U dim
| CAbort : com U dim
| CSeq : com U dim -> com U dim -> com U dim
| CIf : nat -> com U dim -> com U dim -> com U dim
| CWhile : nat -> com U dim -> com U dim
| CUnitary : ucom U dim -> com U dim
| CMeasure : nat -> com U dim -> com U dim -> com U dim
| CCall : string -> com U dim.

Arguments CSkip {U dim}.
Arguments CAbort {U dim}.
Arguments CSeq {U dim}.
Arguments CIf {U dim}.
Arguments CWhile {U dim}.
Arguments CUnitary {U dim}.
Arguments CMeasure {U dim}.
Arguments CCall {U dim}.

Notation "c1 ;; c2" := (CSeq c1 c2) (at level 50) : com_scope.
Notation "'cif' n 'then' c1 'else' c2" := (CIf n c1 c2) (at level 40) : com_scope.
Notation "'cwhile' n 'do' c" := (CWhile n c) (at level 40) : com_scope.

Definition base_com := com base_Unitary.

(************************)
(** Assertions (assert) **)
(************************)

Inductive assert : Type :=
| ATrue : assert
| AFalse : assert
| AMeas : nat -> bool -> assert
| AQState : forall dim, Matrix (2^dim) (2^dim) -> assert
| AAnd : assert -> assert -> assert
| AOr : assert -> assert -> assert
| ANot : assert -> assert
| AImp : assert -> assert -> assert
| AUnitary : forall {U dim}, ucom U dim -> assert -> assert
| IConj : (nat -> assert) -> assert.
