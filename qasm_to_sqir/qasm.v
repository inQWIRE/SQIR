Require Import Arith.
Require Import Bool.
Require Import List.

Definition Id := nat. (* Identifier x *)
Definition Idx := nat. (* Index i *)

Inductive E : Set := (* Expression *)
| e_bit (x:Id)
| e_reg (x:Id) (I:Idx).

(* purely unitary *)
Inductive U : Set := (* Unitary Stmt *)
| u_cx (E1:E) (E2:E)
| u_h (E:E)
| u_t (E:E)
| u_tdg (E:E)
| u_app (Eg:E) (_:list E) (* Eg is unitary gate or named circuit *)
| u_seq (U1:U) (U2:U).

(* potentially effectful/non-unitary *)
Inductive C : Set := (* Command *)
| c_creg (x:Id) (I:Idx)
| c_qreg (x:Id) (I:Idx)
| c_gate (x:Id) (_:list Id) (U:U) (* declare unitary circuits *)
| c_measure (E1:E) (E2:E)
| c_reset (E:E)
| c_U (U:U)
| c_if (E:E) (I:Idx) (U:U) (* only tests a classical bit *)
| c_seq (C1:C) (C2:C).

Definition L := nat. (* Location l *)

Inductive V : Set := (* Value *)
| v_reg (_:list L)
| v_lam (_:list Id) (U:U). (* unitary circuits *)

