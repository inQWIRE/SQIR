Require Import List.
Require Import String.
Require Import Map.

Notation Id := string. (* Identifier x *)
Definition Id_eq : forall x y : Id, {x=y} + {x<>y} := string_dec.
Infix "==id" := Id_eq (no associativity, at level 50).

Notation Idx := nat. (* Index i *)

Inductive E : Set := (* Expression *)
| e_bit (x:Id)
| e_reg (x:Id) (I:Idx).

(* purely unitary *)
Inductive U : Set := (* Unitary Stmt *)
| u_cx (E1 E2:E)
| u_h (E:E)
| u_t (E:E)
| u_tdg (E:E)
| u_app (Eg:E) (_:list E) (* Eg is unitary gate or named circuit *)
| u_seq (U1 U2:U).

(* potentially effectful/non-unitary *)
Inductive C : Set := (* Command *)
| c_creg (x:Id) (I:Idx)
| c_qreg (x:Id) (I:Idx)
| c_gate (x:Id) (_:list Id) (U:U) (* declare unitary circuits *)
| c_measure (E1 E2:E)
| c_reset (E:E)
| c_U (U:U)
| c_if (E:E) (I:Idx) (U:U) (* only tests a classical bit *)
| c_seq (C1 C2:C).

Notation L := nat. (* Location l *)

Inductive V : Set := (* Value *)
| v_reg (_:list L)
| v_lam (_:list Id) (U:U). (* unitary circuits *)

Inductive S : Set :=
| s_E (E:E)
| s_U (U:U)
| s_C (C:C).

Definition env := fmap Id Idx. (* sigma *)

(* Classical bits *)
Parameter c0 : Type.
Parameter c1 : Type.

Definition heap := fmap L (c0+c1). (* eta *)

Definition QState := 
