Require Import List.
Require Import String.

Require Import Map.
Require Import Sets.

Set Implicit Arguments.

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
| v_loc (_:L)
| v_arr (_:list L)
| v_circ (_:list Id) (U:U). (* unitary circuits *)

Inductive S : Set :=
| s_E (E:E)
| s_U (U:U)
| s_C (C:C).

Definition Env := fmap Id V. (* sigma *)

(* Classical bits *)
Parameter c0 : Type.
Parameter c1 : Type.

Definition Heap := fmap L (c0+c1). (* eta *)

(* Qubit abstract type *)
Parameter Qbit : Type.

Definition QState := fmap L Qbit.

(* Built-in gates *)
Definition H (l:list L) (qs:QState) : QState := qs.
Definition T (l:list L) (qs:QState) : QState := qs.
Definition Tdg (l:list L) (qs:QState) : QState := qs.
Definition CNOT (l1 l2:list L) (qs:QState) : QState := qs.

(* Big-step operational semantics *)

(* Expressions *)
Inductive Eeval : E * Env * Heap * QState -> option V -> Prop :=
| EvalVar : forall x env heap st,
    x \in dom env
    -> Eeval (e_bit x, env, heap, st) (env $? x)
| EvalReg : forall x I env heap st ls,
    Eeval (e_bit x, env, heap, st) (Some (v_arr ls))
    -> I <= (List.length ls)
    -> Eeval (e_reg x I, env, heap, st) (Some (v_loc (nth I ls 0) )).

(* Unitary statements *)
Inductive Ueval : U * Env * Heap * QState -> QState -> Prop :=
| EvalH : forall E env heap st l,
    Eeval (E, env, heap, st) (Some l)
    -> Ueval (u_h E, env, heap, st) (H l st)
| EvalT : forall E env heap st l,
    Eeval (E, env, heap, st) (Some l)
    -> Ueval (u_t E, env, heap, st) (T l st)
| EvalTdg : forall E env heap st l,
    Eeval (E, env, heap, st) (Some l)
    -> Ueval (u_tdg E, env, heap, st) (Tdg l st)
| EvalCnot : forall E1 E2 env heap st l1 l2,
    Eeval (E1, env, heap, st) (Some l1)
    -> Eeval (E2, env, heap, st) (Some l2)
    -> Ueval (u_cx E1 E2, env, heap, st) (CNOT l1 l2 st).
