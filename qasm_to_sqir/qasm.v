Require Import List.
Require Import String.

(* From Adam Chlipala's FRAP book *)
Require Import Map.
Require Import Sets.

(* Classical bits *)
Inductive Cbit : Set :=
| c0 : Cbit
| c1 : Cbit.

(* Qubit abstract type *)
Parameter Qbit : Type.

Notation Id := string. (* Identifier x *)
Notation Idx := nat. (* Index i *)

(* Expressions *)
Inductive E : Set := (* Expression *)
| e_bit (x:Id)
| e_reg (x:Id) (I:Idx).

(* purely unitary effects *)
Inductive U : Set := (* Unitary Stmt *)
| u_cx (E1 E2:E)
| u_h (E:E)
| u_t (E:E)
| u_tdg (E:E)
| u_app (Eg:E) (_:list E) (* Eg is unitary gate or named circuit *)
| u_seq (U1 U2:U).

(* also includes non-unitary effects *)
Inductive Cmd : Set := (* Command *)
| c_creg (x:Id) (I:Idx)
| c_qreg (x:Id) (I:Idx)
| c_gate (x:Id) (_:list Id) (U:U) (* declare unitary circuits *)
| c_measure (E1 E2:E)
| c_reset (E:E)
| c_U (U:U)
| c_if (E:E) (I:Cbit) (U:U) (* only tests a classical bit *)
| c_seq (C1 C2:Cmd).

Notation L := nat. (* Location l *)

Inductive V : Set := (* Value *)
| v_loc (l:L)
| v_arr (ls:list L)
| v_circ (xs:list Id) (U:U). (* unitary circuits *)

Definition Env := fmap Id V. (* sigma *)
Definition Heap := fmap L Cbit. (* eta *)
Definition QState := fmap L Qbit. (* \ket psi *)

(* Built-in gates, TODO: fix dummy definitions *)
Definition H (l:L) (qs:QState) : QState := qs.
Definition T (l:L) (qs:QState) : QState := qs.
Definition Tdg (l:L) (qs:QState) : QState := qs.
Definition CNOT (l1 l2:L) (qs:QState) : QState := qs.

(* Projector TODO: fix dummy definition *)
Definition Proj (c:Cbit) (l:L) (qs:QState) : QState := qs.


(**** Big-step operational semantics ****)

(* Expressions *)
Inductive Eeval : E * Env * Heap * QState -> option V -> Prop :=
| EvalVar : forall x env heap st,
    x \in dom env
    -> Eeval (e_bit x, env, heap, st) (env $? x)
| EvalReg : forall x I env heap st ls,
    Eeval (e_bit x, env, heap, st) (Some (v_arr ls))
    -> I <= (List.length ls)
    -> Eeval (e_reg x I, env, heap, st) (Some (v_loc (nth I ls 0))).

(* Unitary statements *)
Inductive Ueval : U * Env * Heap * QState -> QState -> Prop :=
| EvalH : forall E env heap st l,
    Eeval (E, env, heap, st) (Some (v_loc l))
    -> Ueval (u_h E, env, heap, st) (H l st)
| EvalT : forall E env heap st l,
    Eeval (E, env, heap, st) (Some (v_loc l))
    -> Ueval (u_t E, env, heap, st) (T l st)
| EvalTdg : forall E env heap st l,
    Eeval (E, env, heap, st) (Some (v_loc l))
    -> Ueval (u_tdg E, env, heap, st) (Tdg l st)
| EvalCnot : forall E1 E2 env heap st l1 l2,
    Eeval (E1, env, heap, st) (Some (v_loc l1))
    -> Eeval (E2, env, heap, st) (Some (v_loc l2))
    -> Ueval (u_cx E1 E2, env, heap, st) (CNOT l1 l2 st)
| EvalApp : forall E env heap st xs U Es st',
    Eeval (E, env, heap, st) (Some (v_circ xs U))
    -> Ueval (U, env, heap, st) st' (* TODO need to do subst es/xs,
                                        WAIT, do I need to even do that? *)
    -> Ueval (u_app E Es, env, heap, st) st'
| EvalUSeq : forall U1 U2 env heap st st' st'',
    Ueval (U1, env, heap, st) st'
    -> Ueval (U2, env, heap, st') st''
    -> Ueval (u_seq U1 U2, env, heap, st) st''.

(* Commands *)
Inductive Ceval : Cmd * Env * Heap * QState -> Env * Heap * QState -> Prop :=
| EvalCreg : forall x I ls env heap st,
    (* TODO check freshness for ls *)
  Ceval (c_creg x I, env, heap, st) (env $+ (x, v_arr ls), heap, st)
| EvalQreg : forall x I ls env heap st,
    (* TODO check freshness for ls *)
    Ceval (c_qreg x I, env, heap, st) (env $+ (x, v_arr ls), heap, st)
| EvalGate : forall x xs U env heap st,
  Ceval (c_gate x xs U, env, heap, st) (env $+ (x, v_circ xs U), heap, st)
| EvalMeas0 : forall E1 E2 env heap st l1 l2,
    Eeval (E1, env, heap, st) (Some (v_loc l1))
    -> Eeval (E2, env, heap, st) (Some (v_loc l2))
    -> Ceval (c_measure E1 E2, env, heap, st)
             (env, (heap $+ (l2, c0)), Proj c0 l1 st)
| EvalMeas1 : forall E1 E2 env heap st l1 l2,
    Eeval (E1, env, heap, st) (Some (v_loc l1))
    -> Eeval (E2, env, heap, st) (Some (v_loc l2))
    -> Ceval (c_measure E1 E2, env, heap, st)
             (env, (heap $+ (l2, c1)), Proj c1 l1 st)
| EvalReset : forall E env heap st l,
  Ceval (c_reset E, env, heap, st) (env, heap, Proj c0 l st)
| EvalIfFalse : forall E I U env heap st l,
    Eeval (E, env, heap, st) (Some (v_loc l))
    -> heap $? l <> Some I
    -> Ceval (c_if E I U, env, heap, st) (env, heap, st)
| EvalIfTrue : forall E I U env heap st st' l,
    Eeval (E, env, heap, st) (Some (v_loc l))
    -> heap $? l = Some I
    -> Ueval (U, env, heap, st) st'
    -> Ceval (c_if E I U, env, heap, st) (env, heap, st')
| EvalCSeq : forall C1 C2 e e' e'' h h' h'' st st' st'',
    Ceval (C1, e, h, st) (e', h', st')
    -> Ceval (C2, e', h', st') (e'', h'', st'')
    -> Ceval (c_seq C1 C2, e, h, st) (e'', h'', st'').
