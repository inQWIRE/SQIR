Require Import List.
Require Import String.

(* From Adam Chlipala's FRAP book *)
Require Import Map.
Require Import Sets.

(* From QWIRE *)
Require Import QWIRE.Quantum.
Close Scope R_scope. (* Interferes with nat here *)

(* Classical bits *)
Inductive Cbit : Set :=
| c0 : Cbit
| c1 : Cbit.

(* Qubit abstract type *)
Definition Qbit := Vector 2.

Notation Id := string. (* Identifier x *)
Notation Idx := nat. (* Index i *)

(* Expressions *)
Inductive Exp : Set := (* Expression *)
| e_bit (x:Id)
| e_reg (x:Id) (I:Idx).

(* purely unitary effects *)
Inductive Uni : Set := (* Unitary Stmt *)
| u_cx (E1 E2:Exp)
| u_h (E:Exp)
| u_app (Eg:Exp) (_:list Exp) (* Eg is unitary gate or named circuit *)
| u_seq (U1 U2:Uni).

(* also includes non-unitary effects *)
Inductive Cmd : Set := (* Command *)
| c_creg (x:Id) (I:Idx)
| c_qreg (x:Id) (I:Idx)
| c_gate (x:Id) (_:list Id) (U:Uni) (* declare unitary circuits *)
| c_measure (E1 E2:Exp)
| c_reset (E:Exp)
| c_U (U:Uni)
| c_if (E:Exp) (I:Cbit) (U:Uni) (* only tests a classical bit *)
| c_seq (C1 C2:Cmd).

Notation L := nat. (* Location l *)

Inductive V : Set := (* Value *)
| v_loc (l:L)
| v_arr (ls:list L)
| v_circ (xs:list Id) (U:Uni). (* unitary circuits TODO switch to HOAS *)

Definition Env := fmap Id V. (* sigma σ *)
Definition Heap := fmap L Cbit. (* eta η *)
Definition QState := list Qbit. (* \ket psi ∣ψ⟩*)

(* Built-in gates, TODO add more *)
Notation H := hadamard.
Notation CNOT := cnot.

Definition Proj (c:Cbit) :=
  match c with
  | c0 => super ∣0⟩⟨0∣
  | c1 => super ∣1⟩⟨1∣
  end.

(**** Denotational semantics ****)

(* 1. Syntactic Domains, S:
   - Expression, Exp
   - Unitary Statement, Uni
   - Command, Cmd

   2. Semantic Domains
      (Value, Environment, (Classical) Heap, (Quantum) State and Configuration)
      Domain Equations:
      2.1 Value = Location + Array + Circuit
      2.2 Environment = Id → Value
      2.3 Heap = Location → Cbit
      2.4 State = Location → Qbit
      2.5 Configuration = S × σ × η × ∣ψ⟩

   3. Semantic Functions:
      3.1 Expressions,  [[E]] : Exp × σ → option V
      3.2 Unitary Stmt, [[U]] : Uni × σ × η × ∣ψ⟩ → ∣ψ'⟩
      3.2 Commands,   [[Cmd]] : Cmd × σ × η × ∣ψ⟩ → σ' × η' × ∣ψ'⟩

   4. Semantic Clauses:
*)

(* Probably don't need this  *)
Definition qbitDenote (c:Cbit) :=
  match c with
  | c0 => qubit0
  | c1 => qubit1
  end.

Fixpoint expDenote (e:Exp) (σ:Env) {struct e} :=
  match e with
  | e_bit x => σ $? x
  | e_reg x I => match σ $? x with
                 | Some (v_arr ls) => if I <=? (Datatypes.length ls)
                                      then Some (v_loc (nth I ls 0))
                                      else None
                 | _ => None
                 end
  end.

(**** Big-step operational semantics ****)

(* Expressions *)
Inductive Eeval : Exp * Env * Heap * QState -> option V -> Prop :=
| EvalVar : forall x env heap st,
    x \in dom env
    -> Eeval (e_bit x, env, heap, st) (env $? x)
| EvalReg : forall x I env heap st ls,
    Eeval (e_bit x, env, heap, st) (Some (v_arr ls))
    -> I <= (List.length ls)
    -> Eeval (e_reg x I, env, heap, st) (Some (v_loc (nth I ls 0))).

(* Unitary statements *)
Inductive Ueval : Uni * Env * Heap * QState -> QState -> Prop :=
| EvalH : forall E env heap st l,
    Eeval (E, env, heap, st) (Some (v_loc l))
    -> Ueval (u_h E, env, heap, st) (H l st)
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
