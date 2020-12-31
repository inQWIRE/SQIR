Require Import VectorStates UnitaryOps Coq.btauto.Btauto.

(**********************)
(** Unitary Programs **)
(**********************)

Local Open Scope nat_scope.

Definition var := nat.

(* all bound has the form nat * var + nat format. 
   single var is 1 * var + 0, a constant is 0 * var + nat. *)
Inductive bound : Set := 
   | Br : nat -> var -> nat -> bound.


(* Define predicate for applying gates on different circuit. *)
Inductive pred : Set :=
   | Unit : bound -> pred (* = m * var + m for exactly one *)
   | Lt : bound -> pred (* < m * var + m *)
   | Space : nat -> nat -> pred (* =  m * x + m for every one that sat the formula. *)
   | Rel : var -> bound -> pred (* x := m * y + m *)
   | Fun : (nat -> bool) -> pred (* f x *)
   | Conj : pred -> pred -> pred. (* pred /\ pred *)

Definition bound_wf (s : list var) (b:bound) : Prop :=
  match b with Br n y m => In y s end.

Fixpoint pred_wf (s : list var) (x:var) (y: option var) (p:pred) : Prop :=
  match p with Unit br => bound_wf s br
             | Lt br => bound_wf s br
             | Space n m => True
             | Fun f => True
             | Rel z br => (match y with None => False | Some y' => (x = z /\ bound_wf [y'] br) end)
             | Conj p1 p2 => pred_wf s x y p1 /\ pred_wf s x y p2
  end.


(* The first var is the name of the cell, and the second var is the varible
   for the effective quantum gate number used in a pred and a gate. *)
Inductive fvar : Set := Pair: var -> var -> fvar.

(* an example circuit using the predicate above. 
   bcx takes a variable representing the gates, the pred is a predicate defining
   the variable, and variables appears in pred must be bounded by var. *)
Inductive bccom :=
| bcskip
| bcx (x : var) (p : pred)
| bcnot (x : var) (p :pred) (b : bcseq)

 with bcseq :=
    | seq (b: bccom) (bcs : list bccom).

(* well-formedness of a bccom and bcseq based on the well-formedness of pred. *)
Fixpoint bccom_wf (s : list var) (y: option var) (b: bccom) : Prop :=
  match b with bcskip => True
             | bcx x p => pred_wf s x y p
             | bcnot x p b => pred_wf s x y p /\ bcseq_wf s (Some x) b
  end
  with bcseq_wf (s : list var) (y: option var) (b: bcseq) : Prop :=
    match b with seq b' bs =>  fold_left (fun pr b1 => pr /\ bccom_wf s y b1) (b'::bs) True end. 

(* Adding load/store opreation to transform qubits to bits. *)
Inductive moves : Set := | store (q:var) (v:var) (* store a 2^n qubit in cell q to register v. *)
                         | load (q:var) (v:var) (* load a value in register v to 2^n qubit in cell q. *).

(* Operations for arith bits. *)
Inductive expr : Set :=
      | add (x:var) (v1:var) (v2:var) (* x = v1 + v2 *)
      | sub (v1:var) (v2:var) (* x = v1 - v2 *)
      | mul (v1:var) (v2:var) (* x = v1 * v2 *)
      | div (v1:var) (v2:var) (* x = v1 / v2 *) 
      | modu (v1:var) (v2:var)  (* x = v1 % v2 *).

Inductive oper : Set :=
         | Qop (q:var) (b:bcseq)
         (* an quantum op is a sequence of quantum exprs and a cell name q indicating which cell the exps are applied.*)
         | Cop (b : moves)
         | Nop (e:expr).


(* a state is a quantum state in the first piece and normal bit registers. *)
Definition state : Set := ((var -> (nat * (nat -> bool))) * (nat * (var -> nat))).

Definition exec_bcx f x := update f x ((¬ (f x))).

Fixpoint exec_bcxs f n := 
  match n with
        | 0 => exec_bcx f 0
        | S m => exec_bcxs (exec_bcx f m) m
  end.

(*
Inductive interpret : bccom -> nat -> (nat -> bool) -> (nat -> bool) -> Prop :=
  | BCSKIP : forall n f, interpret (NVar bcskip) n f f
  | BCX : forall n x f, interpret (SVar x bcx) n f (exec_bcxs f n).

Inductive eval : list bcfun -> state -> state -> Prop :=
  | Empty : forall S, eval [] S S
  | One : forall x y n s s' theop ops l S, 
      S x = (n,s) -> interpret theop n s s' ->
        eval ((BFun (Pair x y) (AList (theop::ops)))::l) S (update S x (n,s')).
*)



