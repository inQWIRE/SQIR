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
   | Unit : bound -> pred
   | Lt : bound -> pred
   | Space : bound -> pred
   | Rel : var -> bound -> pred
   | Fun : (nat -> bool) -> pred
   | Conj : pred -> pred -> pred.


(* The first var is the name of the cell, and the second var is the varible
   for the effective quantum gate number used in a pred and a gate. *)
Inductive fvar : Set := Pair: var -> var -> fvar.

(* an example circuit using the predicate above. 
   bcx takes a variable representing the gates, the pred is a predicate defining
   the variable, and variables appears in pred must be bounded by var. *)
Inductive bcname :=
| bcskip
| bcx 
.


(* Define the basis element of an opeartion in QK *)
Inductive bccom : Set := 
 | NVar (b : bcname)
 | SVar (v : fvar) (b : bcname)
 | PVar (v : fvar) (b :bcname) (p : pred)
.

(* Define a quantum operation function. *)
Inductive bcfun : Set := BFun : fvar -> bcbody -> bcfun

  with bcbody : Set :=
      | AList : list bccom -> bcbody
      | CNot : fvar -> fvar -> pred -> bcfun -> bcbody.

Definition state := var -> (nat * (nat -> bool)).

Definition exec_bcx f x := update f x ((¬ (f x))).

Fixpoint exec_bcxs f n := 
  match n with
        | 0 => exec_bcx f 0
        | S m => exec_bcxs (exec_bcx f m) m
  end.

Inductive interpret : bccom -> nat -> (nat -> bool) -> (nat -> bool) -> Prop :=
  | BCSKIP : forall n f, interpret (NVar bcskip) n f f
  | BCX : forall n x f, interpret (SVar x bcx) n f (exec_bcxs f n).

Inductive eval : list bcfun -> state -> state -> Prop :=
  | Empty : forall S, eval [] S S
  | One : forall x y n s s' theop ops l S, 
      S x = (n,s) -> interpret theop n s s' ->
        eval ((BFun (Pair x y) (AList (theop::ops)))::l) S (update S x (n,s')).




