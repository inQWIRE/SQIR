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
   | Unit : var -> bound -> pred (* x = m * var + m for exactly one *)
   | Lt : var -> bound -> pred (* x < m * var + m *)
   | Space : var -> nat -> nat -> pred (* forall x, x =  m * x + m for every one that sat the formula. *)
   | Rel : var -> var -> bound -> pred (* forall x, x := m * y + m *)
   | Fun : var -> (nat -> bool) -> pred (* forall x , f x *)
   | Conj : pred -> pred -> pred. (* pred /\ pred *)

Definition bound_wf (s : list var) (b:bound) : Prop :=
  match b with Br n y m => In y s end.

Fixpoint pred_wf (s : list var) (y: option var) (p:pred) : Prop :=
  match p with Unit x br => bound_wf (x::s) br
             | Lt x br => bound_wf (x::s) br
             | Space x n m => True
             | Fun x f => True
             | Rel x z br => (match y with None => False | Some y' => (x = z /\ bound_wf (x::s) br) end)
             | Conj p1 p2 => pred_wf s y p1 /\ pred_wf s y p2
  end.


(* The first var is the name of the cell, and the second var is the varible
   for the effective quantum gate number used in a pred and a gate. *)
Inductive fvar : Set := Pair: var -> var -> fvar.

(* an example circuit using the predicate above. 
   bcx takes a variable representing the gates, the pred is a predicate defining
   the variable, and variables appears in pred must be bounded by var. *)
Inductive one_op :=
  | QX | QY | QH | QZ | QS | QT.

Inductive two_op := QSWAP | QCX | QCZ.

Inductive bccom : Set :=
| bcskip
| one (op : one_op) (x:var) (p:pred) (* apply a single qubit gate in a place at x that is defined by predicate p. *)
| two (op : two_op) (x:var) (y:var) (p:pred)
    (* apply a two qubit gate in a place at x and y that is defined by predicate p. *)
| cu (x : var) (x:var) (y:var) (p : pred) (bs : list one_op)
    (* apply a two qubit CU gate in a place at x and y that is defined by predicate p, followinng a series of ops on y. *)
| bcseq (b1:bccom) (b2:bccom)
   (* seqencing operators *)
| bciter (b:bccom) (x:var) (p:pred).
   (* repeat the b x times and x is defined by predicate p. *)

Declare Scope bccom_scope.
Delimit Scope bccom_scope with bccom.
Local Open Scope bccom.
Notation "p1 ; p2" := (bcseq p1 p2) (at level 50) : bccom_scope.
Parameter x y : var.
Definition const (n:nat) : bound := Br 0 x n.

(* Example programs using the quantum part of the language. *)
(* First example is the Simon algorithm. *)

Definition nH (n:nat) : bccom := one QH x (Lt x (const n)).
Definition csimon (n:nat) (U:bccom) : bccom := nH n; U ; nH n.

(* Second example is the deutsch_jozsa algorithm. *)
Definition XatN (n:nat) : bccom := one QX x (Unit x (const n)).
Definition cdeutsch_jozsa (n:nat) (U:bccom) : bccom := XatN n; nH (S n); U ; nH (S n).

(* Define Grover's algorithm. *)
Definition nCX (n:nat) : bccom := two (QCX) x y (Conj (Lt x (const (n-1))) (Unit x (const n))).
Definition nX (n:nat) : bccom := one QX x (Lt x (const n)).
Definition HatN (n:nat) : bccom := one QH x (Unit x (const n)).
Definition body (n:nat) (U:bccom) := U ; nH n; nX n; HatN (n-1) ; nCX n; HatN (n-1); nX n; nH n.
Definition grover (i n:nat) (U:bccom) := XatN n; nH (S n); bciter (body (S n) U) x (Unit x (const i)).


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
         | Qop (q:var) (b:bccom)
         (* an quantum op is a sequence of quantum exprs and a cell name q indicating which cell the exps are applied.*)
         | Cop (b : moves)
         | Nop (e:expr).

Inductive confi : Set := Fram (v:var) (n:nat) | Frams (v:var) (n:nat) (cf:confi).

Fixpoint confi_wf (cf:confi) (s: list var) : Prop :=
   match cf with Fram v n => In v s
               | Frams v n cf' => In v s /\ confi_wf cf' (v::s)
   end.


(* a state is a quantum state in the first piece and normal bit registers. 
   We assume that quantum cells are finite and classical registers are infinite. *)
Definition state : Set := ((var -> option (nat * (nat -> bool))) * (nat * (var -> nat))).

(* compiling the lang with confi and the size of regs to a state. *)
Fixpoint compile_fram (cf:confi) : ((var -> option (nat * (nat -> bool)))) := 
    match cf with Fram v n => (fun x => if x =? v then Some (n, fun _ => false) else None)
               | Frams v n cf' => (fun x => if x =? v then Some (n, fun _ => false) else compile_fram cf' x)
    end.

Definition compile (cf:confi) (n:nat) : state := (compile_fram cf, (n,fun _ => 0)).


(* First, we need to interpret the pred. *)
Definition eval_bound (y:var) (v:nat) (br : bound) : option nat :=
      match br with Br n x m => 
          if x =? y then Some (n * v + m) else None
      end.

(*
Fixpoint eval_pred (x:nat) (y:var) (v:nat) (u: option nat) (p : pred) : Prop :=
     match p with Unit br => 
          match eval_bound y v br with None => False
                                     | Some n => (x = n)
          end
               | Lt br => 
          match eval_bound y v br with None => False
                                     | Some n => (x < n)
          end
               | Space n m => (x mod n = m)
               | Rel z br => 
          match u with None => False
                    | Some u' =>
              match eval_bound z u' br with None => False
                   | Some uf => (x = uf)
              end
         end
       | Fun f => (f x = true)
       | Conj p1 p2 => eval_pred x y v u p1 /\ eval_pred x y v u p2
    end.



Definition exec_bcx f x := update f x ((¬ (f x))).

Fixpoint exec_bcxs f n := 
  match n with
        | 0 => exec_bcx f 0
        | S m => exec_bcxs (exec_bcx f m) m
  end.
*)
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



