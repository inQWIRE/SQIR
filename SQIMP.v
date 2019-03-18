Require Import Reals.
Require Export List.

Export ListNotations.

Definition Var := nat.
Definition vList := (list Var).
Definition singleton (v : Var) : vList := [v].
Coercion singleton : Var >-> vList. 
Notation "[ x , y , .. , z ]" := (cons x (cons y .. (cons z (nil)) ..)) : list_scope.

Inductive Unitary : nat -> Set := 
  | _H         : Unitary 1 
  | _X         : Unitary 1
  | _Y         : Unitary 1
  | _Z         : Unitary 1
  | _R_        : R -> Unitary 1 
  | ctrl      : forall {n} (U : Unitary n), Unitary (S n).

Notation CNOT := (ctrl _X).
Notation CCNOT := (ctrl (ctrl _X)).
Notation _S := (_R_ (PI / 2)). 
Notation _T := (_R_ (PI / 4)). (* π / 8 gate *)

(** Unitary Programs **)

Inductive ucom : Set :=
| uskip : ucom
| useq : ucom -> ucom -> ucom
| uapp : forall {n}, Unitary n -> vList -> ucom.

Delimit Scope ucom_scope with ucom.
Notation "p1 ; p2" := (useq p1 p2) (at level 50) : ucom_scope.
Notation "v *= u" := (uapp u v) (at level 20) : ucom_scope.

Open Scope ucom.

Definition bounded (l : list nat) (max : nat) :=
  forallb (fun x => x <? max) l = true.

Inductive uc_well_typed : nat -> ucom -> Prop :=
| WT_uskip : forall dim, uc_well_typed dim uskip
| WT_seq : forall dim c1 c2, uc_well_typed dim c1 -> uc_well_typed dim c2 -> uc_well_typed dim (c1; c2)
| WT_app : forall dim n l (u : Unitary n), length l = n -> bounded l dim -> NoDup l -> uc_well_typed dim (l *= u).

Close Scope ucom.

(** General Programs **)

Delimit Scope com_scope with com.
Local Open Scope com_scope.

Inductive com : Set :=
| skip : com
| seq : com -> com -> com
| app : forall {n}, Unitary n -> vList -> com
| meas : Var -> com -> com -> com
| reset : Var -> com.

Notation "p1 ; p2" := (seq p1 p2) (at level 50) : com_scope.
Notation "v *= u" := (app u v) (at level 20) : com_scope.
Notation "'mif' v 'then' p1 'else' p2" := (meas v p1 p2) (at level 40) : com_scope.
Notation "'measure' v" := (meas v skip skip) (at level 40) : com_scope.
Notation "v <- 0" := (reset v) (at level 20) : com_scope.
Notation "v <- 1" := (reset v ; v *= _X)%com (at level 20) : com_scope.


Fixpoint crepeat (n : nat) (p : com) : com :=
  match n with
  | 0    => skip
  | S n' => p ; crepeat n' p
  end.

Fixpoint while (n : nat) (v : Var) (p : com) : com :=
  match n with
  | 0    => skip
  | S n' => mif v then p ; while n' v p else skip
end.

(* Teleport Example *)

Section Teleport.
  
Variable q a b : Var.

Definition bell00 : com :=
  a <- 0; b <- 0;
  a *= _H;
  [a,b] *= CNOT.

Definition alice : com :=
  [q,a] *= CNOT;
  q *= _H      ;
  measure q;
  measure a.

Definition bob : com :=
  [q,b] *= ctrl _X;
  [q,a] *= ctrl _Z.

Definition teleport := bell00 ; alice; bob.

End Teleport.



    

  