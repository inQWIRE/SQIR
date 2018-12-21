Require Import Reals.
Require Import Vector.

Import VectorNotations.
Notation "[ x , y , .. , z ]" := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..)) : vector_scope.

Definition Var := nat.
Definition iList := (@t Var).

Inductive Unitary : nat -> Set := 
  | _H         : Unitary 1 
  | _X         : Unitary 1
  | _Y         : Unitary 1
  | _Z         : Unitary 1
  | _R_        : R -> Unitary 1 
  | ctrl      : forall {n} (U : Unitary n), Unitary (S n).
(* maybe add swap? *)

Notation CNOT := (ctrl _X).
Notation CCNOT := (ctrl (ctrl _X)).
Notation _S := (_R_ (PI / 2)). 
Notation _T := (_R_ (PI / 4)). (* π / 8 gate *)

Inductive prog : Set :=
| skip : prog
| seq : prog -> prog -> prog
| app : forall {n}, Unitary n -> iList n -> prog
| meas : Var -> prog -> prog -> prog
| reset : Var -> prog.

Definition singleton (v : Var) : iList 1 := [v].

Coercion singleton : Var >-> iList. 
Notation "p1 ; p2" := (seq p1 p2) (at level 50).
Notation "'mif' v 'then' p1 'else' p2" := (meas v p1 p2) (at level 40).
Notation "'measure' v" := (meas v skip skip) (at level 40).
Notation "v *= u" := (app u v) (at level 20).
Notation "v <- 0" := (reset v) (at level 20).
Notation "v <- 1" := (reset v ; v *= _X) (at level 20).

Fixpoint repeat (n : nat) (p : prog) : prog :=
  match n with
  | 0    => skip
  | S n' => p ; repeat n' p
  end.

Fixpoint while (n : nat) (v : Var) (p : prog) : prog :=
  match n with
  | 0    => skip
  | S n' => mif v then p ; while n' v p else skip
end.

(* Teleport Example *)

Section Teleport.
  
Variable q a b : Var.

Definition bell00 : prog :=
  a <- 0; b <- 0;
  a *= _H;
  [a,b] *= CNOT.

Definition alice : prog :=
  [q,a] *= CNOT;
  q *= _H      ;
  measure q;
  measure a.

Definition bob : prog :=
  [q,b] *= ctrl _X;
  [q,a] *= ctrl _Z.

Definition teleport := bell00 ; alice; bob.

End Teleport.


    

  