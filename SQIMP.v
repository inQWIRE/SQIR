Require Import Reals.
Require Export List.
Export ListNotations.
Require Import Omega.

Inductive Unitary : nat -> Set := 
  | U_H         : Unitary 1 
  | U_X         : Unitary 1
  | U_Y         : Unitary 1
  | U_Z         : Unitary 1
  | U_R         : R -> Unitary 1 
  | U_CNOT      : Unitary 2.

(**********************)
(** Unitary Programs **)
(**********************)

Inductive ucom : Set :=
| uskip : ucom
| useq : ucom -> ucom -> ucom
| uapp : forall {n}, Unitary n -> list nat -> ucom.

(* Gate application definitions and notations *)

Delimit Scope ucom_scope with ucom.
Notation "p1 ; p2" := (useq p1 p2) (at level 50) : ucom_scope.
Notation "a *= U" := (uapp U [a]) (at level 0) : ucom_scope.

Open Scope ucom_scope.

(*
Notation "'H' a" := (uapp U_H [a]) (at level 0). 
Notation "'X' a" := (uapp U_X [a]) (at level 0). 
Notation "'Y' a" := (uapp U_Y [a]) (at level 0). 
Notation "'Z' a" := (uapp U_Z [a]) (at level 0). 
Notation "'R_' θ . a" := (uapp (U_R θ) [a]) (at level 0). (* not working *)
Notation "'CNOT' a ',' b" := (uapp U_CNOT (a::b::nil)) (at level 0). 
*)

Definition H a := uapp U_H [a].  
Definition X a := uapp U_X [a].  
Definition Y a := uapp U_Y [a].  
Definition Z a := uapp U_Z [a].  
Definition CNOT a b := uapp U_CNOT (a::b::nil).  
(* Definition S (a : nat) := uapp (U_R (PI / 2)) [a]. Dangerous clash *)
Definition T (a : nat) := uapp (U_R (PI / 4)) [a]. 

Definition CZ (a b : nat) : ucom :=
  H b ; CNOT a b ; H b.

Definition SWAP (a b : nat) : ucom :=
  CNOT a b; CNOT b a; CNOT a b.

(***********************)
(* Well Typed Circuits *)
(***********************)

Definition in_bounds (l : list nat) (max : nat) : Prop :=
  forall x, In x l -> x < max.

Definition in_bounds_b (l : list nat) (max : nat) :=
  forallb (fun x => x <? max) l.

Definition in_bounds_eq : forall l max, in_bounds_b l max = true <-> in_bounds l max.
Proof.
  intros l max.
  unfold in_bounds.
  setoid_rewrite forallb_forall.
  setoid_rewrite Nat.ltb_lt.
  reflexivity.
Qed.
  
Lemma in_bounds_pad : forall (l : list nat) (n k : nat), in_bounds l n -> in_bounds l (k + n).
Proof.
  intros l n k B x IN.
  apply B in IN.
  omega.
Qed.  

Lemma in_bounds_b_pad : forall (l : list nat) (n k : nat), in_bounds_b l n = true -> in_bounds_b l (k + n) = true.
Proof.
  setoid_rewrite in_bounds_eq.
  apply in_bounds_pad.
Qed.  

Inductive uc_well_typed : nat -> ucom -> Prop :=
| WT_uskip : forall dim, uc_well_typed dim uskip
| WT_seq : forall dim c1 c2, uc_well_typed dim c1 -> uc_well_typed dim c2 -> uc_well_typed dim (c1; c2)
| WT_app : forall dim n l (u : Unitary n), length l = n -> in_bounds l dim -> NoDup l -> uc_well_typed dim (uapp u l).

(* Equivalent boolean version *)
Fixpoint uc_well_typed_b (dim : nat) (c : ucom) : bool :=
  match c with
  | uskip    => true
  | c1 ; c2  => uc_well_typed_b dim c1 && uc_well_typed_b dim c2 
  | @uapp n u l => (length l =? n) && in_bounds_b l dim (* && boolean_no_dup *)
  end.

Close Scope ucom.

(**********************)
(** General Programs **)
(**********************)

Delimit Scope com_scope with com.
Local Open Scope com_scope.

Inductive com : Set :=
| skip : com
| seq : com -> com -> com
| app : forall {n}, Unitary n -> list nat -> com
(* | meas : nat -> com -> com -> com *)
| meas : nat -> com 
| reset : nat -> com.

Fixpoint from_ucom (c : ucom) : com :=
  match c with
  | uskip => skip
  | useq c1 c2 => seq (from_ucom c1) (from_ucom c2)
  | uapp u l => app u l
  end.

Coercion from_ucom : ucom >-> com.

Notation "p1 ; p2" := (seq p1 p2) (at level 50) : com_scope.

(* Notations for general measure_if: 
Notation "'mif' v 'then' p1 'else' p2" := (meas v p1 p2) (at level 40) : com_scope.
Notation "'measure' v" := (meas v skip skip) (at level 40) : com_scope.
Notation "'reset' v" := (meas v (X v) skip) (at level 40) : com_scope.
Notation "v <- 0" := (meas v (X v) skip) (at level 20) : com_scope.
Notation "v <- 1" := (meas v skip (X v)) (at level 20) : com_scope.
*)

Notation "'measure'" := meas : com_scope.
Notation "v <- 0" := (reset v) (at level 20) : com_scope.
Notation "v <- 1" := (reset v ; X v) (at level 20) : com_scope.

(* Notation "v *= u" := (app u v) (at level 20) : com_scope. *)

Fixpoint crepeat (n : nat) (p : com) : com :=
  match n with
  | 0    => skip
  | S n' => p ; crepeat n' p
  end.

(*
Fixpoint while (iters : nat) (v : nat) (p : com) : com :=
  match iters with
  | 0        => skip
  | S iters' => mif v then p ; while iters' v p else skip
  end.
 *)

(* Simple order reversal: No transposing, measurements and resets stay as they are. *)
Fixpoint reverse (c : com) :=
  match c with              
  | seq c1 c2 => seq (reverse c2) (reverse c1)
  | _ => c
  end.

(* Order reversal exchanging inits and measurements *)
Fixpoint reverse_m (c : com) :=
  match c with              
  | seq c1 c2        => seq (reverse c2) (reverse c1) 
  | reset v          => meas v
  | meas v           => reset v
  | _ => c
  end.

(* Teleport Example *)

Section Teleport.
  
Variable q a b : nat.

Definition bell00 : com :=
  a <- 0; b <- 0;
  H a;
  CNOT a b.

Definition alice : com :=
  CNOT q a;
  H q;
  measure q;
  measure a.

Definition bob : com :=
  CNOT q b;
  CZ q a.

Definition teleport := bell00 ; alice; bob.

End Teleport.

(* Superdense Coding Example *)

Section Superdense.

Variable a b : nat.

Definition encode (b1 b2 : bool): com :=
  if b2 then X a else skip;
  if b1 then Z a else skip.

(* note: 'decode' is just the reverse of bell00, can we define it in terms 
   of bell00 instead? *)
(* RNR: In principle, but it's not the reverse of the bell00 as currently defined. 
   (See the reverse functions above)
  *)
Definition decode : com :=
  CNOT a b;
  H a.

Definition superdense (b1 b2 : bool) := 
    bell00 a b; 
    encode b1 b2; 
    decode; 
    measure a; 
    measure b.

End Superdense.    


  