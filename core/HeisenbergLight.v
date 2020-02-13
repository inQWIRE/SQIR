Require Import QWIRE.Prelim.
Require Import SQIR.

(* The Clifford Set of Unitary Matrices *)
Inductive Clifford : nat -> Set := 
  | U_H                  : Clifford 1 
  | U_S                  : Clifford 1 
  | U_CNOT               : Clifford 2.

Definition clifford_ucom := ucom Clifford.

Local Open Scope ucom.

(* Some useful shorthands. *)
Definition CNOT {dim} m n : clifford_ucom dim := uapp2 U_CNOT m n.  
Definition H {dim} n : clifford_ucom dim := uapp1 U_H n.  
Definition S {dim} n : clifford_ucom dim := uapp1 U_S n.  
Definition Z {dim} n : clifford_ucom dim := S n ; S n.
Definition X {dim} n : clifford_ucom dim := H n; Z n; H n. 
(* Y = iXZ *)
(* Definition Y {dim} n : clifford_ucom dim := X n; Z n. *)
Definition I {dim} n : clifford_ucom dim := H n; H n. 
Definition CZ {dim} m n : clifford_ucom dim :=
  H n ; CNOT m n ; H n.
Definition SWAP {dim} m n : clifford_ucom dim :=
  CNOT m n; CNOT n m; CNOT m n.

Inductive htype : Set := II | XX | YY | ZZ.

(* From Gottesman, table 1 *)
Definition apply1 (c : Clifford 1) (b : htype) : htype :=
  match c, b with 
  | U_H, II => II (* noop *)
  | U_H, XX => ZZ
  | U_H, YY => YY (* inferred *)
  | U_H, ZZ => XX
  | U_S, II => II (* noop *)
  | U_S, XX => YY
  | U_S, YY => XX (* inferred *)
  | U_S, ZZ => ZZ
  end.

(* CNOT (h ⊗ II) *)
Definition apply_cnot1 (h : htype) : htype * htype :=
  match h with
  | II => (II, II)
  | XX => (XX, XX)
  | ZZ => (ZZ, II)
  | YY => (YY, XX) (* inferred *)
  end.
           
(* CNOT (II ⊗ h) *)
Definition apply_cnot2 (h : htype) : htype * htype :=
  match h with
  | II => (II, II)
  | XX => (II, XX)
  | ZZ => (ZZ, ZZ)
  | YY => (ZZ, YY) (* inferred *)
  end.

Definition h_times (h1 h2 : htype) :=
  match h1, h2 with
  | II, h2 => h2
  | h1, II => h1
  | XX, XX => II
  | XX, YY => ZZ
  | XX, ZZ => YY
  | YY, XX => ZZ
  | YY, YY => II
  | YY, ZZ => XX
  | ZZ, XX => YY
  | ZZ, YY => XX
  | ZZ, ZZ => II
  end.

Infix "*" := h_times.

Definition apply_cnot (h1 h2 : htype) : htype * htype :=
  let (h11, h12) := apply_cnot1 h1 in                
  let (h21, h22) := apply_cnot2 h2 in
  (h11 * h21, h12 * h22).

(* Belongs in Prelim -- and Coq standard lib *)
Lemma fold_if : forall (b : bool), (if b then true else false) = b.
Proof. destruct b; easy. Qed.

Lemma II_1_l : forall h, II * h = h.
Proof. reflexivity. Qed.

Lemma II_1_r : forall h, h * II = h.
Proof. intros []; reflexivity. Qed.

Lemma h_times_inv : forall h, h * h = II.
Proof. intros []; reflexivity. Qed.

Example CNOT_IX : apply_cnot II XX = (II, XX).
Proof. reflexivity. Qed.
Example CNOT_XI : apply_cnot XX II = (XX, XX).
Proof. reflexivity. Qed.
Example CNOT_IZ : apply_cnot II ZZ = (ZZ, ZZ).
Proof. reflexivity. Qed.
Example CNOT_ZI : apply_cnot ZZ II = (ZZ, II).
Proof. reflexivity. Qed.
Example CNOT_XX : apply_cnot XX XX = (XX, II).
Proof. reflexivity. Qed.

Definition h_state := list htype. 

Definition all_X_state (dim : nat) := repeat XX dim.
Definition all_Y_state (dim : nat) := repeat YY dim.
Definition all_Z_state (dim : nat) := repeat ZZ dim.
Definition all_I_state (dim : nat) := repeat II dim. (* should never appear *)

(*
Fixpoint apply_at {A} (f : A -> A) (i : nat) (l : list A) : list A :=
  match l, i with
  | [], _                  => []
  | a :: l', 0              => f a :: l'
  | a :: l', Datatypes.S i' => a :: apply_at f i' l' 
  end.
*)

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x , y , .. , z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.

Fixpoint count {A} (f : A -> bool) (l : list A) : nat :=
  match l with
  | [] => 0
  | a :: l' => if f a then 1 + (count f l') else count f l'
  end. 

Fixpoint h_eval {dim} (c : clifford_ucom dim) (st : h_state) : h_state :=
  match c with
  | c1 ; c2      => h_eval c2 (h_eval c1 st)
  | uapp1 U n    => update_at st n (apply1 U (nth n st II)) 
  | uapp2 _ m n  => let (h1,h2) := apply_cnot (nth m st II) (nth n st II) in
                   update_at (update_at st m h1) n h2
  | _            => all_I_state dim (* no 3-qubit gates in our denotation function *) 
  end.
  
(** * Examples from Gottesman Paper *)

(* Example 1 *)

Lemma SWAP_X1 : h_eval (@SWAP 2 0 1) [XX,II] = [II,XX].
Proof. reflexivity. Qed.

Lemma SWAP_basis : forall (h1 h2 : htype),
 h_eval (@SWAP 2 0 1) [h1,h2] = [h2,h1].
Proof. intros [] []; subst; reflexivity. Qed.

(* Could reduce to a two case proof and add a proof that this is
   sufficient to reason about all cases.  *)

(* Example 2 *)

Definition had_cnot : clifford_ucom 2 := 
  H 0; H 1; CNOT 0 1; H 0; H 1.

Lemma had_cnot_notc : forall (h1 h2 : htype),
  h_eval had_cnot [h1,h2] = h_eval (@CNOT 2 1 0) [h1,h2].   
Proof. intros [] []; reflexivity. Qed.

(* TODO: Want a general notion of equality between programs. *)

(* Example 3 *)

Definition hitite_code : clifford_ucom 2 := 
  H 0; S 1; CNOT 0 1; H 1; CNOT 0 1.

Lemma hitite_X1 : h_eval hitite_code [XX,II] = [ZZ,II].
Proof. reflexivity. Qed.

(* Gottesman puts the negation in from of the II *)
Lemma hitite_X2 : h_eval hitite_code [II,XX] = [II, YY].
Proof. reflexivity. Qed.

(* Gottesman uses [-YY,YY] *)
Lemma hitite_Z1 : h_eval hitite_code [ZZ,II] = [YY, YY].
Proof. reflexivity. Qed.

Lemma hitite_Z2 : h_eval hitite_code [II,ZZ] = [ZZ, XX].
Proof. reflexivity. Qed.

(* Example 4 *)

Definition cnot_notc : clifford_ucom 2 := CNOT 0 1; CNOT 1 0.

(* unlabelled case *)
Lemma cnot_notc_Z2 : h_eval cnot_notc [II,ZZ] = [ZZ,II].
Proof. reflexivity. Qed.

Lemma cnot_notc_X1 : h_eval cnot_notc [XX,II] = [II,XX].
Proof. reflexivity. Qed.

Lemma cnot_notc_Z1 : h_eval cnot_notc [ZZ,II] = [ZZ,ZZ].
Proof. reflexivity. Qed.

(* Example 5 *)

Definition bell : clifford_ucom 2 := H 0; CNOT 0 1.

Lemma bell_Z1 : h_eval bell [ZZ,II] = [XX,XX].
Proof. reflexivity. Qed.

Lemma bell_Z2 : h_eval bell [II,ZZ] = [ZZ,ZZ].
Proof. reflexivity. Qed.

(* Example 6 *)

(* Can we represent this as a program? *)

(* Example 7 *)

Definition ec_code : clifford_ucom 4 := 
  H 3; CNOT 0 2; CNOT 1 2; CNOT 3 0; CNOT 3 1; CNOT 3 2.

(* What to prove? *)

(* Example 8 *)

(* Example 9 *)

(* Now with measurement! *)

(* Example 10: Teleportation *)

(* Measurement-free teleportation with bell initialization *)

Definition bell' : clifford_ucom 3 := H 1; CNOT 1 2.

Definition alice : clifford_ucom 3 := CNOT 0 1; H 0.

Definition bob : clifford_ucom 3 := CNOT 1 2; CZ 0 2.

Definition teleport : clifford_ucom 3 := bell'; alice; bob.

Lemma alice_X1 : h_eval alice [XX,II,II] = [ZZ,XX,II].
Proof. reflexivity. Qed.

Lemma alice_Z1 : h_eval alice [ZZ,II,II] = [XX,II,II].
Proof. reflexivity. Qed.

Lemma bob_X1 : h_eval bob [ZZ,XX,II] = [II,XX,XX].
Proof. reflexivity. Qed.

Lemma bob_Z1 : h_eval bob [XX,II,II] = [XX,II,ZZ].
Proof. reflexivity. Qed.

Lemma teleport_X1 : h_eval teleport [XX,II,II] = [II,XX,XX].
Proof. simpl. reflexivity. Qed.

Lemma teleport_Z1 : h_eval teleport [ZZ,II,II] = [XX,II,ZZ].
Proof. simpl. reflexivity. Qed.

(* Example 11: Remove XOR *)


(** Own examples *)

(* GHZ state *)

