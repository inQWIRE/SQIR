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

(* Inductive h_basis : Set := XX | ZZ | II. *)
Inductive h_basis : Set := BX | BZ.

(* 1st boolean is negation, 2nd is i, 3rd is X, 4th is Z. *) 
(* Note: If we ignore global phase, we can leave out the first two
   elements AND treat X and Z as commutative (currently we assume
   (f,f,t,t) is XZ, not ZX) *)
Definition h_config := (bool * bool * bool * bool)%type.

(*
Definition h_config_from_basis (b : h_basis) : h_config :=
  match b with
  | BX => (false, false, true, false)
  | BZ => (false, false, false, true)
  end.
  
Coercion h_config_from_basis : h_basis >-> h_config.
*)

Notation "-1" := (true, false, false, false).
Definition ii : h_config := (false, true, false, false).
Definition II : h_config := (false, false, false, false).
Definition XX : h_config := (false, false, true, false).
Definition ZZ : h_config := (false, false, false, true).
Definition YY : h_config := (false, true, true, true). (* YY = iXZ = -iZX *)

Definition h_apply1 (c : Clifford 1) (b : h_basis) : h_config :=
  match c, b with 
  | U_H, BX => ZZ
  | U_H, BZ => XX
  | U_S, BX => YY
  | U_S, BZ => ZZ
  end.

(* (BX, false) ≡ II ⊗ XX, (BX, true) ≡ XX ⊗ II *)
Definition h_apply_cnot (b : h_basis) (i : bool) : h_config * h_config :=
  match b, i with 
  | BX, false => (II, XX) 
  | BX, true  => (XX, XX)
  | BZ, false => (ZZ, ZZ) 
  | BZ, true  => (ZZ, II)
  end.

(* OLD :
Definition h_apply_cnot (b1 b2 : h_basis) : h_config * h_config :=
  match b1, b2 with 
  | II, II => (II, II)
  | XX, II => (XX, XX)
  | II, XX => (II, XX)
  | XX, XX => (XX, II)
  | XX, II => (XX, XX)
  | II, XX => (II, XX)
  | XX, XX => (XX, II)
  end.
*)

Definition h_times (h1 h2 : h_config) :=
  match h1, h2 with (n1, i1, x1, z1), (n2, i2, x2, z2) => 
    let n3 := z1 && x2 in (* Z then X anticommute *)
    let n4 := i1 && i2 in (* two imaginary components *)
    (n1 ⊕ n2 ⊕ n3 ⊕ n4, i1 ⊕ i2, x1 ⊕ x2, z1 ⊕ z2)
  end.

Infix "*" := h_times.

Example X2_I : XX * XX = II. Proof. reflexivity. Qed.
Example Z2_I : ZZ * ZZ = II. Proof. reflexivity. Qed.
Example Y2_I : YY * YY = II. Proof. reflexivity. Qed.
Example XY_iZ : XX * YY = ii * ZZ. Proof. reflexivity. Qed.
Example YZ_iX : YY * ZZ = ii * XX. Proof. reflexivity. Qed.
Example ZX_iY : ZZ * XX = ii * YY. Proof. reflexivity. Qed.
Example YX_niZ : YY * XX = -1 * ii * ZZ. Proof. reflexivity. Qed.
Example ZY_niX : ZZ * YY = -1 * ii * XX. Proof. reflexivity. Qed.
Example XZ_niY : XX * ZZ = -1 * ii * YY. Proof. reflexivity. Qed.

Lemma II_1_l : forall h, II * h = h.
Proof.
  intros [[[n i] x] z].
  simpl.
  repeat rewrite xorb_false_r.
  assert (forall (b : bool), (if b then true else false) = b) by (intros []; easy). 
  repeat rewrite H0.
  reflexivity.
Qed.

Lemma II_1_r : forall h, h * II = h.
Proof.
  intros [[[n i] x] z].
  simpl.  
  repeat rewrite andb_false_r.
  repeat rewrite xorb_false_r.
  reflexivity.
Qed.

Definition lift_to_config (f : h_basis -> h_config) : h_config -> h_config := 
  fun x => match x with (n, i, x, z) => 
          (n, i, false, false) * (if x then f BX else II) * (if z then f BZ else II)
        end. 



