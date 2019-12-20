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

Definition h_basis_to_config (b : h_basis) : h_config :=
  match b with 
  | BX => XX
  | BZ => ZZ
  end.

Definition h_apply1 (c : Clifford 1) (b : h_basis) : h_config :=
  match c, b with 
  | U_H, BX => ZZ
  | U_H, BZ => XX
  | U_S, BX => YY
  | U_S, BZ => ZZ
  end.

(* (BX, false) ≡ XX ⊗ II, (BX, true) ≡ II ⊗ XX *)
Definition h_apply_cnot (b : h_basis) (i : bool) : h_config * h_config :=
  match b, i with 
  | BX, false => (XX, XX)
  | BX, true  => (II, XX) 
  | BZ, false => (ZZ, II)
  | BZ, true  => (ZZ, ZZ) 
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

(* Belongs in Prelim -- and Coq standard lib *)
Lemma fold_if : forall (b : bool), (if b then true else false) = b.
Proof. destruct b; easy. Qed.

Lemma II_1_l : forall h, II * h = h.
Proof.
  intros [[[n i] x] z].
  simpl.
  repeat rewrite xorb_false_r.
  repeat rewrite fold_if.
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

Definition lift_to_config (f : h_basis -> h_config) : 
  h_config -> h_config := 
  fun x => match x with (n, i, x, z) => 
                     (n, i, false, false) * 
                     (if x then f BX else II) * 
                     (if z then f BZ else II)
        end. 

Lemma to_config_commutes : forall f b,
  lift_to_config f (h_basis_to_config b) = f b. 
Proof.
  intros f []; simpl.
  - destruct (f BX) as [[[n i] x] z]; simpl.
    repeat rewrite andb_false_r.
    repeat rewrite xorb_false_r.
    repeat rewrite fold_if.
    reflexivity.
  - destruct (f BZ) as [[[n i] x] z]; simpl.
    repeat rewrite xorb_false_r.
    repeat rewrite fold_if.
    reflexivity.
Qed.

(* I think n1, n2, i1 and i2 can distribute -- that is, we could combine them in 
   the first term if we desired. *)
Definition lift_to_config_pair (f : h_basis -> bool -> h_config * h_config) : 
  h_config -> h_config -> h_config * h_config :=
  fun h1 h2 => match h1 with (n1, i1, x1, z1) =>
            match h2 with (n2, i2, x2, z2) =>
              let (FX1l,FX1r) := if x1 then f BX false else (II,II) in 
              let (FX2l,FX2r) := if x2 then f BX true else (II,II) in 
              let (FZ1l,FZ1r) := if z1 then f BZ false else (II,II) in 
              let (FZ2l,FZ2r) := if z2 then f BZ true else (II,II) in 
              ((n1, i1, false, false) * FX1l * FX2l * FZ1l * FZ2l,
               (n2, i2, false, false) * FX1r * FX2r * FZ1r * FZ2r)
            end
            end.

Example CNOT_IX : lift_to_config_pair h_apply_cnot II XX = (II, XX).
Proof. reflexivity. Qed.
Example CNOT_XI : lift_to_config_pair h_apply_cnot XX II = (XX, XX).
Proof. reflexivity. Qed.
Example CNOT_IZ : lift_to_config_pair h_apply_cnot II ZZ = (ZZ, ZZ).
Proof. reflexivity. Qed.
Example CNOT_ZI : lift_to_config_pair h_apply_cnot ZZ II = (ZZ, II).
Proof. reflexivity. Qed.
Example CNOT_XX : lift_to_config_pair h_apply_cnot XX XX = (XX, II).
Proof. reflexivity. Qed.

Definition h_state := list h_config. 

Definition all_X_state (dim : nat) := repeat XX dim.
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

Definition normalize_h_state (h : h_state) :=
  let negs := count (fun h => match h with (n,_,_,_) => n end) h in
  let ims  := count (fun h => match h with (_,i,_,_) => i end) h in
  let normed := map (fun h => match h with (_,_,x,z) => (false,false,x,z) end) h in
  let im   := ims mod 2 =? 1 in
  let neg  := (negs + ims / 2) mod 2 =? 1 in
  match normed with 
  | [] => []
  | (_,_,x,z) :: hs => (neg, im, x, z) :: hs 
  end. 

Fixpoint h_eval {dim} (c : clifford_ucom dim) (st : h_state) : h_state :=
  match c with
  | c1 ; c2      => h_eval c2 (h_eval c1 st)
  | uapp1 U n    => let h := lift_to_config (h_apply1 U) (nth n st II) in
                   update_at st n h 
  | uapp2 _ m n  => let (h1,h2) := lift_to_config_pair h_apply_cnot 
                                                (nth m st II) (nth n st II) in
                   update_at (update_at st m h1) n h2
  | _            => all_I_state dim (* no 3-qubit gates in our denotation function *) 
  end.



  
(** * Examples from Gottesman Paper *)

(* Example 1 *)

Lemma SWAP_XI : h_eval (@SWAP 2 0 1) [XX,II] = [II,XX].
Proof. reflexivity. Qed.

Lemma SWAP_basis : forall (b1 b2 : h_basis) (h1 h2 : h_config),
 h1 = h_basis_to_config b1 ->
 h2 = h_basis_to_config b2 ->
 h_eval (@SWAP 2 0 1) [h1,h2] = [h2,h1].
Proof. 
  intros [] [] h1 h2 ? ?; subst; reflexivity.
Qed.

(* Add a lemma that this being true on X and Z makes it 
   true on all bases? 

   Then we can prove a more general version of SWAP_basis *)

(* Example 2 *)

Definition had_cnot : clifford_ucom 2 := 
  H 0; H 1; CNOT 0 1; H 0; H 1.

Lemma had_cnot_notc : forall (b1 b2 : h_basis) (h1 h2 : h_config),
  h1 = h_basis_to_config b1 ->
  h2 = h_basis_to_config b2 ->
  normalize_h_state (h_eval had_cnot [h1,h2]) = 
  normalize_h_state (h_eval (@CNOT 2 1 0) [h1,h2]).   
Proof.  
  intros [] [] h1 h2 ? ?; subst; try reflexivity.
Qed.

(* TODO: Want a general notion of equality between programs. *)

(* TODO: Need to get h_basis_to_config coercion working *)

(* Example 3 *)

Definition hitite_code : clifford_ucom 2 := 
  H 0; S 1; CNOT 0 1; H 1; CNOT 0 1.

Lemma hitite_X1 : h_eval hitite_code [XX,II] = [ZZ,II].
Proof. reflexivity. Qed.

(* Gottesman puts the negation in from of the II *)
Lemma hitite_X2 : h_eval hitite_code [II,XX] = [II, -1*YY].
Proof. reflexivity. Qed.

(* Gottesman uses [-YY,YY] *)
Lemma hitite_Z1 : h_eval hitite_code [ZZ,II] = [XX*ZZ, XX*ZZ].
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

(* Example 11: Remove XOR *)
