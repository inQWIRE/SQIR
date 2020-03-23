Require Import QWIRE.Prelim.
Require Import SQIR.

(* The Clifford Set of Unitary Matrices *)
Inductive CliffordT : nat -> Set := 
  | U_H                  : CliffordT 1 
  | U_S                  : CliffordT 1
  | U_T                  : CliffordT 1     
  | U_CNOT               : CliffordT 2.

Definition cliffordT_ucom := ucom CliffordT.

Local Open Scope ucom.

Notation s := S.

(* Proof of Y equivalence, requires Quantum.v:
Lemma SXSZ : phase_shift (PI/2) × σx × phase_shift (PI/2) × σz = σy.
Proof.
  solve_matrix.
  rewrite Cexp_PI2.
  reflexivity.
  rewrite Cexp_PI2.
  reflexivity.
Qed.
*)

(* Some useful shorthands. *)
Definition CNOT {dim} m n : cliffordT_ucom dim := uapp2 U_CNOT m n.  
Definition H {dim} n : cliffordT_ucom dim := uapp1 U_H n.  
Definition S {dim} n : cliffordT_ucom dim := uapp1 U_S n.  
Definition T {dim} n : cliffordT_ucom dim := uapp1 U_T n. 
Definition Z {dim} n : cliffordT_ucom dim := S n ; S n.
Definition TDAG {dim} n : cliffordT_ucom dim := Z n; S n; T n. 
Definition X {dim} n : cliffordT_ucom dim := H n; Z n; H n. 
(* Y = iXZ = -iZX *)
(* Definition Y {dim} n : cliffordT_ucom dim := X n; Z n. *)
Definition Y {dim} n : cliffordT_ucom dim := S n; X n; Z n; S n.
Definition I {dim} n : cliffordT_ucom dim := H n; H n. 
Definition CZ {dim} m n : cliffordT_ucom dim :=
  H n ; CNOT m n ; H n.
Definition SWAP {dim} m n : cliffordT_ucom dim :=
  CNOT m n; CNOT n m; CNOT m n.

Inductive htype : Set := II | XX | YY | ZZ | QQ.

Notation "⊤" := QQ.

(* From Gottesman, table 1 *)

Definition apply1 (c : CliffordT 1) (b : htype) : htype :=
  match c, b with 
  | U_H, II => II (* noop *)
  | U_H, XX => ZZ
  | U_H, YY => YY (* inferred *)
  | U_H, ZZ => XX
  | U_H, ⊤ => ⊤   (* annihilator *)
  | U_S, II => II (* noop *)
  | U_S, XX => YY
  | U_S, YY => XX (* inferred *)
  | U_S, ZZ => ZZ
  | U_S, ⊤ => ⊤   (* annihilator *)
  | U_T, II => II (* noop *)
  | U_T, XX => ⊤  (* outside Clifford *)
  | U_T, YY => ⊤  (* outside Clifford *)
  | U_T, ZZ => ZZ
  | U_T, ⊤ => ⊤   (* annihilator *)
  end.

(* CNOT (h ⊗ II) *)
Definition apply_cnot1 (h : htype) : htype * htype :=
  match h with
  | II => (II, II)
  | XX => (XX, XX)
  | ZZ => (ZZ, II)
  | YY => (YY, XX) (* inferred *)
  | ⊤ =>  (⊤, ⊤)   (* maybe overkill? *)
  end.
           
(* CNOT (II ⊗ h) *)
Definition apply_cnot2 (h : htype) : htype * htype :=
  match h with
  | II => (II, II)
  | XX => (II, XX)
  | ZZ => (ZZ, ZZ)
  | YY => (ZZ, YY) (* inferred *)
  | ⊤ =>  (⊤, ⊤)   (* maybe overkill? *)
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
  | ⊤, _   => ⊤
  | _, ⊤   => ⊤
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

Lemma h_times_inv : forall h, h <> ⊤ -> h * h = II.
Proof. intros [] N; easy. Qed.

(* Sanity Checks *)
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
Definition all_top (dim : nat) := repeat ⊤ dim.

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x , y , .. , z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.

Fixpoint h_eval {dim} (c : cliffordT_ucom dim) (st : h_state) : h_state :=
  match c with
  | c1 ; c2      => h_eval c2 (h_eval c1 st)
  | uapp1 U n    => update_at st n (apply1 U (nth n st II)) 
  | uapp2 _ m n  => let (h1,h2) := apply_cnot (nth m st II) (nth n st II) in
                   update_at (update_at st m h1) n h2
  | _            => all_I_state dim (* no 3-qubit gates in our denotation function *) 
  end.

(** * Equivalence and Structural Rules **)

(* Precondition about typing? *)
Definition h_equiv {dim} (c1 c2 : cliffordT_ucom dim) := 
  h_eval c1 = h_eval c2.

Infix "≡" := h_equiv (at level 80).

Lemma h_equiv_refl : forall {dim} (c1 : cliffordT_ucom dim), c1 ≡ c1.
Proof. easy. Qed.

Lemma h_equiv_sym : forall {dim} (c1 c2 : cliffordT_ucom dim), c1 ≡ c2 -> c2 ≡ c1. 
Proof. easy. Qed.

Lemma h_equiv_trans : forall {dim} (c1 c2 c3 : cliffordT_ucom dim), 
  c1 ≡ c2 -> c2 ≡ c3 -> c1 ≡ c3. 
Proof. intros dim c1 c2 c3 H12 H23. unfold h_equiv. rewrite H12. easy. Qed.

Lemma hseq_assoc : forall {dim} (c1 c2 c3 : cliffordT_ucom dim), 
  ((c1 ; c2) ; c3) ≡ (c1 ; (c2 ; c3)).
Proof.
  intros dim c1 c2 c3. 
  unfold h_equiv. simpl.
  reflexivity.
Qed.

Lemma hseq_congruence : forall {dim} (c1 c1' c2 c2' : cliffordT_ucom dim),
    c1 ≡ c1' ->
    c2 ≡ c2' ->
    c1 ; c2 ≡ c1' ; c2'.
Proof.
  intros dim c1 c1' c2 c2' Ec1 Ec2.
  unfold h_equiv; simpl.
  rewrite Ec1, Ec2.
  reflexivity.
Qed.

Add Parametric Relation (dim : nat) : (cliffordT_ucom dim) (@h_equiv dim)
  reflexivity proved by h_equiv_refl
  symmetry proved by h_equiv_sym
  transitivity proved by h_equiv_trans
  as h_equiv_rel.

Require Import Setoid.

Add Parametric Morphism (dim : nat) : (@useq CliffordT dim)
  with signature (@h_equiv dim) ==> (@h_equiv dim) ==> (@h_equiv dim) as hseq_mor.
Proof. intros x y H x0 y0 H0. apply hseq_congruence; easy. Qed.

Lemma test_rel : forall (dim : nat) (c1 c2 : cliffordT_ucom dim), c1 ≡ c2 -> c2 ≡ c1.
Proof. intros. rewrite H0. reflexivity. Qed.

Lemma test_mor : forall (dim : nat) (c1 c2 : cliffordT_ucom dim), c1 ≡ c2 -> c2 ; c1 ≡ c1 ; c1.
Proof. intros. rewrite H0. reflexivity. Qed.

(** * Examples from Gottesman Paper *)

(* Example 1: SWAP *)

Lemma SWAP_X1 : h_eval (@SWAP 2 0 1) [XX,II] = [II,XX].
Proof. reflexivity. Qed.

Lemma SWAP_basis : forall (h1 h2 : htype),
 h1 <> ⊤ -> h2 <> ⊤ ->
 h_eval (@SWAP 2 0 1) [h1,h2] = [h2,h1].
Proof. intros [] []; subst; easy. Qed.

(* Could reduce to a two case proof and add a proof that this is
   sufficient to reason about all cases.  *)

(* Example 2 *)

Definition had_cnot : cliffordT_ucom 2 := 
  H 0; H 1; CNOT 0 1; H 0; H 1.

Lemma had_cnot_notc : forall (h1 h2 : htype),
  h_eval had_cnot [h1,h2] = h_eval (@CNOT 2 1 0) [h1,h2].   
Proof. intros [] []; reflexivity. Qed.

(* TODO: Want a general notion of equality between programs. *)

(* Example 3 *)

Definition hitite_code : cliffordT_ucom 2 := 
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

Definition cnot_notc : cliffordT_ucom 2 := CNOT 0 1; CNOT 1 0.

(* unlabelled case *)
Lemma cnot_notc_Z2 : h_eval cnot_notc [II,ZZ] = [ZZ,II].
Proof. reflexivity. Qed.

Lemma cnot_notc_X1 : h_eval cnot_notc [XX,II] = [II,XX].
Proof. reflexivity. Qed.

Lemma cnot_notc_Z1 : h_eval cnot_notc [ZZ,II] = [ZZ,ZZ].
Proof. reflexivity. Qed.

(* Example 5 : Bell *)

Definition bell : cliffordT_ucom 2 := H 0; CNOT 0 1.

Lemma bell_Z1 : h_eval bell [ZZ,II] = [XX,XX].
Proof. reflexivity. Qed.

Lemma bell_Z2 : h_eval bell [II,ZZ] = [ZZ,ZZ].
Proof. reflexivity. Qed.

(* Example 6 *)

(* Can we represent this as a program? *)

(* Example 7 *)

Definition ec_code : cliffordT_ucom 4 := 
  H 3; CNOT 0 2; CNOT 1 2; CNOT 3 0; CNOT 3 1; CNOT 3 2.

(* What to prove? *)

(* Example 8 *)

(* Example 9 *)

(* Now with measurement! *)

(* Example 10: Teleportation *)

(* Measurement-free teleportation with bell initialization *)

Definition bell' : cliffordT_ucom 3 := H 1; CNOT 1 2.

Definition alice : cliffordT_ucom 3 := CNOT 0 1; H 0.

Definition bob : cliffordT_ucom 3 := CNOT 1 2; CZ 0 2.

Definition teleport : cliffordT_ucom 3 := bell'; alice; bob.

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

(** * Own examples *)

(** * Proofs about derived unitaries *)

Lemma X_X1 : @h_eval 1 (X 0) [XX] = [XX].
Proof. reflexivity. Qed.
Lemma X_Z1 : @h_eval 1 (X 0) [ZZ] = [ZZ].
Proof. reflexivity. Qed.
Lemma Y_X1 : @h_eval 1 (Y 0) [XX] = [XX].
Proof. reflexivity. Qed.
Lemma Y_Z1 : @h_eval 1 (Y 0) [ZZ] = [ZZ].
Proof. reflexivity. Qed.
Lemma Z_X1 : @h_eval 1 (Z 0) [XX] = [XX].
Proof. reflexivity. Qed.
Lemma Z_Z1 : @h_eval 1 (Z 0) [ZZ] = [ZZ].
Proof. reflexivity. Qed.

Lemma CZ_X1 : @h_eval 2 (CZ 0 1) [XX,II] = [XX,ZZ].
Proof. reflexivity. Qed.
Lemma CZ_Z1 : @h_eval 2 (CZ 0 1) [ZZ,II] = [ZZ,II].
Proof. reflexivity. Qed.
Lemma CZ_X2 : @h_eval 2 (CZ 0 1) [II,XX] = [ZZ,XX].
Proof. reflexivity. Qed.
Lemma CZ_Z2 : @h_eval 2 (CZ 0 1) [II,ZZ] = [II,ZZ].
Proof. reflexivity. Qed.
  
(* Toffoli Decomposition *)

Definition TOFFOLI {dim} (a b c : nat) : cliffordT_ucom dim :=
  H c; 
  CNOT b c; TDAG c; 
  CNOT a c; T c; 
  CNOT b c; TDAG c; 
  CNOT a c; T b; T c; H c;
  CNOT a b; T a; TDAG b; 
  CNOT a b.

Lemma TOFFOLI_Z1 : @h_eval 3 (TOFFOLI 0 1 2) [ZZ,II,II] = [ZZ,II,II].
Proof. compute. reflexivity. Qed.

Lemma TOFFOLI_Z2 : @h_eval 3 (TOFFOLI 0 1 2) [II,ZZ,II] = [II,ZZ,II].
Proof. compute. reflexivity. Qed.

Lemma TOFFOLI_X3 : @h_eval 3 (TOFFOLI 0 1 2) [II,II,XX] = [II,II,XX].
Proof. compute. reflexivity. Qed.

Lemma TOFFOLI_ZZX : @h_eval 3 (TOFFOLI 0 1 2) [ZZ,ZZ,XX] = [ZZ,ZZ,XX].
Proof. compute. reflexivity. Qed.

Lemma TOFFOLI_X1 : @h_eval 3 (TOFFOLI 0 1 2) [XX,II,II] = [⊤,⊤,⊤].
Proof. compute. reflexivity. Qed.

Lemma TOFFOLI_X2 : @h_eval 3 (TOFFOLI 0 1 2) [II,XX,II] = [⊤,⊤,⊤].
Proof. compute. reflexivity. Qed.

Lemma TOFFOLI_Z3 : @h_eval 3 (TOFFOLI 0 1 2) [II,II,ZZ] = [⊤,⊤,⊤].
Proof. compute. reflexivity. Qed.

(*

Inductive CliffordT : nat -> Set := 
  | Clif : forall {n}, Clifford n -> CliffordT n 
  | U_T  : CliffordT 1.                

Coercion Clif : Clifford >-> CliffordT. 

Definition cliffordT_ucom := ucom CliffordT.

Fixpoint CliffordtoT {dim} (c : clifford_ucom dim) : cliffordT_ucom dim :=
  match c with
  | c1 ; c2 => CliffordtoT c1 ; CliffordtoT c2
  | uapp1 u n => uapp1 (Clif u) n
  | uapp2 u m n => uapp2 (Clif u) m n
  | uapp3 u m n o => uapp3 (Clif u) m n o
  end.

Coercion CliffordtoT : clifford_ucom >-> cliffordT_ucom.

Definition T {dim} n : cliffordT_ucom dim := uapp1 U_T n.
Definition TDAG {dim} n : cliffordT_ucom dim := Z n; (S n : cliffordT_ucom dim); T n. 

*)

  (*
(* Adding a new (non-Clifford) gate and axiomatizing its 
   effect on Z: *)
Parameter U_T : Clifford 1.
Axiom TZ : apply1 U_T ZZ = ZZ.
Definition T {dim} n : clifford_ucom dim := uapp1 U_T n.
Definition TDAG {dim} n : clifford_ucom dim := Z n; S n; T n. 


Definition TOFFOLI {dim} (a b c : nat) : clifford_ucom dim :=
  H c; 
  CNOT b c; TDAG c; 
  CNOT a c; T c; 
  CNOT b c; TDAG c; 
  CNOT a c; T b; T c; H c;
  CNOT a b; T a; TDAG b; 
  CNOT a b.

Lemma TOFFOLI_Z1 : @h_eval 3 (TOFFOLI 0 1 2) [ZZ,II,II] = [ZZ,II,II].
Proof. unfold h_eval, TOFFOLI.
       cbn.
  compute. simpl. reflexivity. Qed.

   *)
  

(* GHZ state *)

Fixpoint GHZ (dim n : nat) : clifford_ucom dim :=
  match n with
  | 0        => I 0
  | 1        => H 0
  | s (s n'' as n') => GHZ dim n' ; CNOT n'' n'      
  end.

Lemma GHZ3_XII : h_eval (GHZ 3 3) [ZZ, II, II] = [XX, XX, XX].
Proof. reflexivity. Qed.

(* interesting *)
Lemma GHZ3_IZI : h_eval (GHZ 3 3) [II, ZZ, II] = [ZZ, ZZ, II]. 
Proof. simpl. reflexivity. Qed.

Lemma GHZ3_IIZ : h_eval (GHZ 3 3) [II, II, ZZ] = [II, ZZ, ZZ].
Proof. simpl. reflexivity. Qed.

Lemma GHZ_Z : forall n, h_eval (GHZ (1+n) (1+n)) (ZZ :: all_I_state n) = all_X_state (1+n).
Proof.
  induction n.
  - reflexivity.
  - simpl.
    
