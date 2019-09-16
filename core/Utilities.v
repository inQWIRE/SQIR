Require Export UnitarySem.
Require Import Dirac.

Local Open Scope ucom_scope.
Local Close Scope C_scope.
Local Close Scope R_scope.

(* Misc. SQIRE utilies including:
   - support for composing SQIRE programs
   - suport for reasoning about classical states
*)

(** Composing SQIRE programs. **)

(* TODO: extend the defs below to non-unitary circuits *)

(* General qubit re-labeling function. *)

Fixpoint map_qubits {U dim} (f : nat -> nat) (c : ucom U dim) : ucom U dim :=
  match c with
  | c1; c2 => map_qubits f c1; map_qubits f c2
  | uapp1 u n => uapp1 u (f n)
  | uapp2 u m n => uapp2 u (f m) (f n)
  | uapp3 u m n p => uapp3 u (f m) (f n) (f p)
  end.
  
(* Lemmas about padding *)

(* TODO: Is there a nicer way to write this? *)
Fixpoint cast {U dim} (c : ucom U dim) dim' : ucom U dim' := 
  match c with 
  | c1; c2 => cast c1 dim' ; cast c2 dim'
  | uapp1 u n => uapp1 u n
  | uapp2 u m n => uapp2 u m n
  | uapp3 u m n p => uapp3 u m n p
  end.                                                     

Lemma typed_cast : forall {U n} (c : ucom U n) (n' : nat),
  uc_well_typed c -> n <= n' -> uc_well_typed (cast c n').
Proof.
  intros.
  induction H; simpl; constructor; try lia.
  apply IHuc_well_typed1. apply IHuc_well_typed2.
Qed.
                                                     
Lemma pad_dims_r : forall {dim} (c : base_ucom dim) (k : nat),
  uc_well_typed c ->
  (uc_eval c) ⊗ I (2^k) = uc_eval (cast c (dim + k)).  
Proof.
  intros dim c k H.
  induction c; try dependent destruction u.
  - inversion H; subst.
    simpl. rewrite <- IHc1, <- IHc2; trivial.
    restore_dims; Msimpl; reflexivity.
  - simpl. inversion H; subst.
    autorewrite with eval_db.
    gridify; reflexivity.
  - simpl. inversion H; subst.
    autorewrite with eval_db.
    gridify; reflexivity.
Qed.

Lemma pad_dims_l : forall {dim} (c : base_ucom dim) (k : nat),
  I (2^k) ⊗ (uc_eval c) = uc_eval (cast (map_qubits (fun q => k + q) c) (k + dim)).  
Proof.
  intros.
  induction c; try dependent destruction u; simpl.
  - rewrite <- IHc1, <- IHc2.
    restore_dims; Msimpl. reflexivity.
  - autorewrite with eval_db.
    gridify; reflexivity.
  - autorewrite with eval_db.
    gridify; reflexivity.
Qed.

(* Combine two programs in parallel. *)

Definition inPar {U dim1 dim2} (c1 : ucom U dim1) (c2 : ucom U dim2) :=
  (cast c1 (dim1 + dim2)); (cast (map_qubits (fun q => dim1 + q) c2) (dim1 + dim2)).

Lemma inPar_WT : forall {U dim1 dim2} (c1 : ucom U dim1) (c2 : ucom U dim2),
  uc_well_typed c1 -> uc_well_typed c2 -> uc_well_typed (inPar c1 c2).
Proof.
  intros U dim1 dim2 c1 c2 WTc1 WTc2.
  unfold inPar.
  apply WT_seq.
  - clear - WTc1.
    induction WTc1; simpl; constructor; try lia; assumption.
  - clear - WTc2. 
    induction WTc2; simpl; constructor; try lia; assumption.
Qed.

Lemma inPar_correct : forall {dim1 dim2} (c1 : base_ucom dim1) (c2 : base_ucom dim2),
  uc_well_typed c1 -> uc_eval (inPar c1 c2) = (uc_eval c1) ⊗ (uc_eval c2).
Proof.
  intros dim1 dim2 c1 c2 WTc1.
  simpl.
  rewrite <- (pad_dims_r c1); try assumption.
  rewrite <- pad_dims_l.
  restore_dims.
  rewrite kron_mixed_product.
  Msimpl.
  reflexivity.
Qed.

(** Reasoning about classical states. **)

(* General facts about (nat -> A) functions.

   TODO #1: These lemmas are probably already defined in Coq somewhere.
   TODO #2: For efficiency, instead of using functions indexed by natural
            numbers, we should use vectors/arrays. *)

(* Update the value at one index of a boolean function. *)
Definition update {A} (f : nat -> A) (i : nat) (x : A) :=
  fun j => if j =? i then x else f j.

Lemma update_index_eq : forall {A} (f : nat -> A) i b, (update f i b) i = b.
Proof.
  intros. 
  unfold update.
  replace (i =? i) with true by (symmetry; apply Nat.eqb_eq; reflexivity).
  reflexivity.
Qed.

Lemma update_index_neq : forall {A} (f : nat -> A) i j b, i <> j -> (update f i b) j = f j.
Proof.
  intros. 
  unfold update.
  bdestruct (j =? i); try easy. 
  contradict H0; lia.
Qed.

Lemma update_same : forall {A} (f : nat -> A) i b,
  b = f i -> update f i b = f.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold update.
  bdestruct (x =? i); subst; reflexivity.
Qed.

Lemma update_twice_eq : forall {A} (f : nat -> A) i b b',
  update (update f i b) i b' = update f i b'.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold update.
  bdestruct (x =? i); subst; reflexivity.
Qed.  

Lemma update_twice_neq : forall {A} (f : nat -> A) i j b b',
  i <> j -> update (update f i b) j b' = update (update f j b') i b.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold update.
  bdestruct (x =? i); bdestruct (x =? j); subst; 
  try (contradict H; reflexivity); reflexivity.
Qed.

(* Convert a boolean function to a vector; examples: 
     f_to_vec 0 3 f --> ((I 1 ⊗ ∣ f 0 ⟩) ⊗ ∣ f 1 ⟩) ⊗ | f 2 ⟩ 
     f_to_vec 2 2 f -->  (I 1 ⊗ ∣ f 2 ⟩) ⊗ ∣ f 3 ⟩ 
*)
Definition bool_to_nat (b : bool) : nat := if b then 1 else 0.
Coercion bool_to_nat : bool >-> nat.
Fixpoint f_to_vec (base n : nat) (f : nat -> bool) : Vector (2^n) :=
  match n with 
  | 0 => I 1
  | S n' =>  (f_to_vec base n' f) ⊗ ∣ f (base + n')%nat ⟩
  end.

Lemma f_to_vec_WF : forall (base n : nat) (f : nat -> bool),
  WF_Matrix (f_to_vec base n f).
Proof.
  intros.
  induction n; simpl; try auto with wf_db.
  apply WF_kron; try lia; try assumption.
  destruct (f (base + n)%nat); auto with wf_db.
Qed.

Hint Resolve f_to_vec_WF : wf_db.

Lemma f_to_vec_update : forall (base n : nat) (f : nat -> bool) (i : nat) (b : bool),
  (i < base \/ base + n <= i)%nat ->
  f_to_vec base n (update f i b) = f_to_vec base n f.
Proof.
  intros.
  destruct H.
  - induction n; simpl; try reflexivity.
    unfold update.
    bdestruct (base + n =? i).
    contradict H0. lia.
    rewrite <- IHn.
    reflexivity.
  - induction n; simpl; try reflexivity.
    unfold update.
    bdestruct (base + n =? i).
    contradict H0. lia.
    rewrite <- IHn.
    reflexivity. lia.
Qed.

Lemma f_to_vec_split : forall (base n i : nat) (f : nat -> bool),
  i < n ->
  f_to_vec base n f = (f_to_vec base i f) ⊗ ∣ f (base + i)%nat ⟩ ⊗ (f_to_vec (base + i + 1) (n - 1 - i) f).
Proof.
  intros.
  induction n.
  - contradict H. lia.
  - bdestruct (i =? n).
    + subst.
      replace (S n - 1 - n)%nat with O by lia.
      simpl. Msimpl.
      reflexivity.
    + assert (i < n)%nat by lia.
      specialize (IHn H1).
      replace (S n - 1 - i)%nat with (S (n - 1 - i))%nat by lia.
      simpl.
      rewrite IHn.
      replace (base + i + 1 + (n - 1 - i))%nat with (base + n)%nat by lia.
      restore_dims; repeat rewrite kron_assoc. 
      reflexivity.
Qed.

Lemma f_to_vec_X : forall (n i : nat) (f : nat -> bool),
  i < n ->
  (uc_eval (X i)) × (f_to_vec 0 n f) 
      = f_to_vec 0 n (update f i (¬ (f i))).
Proof.
  intros.
  autorewrite with eval_db.
  rewrite (f_to_vec_split 0 n i f H). 
  simpl; replace (n - 1 - i) with (n - (i + 1)) by lia.
  repad. 
  Msimpl.
  rewrite (f_to_vec_split 0 (i + 1 + x) i); try lia.
  repeat rewrite (f_to_vec_update _ _ _ i (¬ (f i))).
  2: left; lia.
  2: right; lia.
  destruct (f i); simpl; rewrite update_index_eq;
  simpl; autorewrite with ket_db;
  replace (i + 1 + x - 1 - i) with x by lia;
  reflexivity.
Qed.

Lemma f_to_vec_CNOT : forall (n i j : nat) (f : nat -> bool),
  i < n ->
  j < n ->
  i <> j ->
  (uc_eval (SQIRE.CNOT i j)) × (f_to_vec 0 n f) 
      = f_to_vec 0 n (update f j (f j ⊕ f i)).
Proof.
  intros.
  autorewrite with eval_db.
  repad.
  - repeat rewrite (f_to_vec_split 0 (i + (1 + d + 1) + x) i); try lia.
    rewrite f_to_vec_update.
    2: right; lia.
    rewrite update_index_neq; try lia.
    repeat rewrite (f_to_vec_split (0 + i + 1) (i + (1 + d + 1) + x - 1 - i) d); try lia.
    repeat rewrite f_to_vec_update.
    2: left; lia.
    2: right; lia.
    simpl; rewrite update_index_eq.
    replace (i + S (d + 1) + x - 1 - i - 1 - d) with x by lia.
    distribute_plus.  
    restore_dims.
    repeat rewrite <- kron_assoc.
    destruct (f i); destruct (f (i + 1 + d)); simpl; Msimpl.
    all: repeat rewrite Mmult_assoc. 
    all: replace ((∣1⟩)† × ∣ 1 ⟩) with (I 1) by solve_matrix. 
    all: replace ((∣0⟩)† × ∣ 0 ⟩) with (I 1) by solve_matrix.  
    all: replace ((∣1⟩)† × ∣ 0 ⟩) with (@Zero 1 1) by solve_matrix.
    all: replace ((∣0⟩)† × ∣ 1 ⟩) with (@Zero 1 1) by solve_matrix.
    all: Msimpl_light; try reflexivity.
    rewrite X1_spec; reflexivity.
    rewrite X0_spec; reflexivity.
  - repeat rewrite (f_to_vec_split 0 (j + (1 + d + 1) + x0) j); try lia.
    rewrite f_to_vec_update.
    2: right; lia.
    replace (0 + j) with j by reflexivity.
    rewrite update_index_eq.
    repeat rewrite (f_to_vec_split (j + 1) (j + (1 + d + 1) + x0 - 1 - j) d); try lia.
    repeat rewrite f_to_vec_update.
    2, 3: left; lia.
    rewrite update_index_neq; try lia.
    replace (j + (1 + d + 1) + x0 - 1 - j - 1 - d) with x0 by lia.
    distribute_plus.  
    restore_dims.
    repeat rewrite <- kron_assoc.
    destruct (f j); destruct (f (j + 1 + d)); simpl; Msimpl.
    all: repeat rewrite Mmult_assoc. 
    all: replace ((∣1⟩)† × ∣ 1 ⟩) with (I 1) by solve_matrix. 
    all: replace ((∣0⟩)† × ∣ 0 ⟩) with (I 1) by solve_matrix.  
    all: replace ((∣1⟩)† × ∣ 0 ⟩) with (@Zero 1 1) by solve_matrix.
    all: replace ((∣0⟩)† × ∣ 1 ⟩) with (@Zero 1 1) by solve_matrix.
    all: Msimpl_light; try reflexivity.
    rewrite X1_spec; reflexivity.
    rewrite X0_spec; reflexivity.
Qed.    

Definition bool_to_real (b : bool) : R := if b then 1%R else 0%R.
Coercion bool_to_real : bool >-> R.

Lemma phase_shift_on_basis_state : forall (θ : R) (b : bool),
  phase_shift θ × ∣ b ⟩ = (Cexp (b * θ)) .* ∣ b ⟩.
Proof.
  intros.
  destruct b; solve_matrix; autorewrite with R_db.
  reflexivity.
  rewrite Cexp_0; reflexivity.
Qed.

Lemma f_to_vec_Rz : forall (n i : nat) (θ : R) (f : nat -> bool),
  (i < n)%nat ->
  (uc_eval (SQIRE.Rz θ i)) × (f_to_vec 0 n f) 
      = (Cexp ((f i) * θ)) .* f_to_vec 0 n f.
Proof.
  intros.
  autorewrite with eval_db.
  rewrite (f_to_vec_split 0 n i f H). 
  simpl; replace (n - 1 - i)%nat with (n - (i + 1))%nat by lia.
  repad. 
  Msimpl.
  rewrite phase_shift_on_basis_state.
  rewrite Mscale_kron_dist_r.
  rewrite Mscale_kron_dist_l.
  reflexivity.
Qed.