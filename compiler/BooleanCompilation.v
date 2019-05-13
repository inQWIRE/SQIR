Require Import QWIRE.Dirac.
Require Import UnitarySem.
Open Scope ucom.

(*********************************)
(** Boolean Circuit Compilation **)
(*********************************)
(* This file defines a 'compile' function that converts an arbitrary
   boolean expression into a reversible circuit that (provably) uncomputes 
   its ancillae. We use eager ancilla cleanup, which requires fewer qubits,
   but more gates, than the lazy approach. Because SQIRE does not allow
   initializing / discarding qubits, we precompute the number of ancillae
   needed and include them in the global register.
 
   The boolean expression language and compilation strategy are modelled 
   after the Oracles.v file in (Re)QWIRE, which is based on the ReVerC 
   reversible circuit compiler. 

   We prove that compilation is correct by showing that the output circuit
   has the expected behavior on any basis state. The proof requires some
   new formalisms for describing classical states (see 'f_to_vec'). *)

(** (nat -> bool) functions **)
(* (nat -> bool) functions are used to express the evaluation context for
   boolean expressions, and to describe classical states. 

   TODO: These lemmas are fairly generic - are they defined somewhere in
   Coq already? *)

(* Update the value at one index of a boolean function. *)
Definition update (f : nat -> bool) (i : nat) (b : bool) :=
  fun i' => if i' =? i then b else f i'.

Lemma update_index_eq : forall f i b, (update f i b) i = b.
Proof.
  intros. 
  unfold update.
  replace (i =? i) with true by (symmetry; apply Nat.eqb_eq; reflexivity).
  reflexivity.
Qed.

Lemma update_index_neq : forall f i j b, i <> j -> (update f i b) j = f j.
Proof.
  intros. 
  unfold update.
  bdestruct (j =? i); try easy. 
  contradict H0; lia.
Qed.

Lemma update_same : forall f i b,
  b = f i -> update f i b = f.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold update.
  bdestruct (x =? i); subst; reflexivity.
Qed.

Lemma update_twice_eq : forall f i b b',
  update (update f i b) i b' = update f i b'.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold update.
  bdestruct (x =? i); subst; reflexivity.
Qed.  

Lemma update_twice_neq : forall f i j b b',
  i <> j -> update (update f i b) j b' = update (update f j b') i b.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold update.
  bdestruct (x =? i); bdestruct (x =? j); subst; 
  try (contradict H; reflexivity); reflexivity.
Qed.

(** Boolean expressions **)

Inductive bexp := 
| b_t   : bexp
| b_f   : bexp
| b_var : nat -> bexp
| b_and : bexp -> bexp -> bexp 
| b_xor : bexp -> bexp -> bexp.

Fixpoint interpret_bexp (b : bexp) (f : nat -> bool) : bool :=
  match b with
  | b_t         => true 
  | b_f         => false 
  | b_var v     => f v 
  | b_and b1 b2 => (interpret_bexp b1 f) && (interpret_bexp b2 f)
  | b_xor b1 b2 => (interpret_bexp b1 f) ⊕ (interpret_bexp b2 f)
  end.  

Inductive bexp_well_typed : nat -> bexp -> Prop :=
  | WT_b_t : forall n, bexp_well_typed n b_t
  | WT_b_f : forall n, bexp_well_typed n b_f
  | WT_b_var : forall n q, (q < n)%nat -> bexp_well_typed n (b_var q)
  | WT_b_and : forall n b1 b2, bexp_well_typed n b1 -> bexp_well_typed n b2 -> bexp_well_typed n (b_and b1 b2)
  | WT_b_xor : forall n b1 b2, bexp_well_typed n b1 -> bexp_well_typed n b2 -> bexp_well_typed n (b_xor b1 b2).

Lemma well_typed_increase_dim : forall b n n',
  (n <= n')%nat ->
  bexp_well_typed n b ->
  bexp_well_typed n' b.
Proof.
  intros.
  induction H0; try constructor; try lia;
  try apply IHbexp_well_typed1; 
  try apply IHbexp_well_typed2; 
  assumption.
Qed.

Lemma interpret_bexp_f : forall i b f f',
  bexp_well_typed i b ->
  (forall k, (k < i)%nat -> f k = f' k) ->
  interpret_bexp b f = interpret_bexp b f'.
Proof.
  intros.
  induction H; simpl; try reflexivity.
  - apply H0. assumption.
  - rewrite IHbexp_well_typed1; try assumption.
    rewrite IHbexp_well_typed2; try assumption.
    reflexivity.
  - rewrite IHbexp_well_typed1; try assumption.
    rewrite IHbexp_well_typed2; try assumption.
    reflexivity.
Qed.

Lemma interpret_bexp_update : forall b f i j r,
  (i <= j)%nat ->
  bexp_well_typed i b ->
  interpret_bexp b f = interpret_bexp b (update f j r).
Proof.
  intros.
  apply interpret_bexp_f with (i:=i); try assumption.
  intros.
  rewrite update_index_neq; try lia.
  reflexivity.
Qed.

(** Toffoli gate **)
(* The Toffoli gate is useful for defining oracles. It is not built in to our
   gate set, so we define it in terms of built-in gates here. *)

(* From https://en.wikipedia.org/wiki/Toffoli_gate *)
Definition TDAG a := uapp (U_R (- PI / 4)) [a].
Definition TOFFOLI (a b c : nat) : ucom :=
  H c; 
  CNOT b c; TDAG c; 
  CNOT a c; T c; 
  CNOT b c; TDAG c; 
  CNOT a c; T b; T c; H c;
  CNOT a b; T a; TDAG b; 
  CNOT a b.

(** Utilities for constructing and manipulating classical states **)

(* Move coercion to Dirac file in QWIRE library? *)
Definition bool_to_nat (b : bool) : nat := if b then 1 else 0.
Coercion bool_to_nat : bool >-> nat.

(* Convert a boolean function to a vector; examples: 
     f_to_vec 0 3 f --> ((I 1 ⊗ ∣ f 0 ⟩) ⊗ ∣ f 1 ⟩) ⊗ | f 2 ⟩ 
     f_to_vec 2 2 f -->  (I 1 ⊗ ∣ f 2 ⟩) ⊗ ∣ f 3 ⟩ 
*)
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

Lemma f_to_vec_update : forall (base n : nat) (f : nat -> bool) (i : nat) (b : bool),
  (i < base \/ base + n <= i)%nat ->
  f_to_vec base n f = f_to_vec base n (update f i b).
Proof.
  intros.
  destruct H.
  - induction n; simpl; try reflexivity.
    unfold update.
    bdestruct (base + n =? i).
    contradict H0. lia.
    rewrite IHn.
    reflexivity.
  - induction n; simpl; try reflexivity.
    unfold update.
    bdestruct (base + n =? i).
    contradict H0. lia.
    rewrite IHn.
    reflexivity. lia.
Qed.

Lemma f_to_vec_split : forall (base n i : nat) (f : nat -> bool),
  (i < n)%nat ->
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
      restore_dims_strong; repeat rewrite kron_assoc. 
      reflexivity.
Qed.

Lemma f_to_vec_X : forall (n i : nat) (f : nat -> bool),
  (i < n)%nat ->
  (uc_eval n (X i)) × (f_to_vec 0 n f) 
      = f_to_vec 0 n (update f i (¬ (f i))).
Proof.
  intros.
  simpl; unfold uc_eval, ueval1, pad. 
  replace (i + 1 <=? n) with true by (symmetry; apply Nat.leb_le; lia).
  rewrite (f_to_vec_split 0 n i f H).
  restore_dims_strong; Msimpl. 
  repeat rewrite Mmult_1_l; try apply f_to_vec_WF.
  rewrite (f_to_vec_split 0 n i _ H).
  simpl.
  repeat rewrite <- (f_to_vec_update _ _ _ i (¬ (f i))).
  2: { left. lia. }
  2: { right. lia. }
  destruct (f i); try rewrite update_index_eq; simpl;
  autorewrite with ket_db;
  reflexivity.
Qed.

(* TODO: Move these to the Dirac file in QWIRE *)
Lemma ket00_0 : ∣0⟩⟨0∣ × ∣ 0 ⟩ = ∣ 0 ⟩. 
Proof. solve_matrix. Qed.
Lemma ket00_1 : ∣0⟩⟨0∣ × ∣ 1 ⟩ = @Zero 2 1. 
Proof. solve_matrix. Qed.
Lemma ket11_0 : ∣1⟩⟨1∣ × ∣ 0 ⟩ = @Zero 2 1. 
Proof. solve_matrix. Qed.
Lemma ket11_1 : ∣1⟩⟨1∣ × ∣ 1 ⟩ = ∣ 1 ⟩. 
Proof. solve_matrix. Qed.

(* We can prove more general lemmas about CNOT and TOFFOLI (placing no 
   restrictions on i, j), but the following are sufficient for our 
   purposes here. We can revisit the design if we choose a different 
   representation of tensor products. *)
Lemma f_to_vec_CNOT : forall (n i j : nat) (f : nat -> bool),
  (i < j)%nat ->
  (j < n)%nat ->
  (uc_eval n (CNOT i j)) × (f_to_vec 0 n f) 
      = f_to_vec 0 n (update f j (f j ⊕ f i)).
Proof.
  intros.
  simpl; unfold uc_eval, ueval_cnot, pad.
  replace (i <? j) with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (i + (1 + (j - i - 1) + 1) <=? n) with true by (symmetry; apply Nat.leb_le; lia).
  replace (2 ^ (j - i))%nat with (2 ^ (j - i - 1) * 2)%nat by unify_pows_two.
  rewrite <- id_kron.
  repeat rewrite (f_to_vec_split 0 n j _ H0).
  repeat rewrite (f_to_vec_split 0 j i _ H).
  repeat rewrite <- (f_to_vec_update _ _ _ j (f j ⊕ f i));
  try (left; lia); try (right; lia).
  rewrite update_index_eq, update_index_neq; try lia.
  replace (j - 1 - i)%nat with (j - i - 1)%nat by lia.
  replace (n - 1 - j)%nat with (n - (1 + (j - i - 1) + 1) - i)%nat by lia.
  rewrite <- kron_assoc.
  rewrite (kron_assoc (f_to_vec 0 i f) _ _ ).
  restore_dims_strong.
  rewrite (kron_assoc _ _ ( ∣ f (0 + j)%nat ⟩)).
  restore_dims_strong; Msimpl.
  rewrite Mmult_plus_distr_r.
  Msimpl. 
  simpl; destruct (f i); destruct (f j); simpl;
  repeat rewrite Mmult_1_l; try apply f_to_vec_WF; try auto with wf_db;
  try rewrite ket00_0; try rewrite ket00_1;
  try rewrite ket11_0; try rewrite ket11_1;
  autorewrite with ket_db; try auto with wf_db; try apply f_to_vec_WF;
  repeat rewrite kron_0_l;
  rewrite kron_0_r;
  rewrite kron_0_l;
  try rewrite Mplus_0_r;
  try rewrite Mplus_0_l;
  restore_dims_strong;
  repeat rewrite kron_assoc;
  restore_dims_strong;
  reflexivity.
Qed.    

Lemma f_to_vec_TOFF : forall (n i j : nat) (f : nat -> bool),
  (i < j)%nat ->
  (j + 1 < n)%nat ->
  (uc_eval n (TOFFOLI j (j+1) i)) × (f_to_vec 0 n f) 
      = f_to_vec 0 n (update f i (f i ⊕ (f j && f (j+1)%nat))).
Proof. 
  intros.
  simpl; unfold uc_eval, ueval1, ueval_cnot, pad.
  (* Simplify LHS (we can eliminate all the conditionals because of 
     restrictions on i and j) *)
  replace (j <? j + 1) with true;
  try replace (j + (1 + (j + 1 - j - 1) + 1) <=? n) with true;
  try replace (j + 1 + 1 <=? n) with true;
  try replace (j + 1 <=? n) with true;
  try replace (i + 1 <=? n) with true;
  try replace (i <? j) with true;
  try replace (i + (1 + (j - i - 1) + 1) <=? n) with true;
  try replace (i <? j + 1) with true;
  try replace (i + (1 + (j + 1 - i - 1) + 1) <=? n) with true;
  try (symmetry; apply Nat.ltb_lt; lia);
  try (symmetry; apply Nat.leb_le; lia).
  bdestruct (j <? i). contradict H1; lia.
  bdestruct (j + 1 <? i). contradict H2; lia.
  (* Rewrite f_to_vec terms *)
  repeat rewrite (f_to_vec_split 0 n (j+1) _ H0).
  repeat rewrite (f_to_vec_split 0 (j+1) j); try lia.
  repeat rewrite (f_to_vec_split 0 j i _ H).
  replace (0 + i)%nat with i by easy. 
  rewrite update_index_eq.
  repeat rewrite update_index_neq; try lia.
  repeat rewrite <- f_to_vec_update;
    try (left; lia); try (right; lia).
  
  (* From this point on, all that's left is algebra... *)
  repeat rewrite Mmult_assoc.
  
Admitted.

Opaque TOFFOLI.

(** Compilation of boolean expressions to oracles **)

(* How many input variables does this expression use? *)
Fixpoint max_var b v :=
  match b with 
  | b_var v' => max v v'
  | b_and b1 b2 => max (max_var b1 v) (max_var b2 v)
  | b_xor b1 b2 => max (max_var b1 v) (max_var b2 v)
  | _ => v
  end.

Fixpoint no_vars b :=
  match b with
  | b_var _ => false
  | b_and b1 b2 => no_vars b1 && no_vars b2
  | b_xor b1 b2 => no_vars b1 && no_vars b2
  | _ => true
  end.

Definition num_inputs b : nat := if (no_vars b) then 0 else (max_var b 0) + 1.

Lemma num_inputs_well_typed : forall b,
  bexp_well_typed (num_inputs b) b.
Proof.
  induction b.
  - constructor.
  - constructor.
  - unfold num_inputs; simpl.
    constructor. lia.
  - constructor.
    + apply well_typed_increase_dim with (n:=num_inputs b1); try assumption.
      unfold num_inputs.
      simpl; destruct (no_vars b1); destruct (no_vars b2); simpl; lia.
    + apply well_typed_increase_dim with (n:=num_inputs b2); try assumption.
      unfold num_inputs.
      simpl; destruct (no_vars b1); destruct (no_vars b2); simpl; lia.
  - constructor.
    + apply well_typed_increase_dim with (n:=num_inputs b1); try assumption.
      unfold num_inputs.
      simpl; destruct (no_vars b1); destruct (no_vars b2); simpl; lia.
    + apply well_typed_increase_dim with (n:=num_inputs b2); try assumption.
      unfold num_inputs.
      simpl; destruct (no_vars b1); destruct (no_vars b2); simpl; lia.
Qed.

(* How many ancillary qubits are needed to represent this expression? *)
Fixpoint num_ancillae b : nat :=
  match b with
  | b_and b1 b2 => 2 + (max (num_ancillae b1) (num_ancillae b2))
  | b_xor b1 b2 => max (num_ancillae b1) (num_ancillae b2) 
  | _ => 0
  end.

(* Total number of qubits required. *)
Definition b_dim (b : bexp) : nat := (num_inputs b) + 1 + (num_ancillae b).

(* Translate a boolean expression into a reversible circuit. The produced 
   program should only modify the qubit at index i.
   - i is the index of the result
   - j is the index of the next available ancilla. *)
Fixpoint compile' (b : bexp) (i j : nat) : ucom :=
  match b with
  | b_t         => X i
  | b_f         => uskip
  | b_var v     => CNOT v i
  | b_and b1 b2 => compile' b1 j (j+2); 
                  compile' b2 (j+1) (j+2);
                  TOFFOLI j (j+1) i;
                  compile' b2 (j+1) (j+2); 
                  compile' b1 j (j+2)
  | b_xor b1 b2 => compile' b1 i j; 
                  compile' b2 i j
  end.

Definition compile b := compile' b (num_inputs b) ((num_inputs b) + 1).

(* Correctness of compile':
   1. The value at index i is xor-ed with the desired boolean expression.
   2. All other values remain unchanged.

   Notes:
   * The well-typedness constraint is used in the b_var case.
   * 'i < j' is used when applying f_to_vec_X, f_to_vec_CNOT, and f_to_vec_TOFF.
   * 'j + (num_ancillae b) < n + 1' and 'forall k ...' are used in the b_and 
     case -- note that this is the only case where the ancilla matter.
*)
Lemma compile'_correct : forall (b : bexp) (f : nat -> bool) (i j n : nat),
  bexp_well_typed i b -> 
  (i < j)%nat ->
  (j + (num_ancillae b) < n + 1)%nat ->
  (forall k, (k > i)%nat -> f k = false) ->
  (uc_eval n (compile' b i j)) × (f_to_vec 0 n f) 
    = f_to_vec 0 n (update f i ((f i) ⊕ (interpret_bexp b f))).
Proof.
  intros.
  generalize dependent f.
  generalize dependent j.
  generalize dependent i. 
  induction b; intros.
  - (* b_t *)
    unfold compile'. 
    rewrite f_to_vec_X; try lia.
    destruct (f i); simpl; reflexivity.
  - (* b_f *)
    simpl. 
    rewrite Mmult_1_l; try apply f_to_vec_WF.
    rewrite xorb_false_r.
    rewrite update_same; reflexivity.
  - (* b_var v *)
    inversion H; subst.
    unfold compile'.
    rewrite f_to_vec_CNOT; try lia.
    reflexivity.
  - (* b_and b1 b2 *) 
    inversion H; subst; clear H.
    assert (bexp_well_typed j b1).
    { apply (well_typed_increase_dim b1 i j); try assumption; lia. }
    assert (bexp_well_typed (j+1) b2).
    { apply (well_typed_increase_dim b2 i (j+1)); try assumption; lia. }
    assert (j < j + 2)%nat by lia.
    assert (j + 1 < j + 2)%nat by lia.
    simpl in H1.
    assert ((j + 2) + num_ancillae b1 < n + 1)%nat by lia.
    assert ((j + 2) + num_ancillae b2 < n + 1)%nat by lia.
    specialize (IHb1 j H (j+2)%nat H4 H8).
    specialize (IHb2 (j+1)%nat H3 (j+2)%nat H5 H9).
    clear H H3 H4 H5 H8 H9.
    simpl.
    repeat rewrite Mmult_assoc.
    rewrite IHb1.
    2: { intros. apply H2. lia. }
    rewrite IHb2.
    2: { intros. rewrite update_index_neq; try apply H2; lia. }
    rewrite update_index_neq; try lia.
    rewrite <- interpret_bexp_update with (i:=i);
      try assumption; try lia.
    rewrite f_to_vec_TOFF; try lia.
    rewrite update_index_eq. 
    do 3 (rewrite update_index_neq; try lia).
    rewrite update_index_eq.
    rewrite IHb2.
    2: { intros. repeat rewrite update_index_neq; try apply H2; lia. }
    rewrite update_twice_neq with (i:=(j+1)%nat); try lia.
    rewrite update_twice_eq with (i:=(j+1)%nat).
    rewrite update_index_eq.
    repeat rewrite <- interpret_bexp_update with (i:=i);
      try assumption; try lia.
    rewrite xorb_assoc.
    rewrite xorb_nilpotent.
    rewrite xorb_false_r.
    rewrite IHb1.
    2: { intros. 
         rewrite update_twice_neq; try lia.
         rewrite update_index_neq; try lia.
         rewrite update_twice_neq; try lia.
         rewrite update_index_neq; try lia.
         rewrite update_same; try reflexivity.
         apply H2; lia. }
    rewrite update_twice_neq with (i:=j); try lia.
    rewrite update_twice_neq with (i:=j); try lia.
    rewrite update_twice_eq with (i:=j).
    rewrite update_index_eq.
    repeat rewrite <- interpret_bexp_update with (i:=i);
      try assumption; try lia.
    rewrite xorb_assoc.
    rewrite xorb_nilpotent.
    rewrite xorb_false_r.
    repeat rewrite update_twice_neq with (i:=i); try lia.
    rewrite update_same with (i:=(j+1)%nat); try reflexivity.
    rewrite update_same with (i:=j); try reflexivity.
    rewrite H2 with (k:=j); try lia.
    rewrite H2 with (k:=(j+1)%nat); try lia.
    repeat rewrite xorb_false_l.
    reflexivity.
  - (* b_xor b1 b2 *)
    inversion H; subst; clear H.
    simpl.
    rewrite Mmult_assoc.
    simpl in H1.
    rewrite IHb1; try assumption; try lia.
    rewrite IHb2; try assumption; try lia.
    2: { intros. rewrite update_index_neq; try apply H2; lia. }
    rewrite update_twice_eq.
    rewrite update_index_eq.
    rewrite <- interpret_bexp_update with (i:=i);
      try assumption; try lia.
    rewrite xorb_assoc.
    reflexivity.
Qed.

Lemma compile_correct : forall (b : bexp) (f : nat -> bool) (r : bool), 
  let in_s := fun i => if i <? (num_inputs b) then f i else false in
  let out_s := update in_s (num_inputs b) (interpret_bexp b f) in
  (uc_eval (b_dim b) (compile b)) × f_to_vec 0 (b_dim b) in_s
    = f_to_vec 0 (b_dim b) out_s.
Proof.
  intros.
  unfold compile, out_s.
  rewrite <- (xorb_false_l (interpret_bexp b f)).
  replace false with (in_s (num_inputs b)).
  2: { unfold in_s. bdestruct (num_inputs b <? num_inputs b). 
       contradict H. lia. reflexivity. }
  rewrite interpret_bexp_f with (i:=num_inputs b) (f':=in_s);
    try apply compile'_correct;
    try apply num_inputs_well_typed;
    unfold b_dim; try lia.
  intros k Hk. unfold in_s. bdestruct (k <? num_inputs b);
    try (contradict H; lia); reflexivity.
  intros k Hk. unfold in_s. bdestruct (k <? num_inputs b);
    try (contradict H; lia); reflexivity.
Qed.

(** Examples **)
(* Small examples taken from (Re)QWIRE's Arithmetic.v file.
   
   TODO: Port over n-qubit adder examples. (I don't think this will cause
   any problems, but precomputing the number of ancillae might get a bit
   weird.) *)

Infix "⊻" := b_xor (at level 40).
Infix "∧" := b_and (at level 40).
Coercion b_var : nat >-> bexp.

Local Close Scope R_scope.

(*
Input : var 1 : y
        var 2 : x
        var 3 : cin
Output : cout = cin(x ⊕ y) ⊕ xy
*)
Definition adder_cout_bexp : bexp := (3 ∧ (2 ⊻ 1)) ⊻ (2 ∧ 1).
Eval cbv in (compile adder_cout_bexp).

(*
Input : var 0 : y
        var 1 : x
        var 2 : cin
Output : sum = cin ⊕ (x ⊕ y)
 *)
Definition adder_sum_bexp : bexp := 2 ⊻ (1 ⊻ 0).
Eval cbv in (compile adder_sum_bexp).

(*
Input : var 0 : x
        var 1 : y
Output : xor = x ⊕ y
*)
Definition xor_bexp : bexp := 0 ⊻ 1.
Eval cbv in (compile xor_bexp).

(*
Input : var 0 : x
Output : x' = x
*)
Definition id_bexp : bexp := 0.
Eval cbv in (compile id_bexp).