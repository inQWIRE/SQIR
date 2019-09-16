Require Import QWIRE.Dirac.
Require Import core.Utilities.
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
Definition TOFFOLI {dim} (a b c : nat) : base_ucom dim :=
  H c; 
  CNOT b c; TDAG c; 
  CNOT a c; T c; 
  CNOT b c; TDAG c; 
  CNOT a c; T b; T c; H c;
  CNOT a b; T a; TDAG b; 
  CNOT a b.

(* TODO: This is really just ket_db with lemmas about kron/mult distribution 
   removed. Some of the lemmas below should probably be moved to QWIRE. *)
Lemma ket00_0 : ∣0⟩⟨0∣ × ∣ 0 ⟩ = ∣ 0 ⟩. 
Proof. solve_matrix. Qed.
Lemma ket00_1 : ∣0⟩⟨0∣ × ∣ 1 ⟩ = @Zero 2 1. 
Proof. solve_matrix. Qed.
Lemma ket11_0 : ∣1⟩⟨1∣ × ∣ 0 ⟩ = @Zero 2 1. 
Proof. solve_matrix. Qed.
Lemma ket11_1 : ∣1⟩⟨1∣ × ∣ 1 ⟩ = ∣ 1 ⟩. 
Proof. solve_matrix. Qed.
Lemma phase_shift0_spec : forall θ, (phase_shift θ) × ∣ 0 ⟩ = ∣ 0 ⟩.
Proof. intros. solve_matrix. Qed.
Lemma phase_shift1_spec : forall θ, (phase_shift θ) × ∣ 1 ⟩ = (Cexp θ) .* ∣ 1 ⟩.
Proof. intros. solve_matrix. Qed.
Hint Rewrite H0_spec H1_spec Hplus_spec Hminus_spec X0_spec X1_spec : small_ket_db.
Hint Rewrite ket00_0 ket00_1 ket11_0 ket11_1 : small_ket_db.
Hint Rewrite phase_shift0_spec phase_shift1_spec : small_ket_db.
Hint Rewrite Mscale_mult_dist_r Mscale_mult_dist_l Mscale_kron_dist_r Mscale_kron_dist_l Mscale_plus_distr_r Mscale_plus_distr_l Mscale_assoc : small_ket_db.
Hint Rewrite kron_1_l kron_1_r Mmult_1_l Mmult_1_r  using (auto 10 with wf_db) : small_ket_db.
Hint Rewrite kron_0_l kron_0_r Mmult_0_l Mmult_0_r Mscale_0_r Mplus_0_l Mplus_0_r using (auto 10 with wf_db) : small_ket_db.

(* Correctness lemma for TOFF with restrictions on i, j. *)
Lemma f_to_vec_TOFF : forall (n i j : nat) (f : nat -> bool),
  (i < j)%nat ->
  (j + 1 < n)%nat ->
 (uc_eval (TOFFOLI j (j+1) i)) × (f_to_vec 0 n f) 
      = f_to_vec 0 n (update f i (f i ⊕ (f j && f (j+1)%nat))).
Proof. 
  intros.
  unfold TOFFOLI, T, TDAG.
  simpl uc_eval.
  autorewrite with eval_db. 
  repad. (* slow *)
  inversion H1; subst.
  clear.
  repeat rewrite Nat.pow_add_r.
  repeat rewrite <- id_kron.
  simpl I; Msimpl_light.

  (* 1. Get rid of unnecessary (I (2 ^ i)) and (I (2 ^ x)) terms. My theory is that
     this makes the rest of the proof faster by keeping the proof term smaller. *)
  
  (* Group (I (2 ^ i)) terms. *)
  repeat rewrite kron_assoc.
  restore_dims.
  repeat rewrite <- Nat.mul_assoc.
  repeat rewrite Nat.mul_1_l.
  repeat rewrite kron_mixed_product.
  Msimpl_light.

  (* Group (I (2 ^ x)) terms. *)
  do 2 (repeat rewrite <- kron_assoc;
        restore_dims;
        repeat rewrite Nat.mul_assoc;
        repeat rewrite kron_mixed_product;
        Msimpl_light). 

  (* Split up f_to_vec terms. *)
  rewrite 2 (f_to_vec_split 0 (i + S (x0 + 1 + 1) + x) (i + x0 + 1 + 1)); try lia.
  replace (i + S (x0 + 1 + 1) + x - 1 - (i + x0 + 1 + 1))%nat with x by lia.
  rewrite update_index_neq; try lia.
  rewrite 2 (f_to_vec_split 0 (i + x0 + 1 + 1) (i + x0 + 1)); try lia.
  replace (i + x0 + 1 + 1 - 1 - (i + x0 + 1))%nat with 0%nat by lia. 
  replace (f_to_vec (0 + (i + x0 + 1) + 1) 0 f) with (I 1) by reflexivity.
  rewrite 2 kron_1_r.
  rewrite update_index_neq; try lia.
  rewrite 2 (f_to_vec_split 0 (i + x0 + 1) i); try lia.
  replace (i + x0 + 1 - 1 - i)%nat with x0 by lia.
  rewrite update_index_eq.
  repeat rewrite f_to_vec_update.
  2, 3: left; lia.
  2: right; lia.
  repeat rewrite Nat.add_0_l.
  replace (i + x0 + 1)%nat with (i + 1 + x0)%nat by lia.
  repeat rewrite Nat.pow_add_r.
  replace (2 ^ 1)%nat with 2%nat by reflexivity.

  (* Apply f_equal2 *)
  restore_dims.
  repeat rewrite kron_assoc. 
  repeat rewrite <- Nat.mul_assoc. 
  setoid_rewrite kron_mixed_product.
  repeat rewrite <- kron_assoc. 
  repeat rewrite Nat.mul_assoc. 
  rewrite kron_mixed_product.
  Msimpl_light. 
  do 3 (rewrite (kron_assoc (f_to_vec 0 i f)); restore_dims).
  rewrite <- (kron_assoc (f_to_vec 0 i f)).
  apply f_equal2; try reflexivity.
  repeat rewrite Nat.mul_assoc. 
  apply f_equal2; try reflexivity.

  (* 2. Destruct (f i), (f (i + 1 + x0)), and (f (i + 1 + x0 + 1)) and simplify.
     Instead of expanding everything (e.g. via distribute_plus) and then reducing
     (e.g. via autorewrite with ket_db), we alternate between expanding and 
     reducing. Otherwise the proof is just too slow. *)

  repeat rewrite Mmult_assoc.
  replace (i + 1 + (x0 + (1 + 0)))%nat with (i + 1 + x0 + 1)%nat by lia.
  destruct (f i); destruct (f (i + 1 + x0)%nat); destruct (f (i + 1 + x0 + 1)%nat).
  all: simpl bool_to_nat.
  all: repeat (try rewrite kron_plus_distr_l; 
               try rewrite kron_plus_distr_r).
  all: repeat rewrite <- kron_assoc; restore_dims.
  all: repeat (do 5 try rewrite Mmult_plus_distr_l;
               do 5 try rewrite Mmult_plus_distr_r; 
               repeat rewrite kron_mixed_product;
               autorewrite with small_ket_db).
  all: auto 100 with wf_db.
  all: repeat rewrite <- Mscale_kron_dist_l.
  all: do 3 (apply f_equal2; try reflexivity).
  all: group_radicals.
  all: repeat rewrite <- Cmult_assoc;
       repeat (try rewrite Cexp_mul_neg_r; 
               try rewrite Cexp_mul_neg_l;
               autorewrite with C_db);
       repeat rewrite <- Cexp_add.
  2, 3, 4, 6, 7, 8: solve_matrix.
  all: replace (PI / 4 + PI / 4)%R with (PI / 2)%R by lra;
       replace (- (PI / 4) + - (PI / 4))%R with (- (PI / 2))%R by lra.
  all: repeat rewrite Mscale_plus_distr_r;
       repeat rewrite Mscale_assoc.
  all: repeat rewrite (Cmult_comm (Cexp (PI / 2)));
       repeat rewrite <- Cmult_assoc;
       try rewrite Cexp_mul_neg_r; 
       try rewrite Cexp_mul_neg_l.
  all: solve_matrix; autorewrite with Cexp_db; lca.
Qed.

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
Fixpoint compile' {dim} (b : bexp) (i j : nat) : base_ucom dim :=
  match b with
  | b_t         => X i
  | b_f         => SKIP
  | b_var v     => CNOT v i
  | b_and b1 b2 => compile' b1 j (j+2); 
                  compile' b2 (j+1) (j+2);
                  TOFFOLI j (j+1) i;
                  compile' b2 (j+1) (j+2); 
                  compile' b1 j (j+2)
  | b_xor b1 b2 => compile' b1 i j; 
                  compile' b2 i j
  end.

Definition compile b : base_ucom (b_dim b) := 
  compile' b (num_inputs b) ((num_inputs b) + 1).

(* Correctness of compile':
   1. The value at index i is xor-ed with the desired boolean expression.
   2. All other values remain unchanged.

   Notes:
   * The well-typedness constraint is used in the b_var case.
   * 'i < j' is used when applying f_to_vec_X, f_to_vec_CNOT, and f_to_vec_TOFF.
   * 'j + (num_ancillae b) < n + 1' and 'forall k ...' are used in the b_and 
     case -- note that this is the only case where the ancilla matter.
*)
Lemma compile'_correct : forall dim (b : bexp) (f : nat -> bool) (i j : nat),
  bexp_well_typed i b -> 
  (i < j)%nat ->
  (j + (num_ancillae b) < dim + 1)%nat ->
  (forall k, (k > i)%nat -> f k = false) ->
  (uc_eval (@compile' dim b i j)) × (f_to_vec 0 dim f) 
    = f_to_vec 0 dim (update f i ((f i) ⊕ (interpret_bexp b f))).
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
    simpl.  autorewrite with eval_db; try lia.
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
    assert ((j + 2) + num_ancillae b1 < dim + 1)%nat by lia.
    assert ((j + 2) + num_ancillae b2 < dim + 1)%nat by lia.
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
    rewrite (update_twice_neq _ (j+1)); try lia.
    rewrite update_twice_eq. 
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
    do 2 (rewrite (update_twice_neq _ j); try lia).
    rewrite update_twice_eq.
    rewrite update_index_eq.
    repeat rewrite <- interpret_bexp_update with (i:=i);
      try assumption; try lia.
    rewrite xorb_assoc.
    rewrite xorb_nilpotent.
    rewrite xorb_false_r.
    repeat rewrite (update_twice_neq _ i); try lia.
    rewrite (update_same _ (j+1)); try reflexivity.
    rewrite (update_same _ j); try reflexivity.
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
  (@uc_eval (b_dim b) (compile b)) × f_to_vec 0 (b_dim b) in_s
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
