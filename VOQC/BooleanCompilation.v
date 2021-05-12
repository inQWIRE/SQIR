Require Import UnitaryOps.
Open Scope ucom.

(*********************************)
(** Boolean Circuit Compilation **)
(*********************************)
(* This file defines a 'compile' function that converts an arbitrary
   boolean expression into a reversible circuit that (provably) uncomputes 
   its ancillae. We use eager ancilla cleanup, which requires fewer qubits,
   but more gates, than the lazy approach. Because SQIR does not allow
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
                  CCX j (j+1) i;
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
Local Opaque CCX.
Lemma compile'_correct : forall dim (b : bexp) (f : nat -> bool) (i j : nat),
  bexp_well_typed i b -> 
  (i < j)%nat ->
  (j + (num_ancillae b) < dim + 1)%nat ->
  (forall k, (k > i)%nat -> f k = false) ->
  (uc_eval (@compile' dim b i j)) × (f_to_vec dim f) 
    = f_to_vec dim (update f i ((f i) ⊕ (interpret_bexp b f))).
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
    rewrite f_to_vec_CCX; try lia.
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
  (@uc_eval (b_dim b) (compile b)) × f_to_vec (b_dim b) in_s
    = f_to_vec (b_dim b) out_s.
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
