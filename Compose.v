Require Export UnitarySem.
Require Import Tactics.

Local Open Scope ucom_scope.
Local Close Scope C_scope.
Local Close Scope R_scope.

(* Utilities for composing SQIRE programs. *)

(* TODO: extend the defs below to non-unitary circuits *)

(** General qubit re-labeling function. **)

Fixpoint map_qubits {dim} (f : nat -> nat) (c : ucom dim) : ucom dim :=
  match c with
  | uskip => uskip
  | c1; c2 => map_qubits f c1; map_qubits f c2
  | uapp1 u n => uapp1 u (f n)
  | uapp2 u m n => uapp2 u (f m) (f n)
  end.
  

(** Lemmas about padding **)

(* TODO: Is there a nicer way to write this? *)
Fixpoint cast {dim} (c : ucom dim) dim' : ucom dim' := 
  match c with 
  | uskip => uskip
  | c1; c2 => cast c1 dim' ; cast c2 dim'
  | uapp1 u n => uapp1 u n
  | uapp2 u m n => uapp2 u m n
  end.                                                     
                                                     
Lemma pad_dims_r : forall {dim} (c : ucom dim) (k : nat),
  uc_well_typed c ->
  (uc_eval c) ⊗ I (2^k) = uc_eval (cast c (dim + k)).  
Proof.
  intros dim c k H.
  induction c.
  - simpl. rewrite id_kron. unify_pows_two. reflexivity.
  - inversion H; subst.
    simpl. rewrite <- IHc1, <- IHc2; trivial.
    restore_dims_fast; Msimpl; reflexivity.
  - simpl.
    inversion H; subst.
    unfold ueval1.
    unfold pad.
    repad; try contradict_eqb_false.
    restore_dims_fast.
    repeat rewrite kron_assoc.
    rewrite id_kron.
    unify_matrices_light.
  - simpl. inversion H; subst.
    unfold ueval_cnot, pad.
    repad; try contradict_eqb_false.
    + restore_dims_fast.
      repeat rewrite kron_assoc.
      repeat rewrite id_kron.
      unify_matrices_light.
    + restore_dims_fast.
      repeat rewrite kron_assoc.
      repeat rewrite id_kron.
      unify_matrices_light.
Qed.

(*Ltac prove_wt :=
  repeat match goal with
         | |- context [ uc_well_typed ?d uskip ] => apply WT_uskip
         | |- context [ uc_well_typed ?d (useq ?c1 ?c2) ] => apply WT_seq
         | |- context [ uc_well_typed ?d (uapp ?u ?l) ] => try unfold CNOT; apply WT_app
         end.*)

Lemma typed_pad : forall {dim} (c : ucom dim) (k : nat), 
  uc_well_typed c -> uc_well_typed (cast c (dim + k)).
Proof.
  intros.
  induction c; simpl.
  - constructor.
  - inversion H; subst.
    constructor; try apply IHc1; try apply IHc2; assumption.
  - inversion H; subst.
    constructor; lia.
  - inversion H; subst.
    constructor; lia.
Qed.

Lemma pad_dims_l : forall {dim} (c : ucom dim) (k : nat),
  I (2^k) ⊗ (uc_eval c) = uc_eval (cast (map_qubits (fun q => q + k) c) (k + dim)).  
Proof.
  intros.
  induction c; simpl.
  - rewrite id_kron. unify_pows_two. reflexivity.
  - rewrite <- IHc1, <- IHc2.
    restore_dims_fast; Msimpl. reflexivity.
  - unfold ueval1.
    unfold pad.
    repad; try contradict_eqb_false.
    replace (k + (n + 1 + d) - (n + k + 1)) with d by lia.
    rewrite (plus_comm n k).
    repeat rewrite Nat.pow_add_r.
    rewrite <- id_kron.
    repeat rewrite kron_assoc.
    repeat rewrite mult_assoc.
    reflexivity.
  - unfold ueval_cnot, pad.
    bdestruct (n <? n0); bdestruct (n + k <? n0 + k); try lia; clear H0.
    + bdestruct (n + (1 + (n0 - n - 1) + 1) <=? dim); 
      bdestruct (n + k + (1 + (n0 + k - (n + k) - 1) + 1) <=? k + dim);
      try lia;
      try (remove_zero_gates; trivial).
      clear H1.
      restore_dims_strong.
      repeat rewrite <- (kron_assoc (I (2^k))). 
      rewrite id_kron; unify_pows_two.
      replace (n0 + k - (n + k)) with (n0 - n) by lia.
      replace (k + dim - (1 + (n0 - n - 1) + 1) - (n + k)) with (dim - (1 + (n0 - n - 1) + 1) - n) by lia.
      replace (k + n) with (n + k) by lia.
      unify_matrices_light.
    + bdestruct (n0 <? n); bdestruct (n0 + k <? n + k); try lia;
      try (remove_zero_gates; trivial).
      clear H H1.
      bdestruct (n0 + (1 + (n - n0 - 1) + 1) <=? dim); 
      bdestruct (n0 + k + (1 + (n + k - (n0 + k) - 1) + 1) <=? k + dim);
      try lia;
      try (remove_zero_gates; trivial).
      clear H1.
      restore_dims_fast.
      repeat rewrite <- (kron_assoc (I (2^k))). 
      rewrite id_kron; unify_pows_two.
      unify_matrices_light.
Qed.


(** Combine two programs in parallel. **)

(* Note that we have no way to enforce that dim1 and dim2 are actually the 
   dimensions of the global registers of c1 and c2. *)
Definition inPar {dim1 dim2} (c1 : ucom dim1) (c2 : ucom dim2) :=
  (cast c1 (dim1 + dim2)); (cast (map_qubits (fun q => q + dim1) c2) (dim1 + dim2)).

Lemma inPar_WT : forall {dim1 dim2} (c1 : ucom dim1) (c2 : ucom dim2),
  uc_well_typed c1 -> uc_well_typed c2 -> uc_well_typed (inPar c1 c2).
Proof.
  intros dim1 dim2 c1 c2 WTc1 WTc2.
  unfold inPar.
  apply WT_seq.
  - clear - WTc1.
    induction WTc1; simpl; constructor; try lia; assumption.
  - clear - WTc2. 
    induction WTc2; simpl; constructor; try lia; assumption.
Qed.

Lemma inPar_correct : forall {dim1 dim2} (c1 : ucom dim1) (c2 : ucom dim2),
  uc_well_typed c1 -> uc_eval (inPar c1 c2) = (uc_eval c1) ⊗ (uc_eval c2).
Proof.
  intros dim1 dim2 c1 c2 WTc1.
  simpl.
  rewrite <- (pad_dims_r c1); try assumption.
  rewrite <- pad_dims_l.
  restore_dims_strong.
  rewrite kron_mixed_product.
  Msimpl.
  reflexivity.
Qed.
