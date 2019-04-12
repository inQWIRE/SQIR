Require Export UnitarySem.

Local Open Scope ucom_scope.
Local Close Scope C_scope.
Local Close Scope R_scope.

(* Utilities for composing SQIRE programs. Our design is not intended to 
   be compositional (but rather a simple IR). In order to compose two SQIRE
   programs, the programmer (or compiler) needs to map qubits in both programs
   to the new global register. *)


(* TODO: extend the defs below to non-unitary circuits *)

(** General qubit relabeling function. **)

Fixpoint map_qubits (f : nat -> nat) (c : ucom) :=
  match c with
  | uskip => uskip
  | c1; c2 => map_qubits f c1; map_qubits f c2
  | uapp u l => uapp u (map f l)
  end.
  

(** Lemmas about padding **)

Lemma pad_dims_r : forall c n k,
  uc_well_typed n c ->
  (uc_eval n c) ⊗ I (2^k) = uc_eval (n + k) c.  
Proof.
  intros c n k H.
  induction c.
  - simpl. rewrite id_kron. unify_pows_two. reflexivity.
  - inversion H; subst.
    simpl. rewrite <- IHc1, <- IHc2; trivial.
    restore_dims_strong; Msimpl; reflexivity.
  - simpl.
    unfold ueval.
    destruct n0 as [|[|[|]]]; simpl; remove_zero_gates; trivial.
    + destruct l as [| a []]; remove_zero_gates; trivial.
      unfold ueval1.
      repeat match goal with
      | [|- context [pad _ _ ?U ]] => remember U as U'
      end.
      unfold pad.
      assert(L : a + 1 <= n).
      { inversion H; subst.
        specialize (H5 a (or_introl eq_refl)).
        lia.
      }
      bdestruct (a + 1 <=? n); bdestructΩ (a + 1 <=? n+k).
      restore_dims.
      rewrite (kron_assoc (I (2^a) ⊗ U')).
      rewrite id_kron. unify_pows_two.
      replace (n - 1 - a + k) with (n + k - 1 - a) by lia.
      reflexivity.
    + destruct l as [| a [|b[|]]]; remove_zero_gates; trivial.
      unfold ueval_cnot.
      inversion H; subst.
      assert (La : a < n) by (apply H5; simpl; auto).
      assert (Lb : b < n) by (apply H5; simpl; auto).
      clear -La Lb.
      unfold pad.
      bdestruct (a <? b); bdestructΩ (b <? a); remove_zero_gates; trivial.
      * bdestructΩ (a + S (b - a - 1 + 1) <=? n).
        bdestructΩ (a + S (b - a - 1 + 1) <=? n + k).
        restore_dims; rewrite (kron_assoc _ _  (I (2^k))).
        rewrite id_kron.
        unify_pows_two.
        rewrite Nat.sub_add by lia.
        rewrite Nat.add_sub_swap by lia.
        rewrite Nat.add_sub_swap by lia.
        reflexivity.
      * bdestructΩ (b + S (a - b - 1 + 1) <=? n).
        bdestructΩ (b + S (a - b - 1 + 1) <=? n + k).
        restore_dims; rewrite (kron_assoc _ _  (I (2^k))).
        rewrite id_kron.
        unify_pows_two.
        rewrite Nat.sub_add by lia.
        rewrite Nat.add_sub_swap by lia.
        rewrite Nat.add_sub_swap by lia.
        reflexivity.
Qed.

Ltac prove_wt :=
  repeat match goal with
         | |- context [ uc_well_typed ?d uskip ] => apply WT_uskip
         | |- context [ uc_well_typed ?d (useq ?c1 ?c2) ] => apply WT_seq
         | |- context [ uc_well_typed ?d (uapp ?u ?l) ] => try unfold CNOT; apply WT_app
         end.

Lemma typed_pad : forall (n k : nat)(c : ucom), uc_well_typed n c -> uc_well_typed (k + n) c.
Proof.
  intros. generalize dependent n.
  induction c; intros; prove_wt; induction k;
  [| apply IHc1 | apply IHc2 | apply IHc2 | | | | apply (in_bounds_pad _ _ 1%nat) | | ]; 
  inversion H; assumption.
Qed.

Lemma pad_dims_l : forall c n k,
  I (2^n) ⊗ (uc_eval k c) = uc_eval (n + k) (map_qubits (fun q => q + n) c).  
Proof.
  intros c n k.
  induction c.
  - simpl. rewrite id_kron. unify_pows_two. reflexivity.
  - simpl. rewrite <- IHc1, <- IHc2.
    restore_dims_strong; Msimpl. reflexivity.
  - simpl.
    unfold ueval.
    destruct n0 as [|[|[|]]]; simpl; remove_zero_gates; trivial.
    + destruct l as [| a []]; simpl; remove_zero_gates; trivial.
      unfold ueval1.
      repeat match goal with
      | [|- context [pad _ _ ?U ]] => remember U as U'
      end.
      clear.
      unfold pad.
      bdestruct (a + 1 <=? k).
      2: { bdestruct (a + n + 1 <=? n + k). 
           contradict H0; lia.
           remove_zero_gates; trivial. }
      replace (a + n + 1 <=? n + k) with true.
      2: { symmetry; apply Nat.leb_le; lia. }
      restore_dims_strong.
      repeat rewrite <- (kron_assoc (I (2^n))). 
      rewrite id_kron; unify_pows_two.
      replace (n + k - 1 - (a + n)) with (k - 1 - a) by lia.
      replace (n + a) with (a + n) by lia.
      reflexivity.
    + destruct l as [| a [|b[|]]]; simpl; remove_zero_gates; trivial.
      unfold ueval_cnot.
      bdestruct (a <? b).
      * replace (a + n <? b + n) with true by (symmetry; apply Nat.ltb_lt; lia).
        unfold pad.
        remember (b - a - 1) as i.
        replace (b + n - (a + n) - 1) with i by lia.
        bdestruct (a + (1 + i + 1) <=? k).
        2: { bdestruct (a + n + (1 + i + 1) <=? n + k).
             contradict H1; lia.
             remove_zero_gates; trivial. }
        replace (a + n + (1 + i + 1) <=? n + k) with true.
        2: { symmetry; apply Nat.leb_le; lia. }
        replace (n + k - (1 + i + 1) - (a + n)) with (k - (1 + i + 1) - a) by lia.
        replace (b + n - (a + n)) with (b - a) by lia.
        restore_dims_strong.
        repeat rewrite <- (kron_assoc (I (2^n))). 
        rewrite id_kron.
        replace (2 ^ n * 2 ^ a) with (2 ^ (a + n)) by unify_pows_two.
        reflexivity.
      * bdestruct (b <? a).
        2: { bdestruct (a + n <? b + n). 
             contradict H1; lia.
             bdestruct (b + n <? a + n). 
             contradict H2; lia.
             remove_zero_gates; trivial. }
        bdestruct (a + n <? b + n).
        contradict H1; lia.
        replace (b + n <? a + n) with true by (symmetry; apply Nat.ltb_lt; lia).
        unfold pad.
        remember (a - b - 1) as i.
        replace (a + n - (b + n) - 1) with i by lia.
        bdestruct (b + (1 + i + 1) <=? k).
        2: { bdestruct (b + n + (1 + i + 1) <=? n + k).
             contradict H1; lia.
             remove_zero_gates; trivial. }
        replace (b + n + (1 + i + 1) <=? n + k) with true.
        2: { symmetry; apply Nat.leb_le; lia. }
        replace (n + k - (1 + i + 1) - (b + n)) with (k - (1 + i + 1) - b) by lia.
        replace (a + n - (b + n)) with (a - b) by lia.
        restore_dims_strong.
        repeat rewrite <- (kron_assoc (I (2^n))). 
        rewrite id_kron.
        replace (2 ^ n * 2 ^ b) with (2 ^ (b + n)) by unify_pows_two.
        reflexivity.
Qed.


(** Combine two programs in parallel. **)

(* Note that we have no way to enforce that dim1 and dim2 are actually the 
   dimensions of the global registers of c1 and c2. *)
Definition inPar (c1 c2 : ucom) (dim1 dim2 : nat) :=
  c1; map_qubits (fun q => q + dim1) c2.

Require Import Coq.Logic.FinFun.

Lemma inPar_WT : forall c1 c2 dim1 dim2,
  uc_well_typed dim1 c1 -> uc_well_typed dim2 c2 -> uc_well_typed (dim1 + dim2) (inPar c1 c2 dim1 dim2).
Proof.
  intros c1 c2 dim1 dim2 WTc1 WTc2.
  unfold inPar.
  apply WT_seq.
  - replace (dim1 + dim2) with (dim2 + dim1) by lia. 
    apply typed_pad. assumption.
  - clear - WTc2. induction WTc2.
    + apply WT_uskip.
    + apply WT_seq. apply IHWTc2_1. apply IHWTc2_2.
    + apply WT_app.
      * rewrite map_length; assumption.
      * intros x Hin.
        apply in_map_iff in Hin.
        inversion Hin as [x0 [Hx0 Hinx0]].
        apply H0 in Hinx0.
        lia.
      * apply Injective_map_NoDup; try assumption.
        intros x y Hxy.
        lia.
Qed.

Lemma inPar_correct : forall c1 c2 dim1 dim2,
  uc_well_typed dim1 c1 ->
  uc_eval (dim1 + dim2) (inPar c1 c2 dim1 dim2) = (uc_eval dim1 c1) ⊗ (uc_eval dim2 c2).
Proof.
  intros c1 c2 dim1 dim2 WTc1.
  simpl.
  rewrite <- (pad_dims_r c1); try assumption.
  rewrite <- pad_dims_l.
  restore_dims_strong.
  rewrite kron_mixed_product.
  Msimpl.
  reflexivity.
Qed.
