Require Import UnitaryOps.

Local Open Scope ucom_scope.

(* Example from QBRICKS draft. *)

Fixpoint repeat_H n : base_ucom 1 :=
  match n with
  | O => SKIP
  | S n' => H O ; repeat_H n'
  end.

(* Proof of the property stated in the draft. *)

Local Opaque Nat.mul Nat.pow.
Local Coercion Nat.b2n : bool >-> nat.
Lemma repeat_H_id : forall (n : nat) (x : bool),
  Nat.Even n ->
  uc_eval (repeat_H n) × ∣ x ⟩ = ∣ x ⟩.
Proof.
  intros.
  destruct H as [m ?].
  generalize dependent n.
  induction m.
  - intros.
    rewrite Nat.mul_0_r in H.
    rewrite H.
    simpl.
    rewrite denote_SKIP by lia.
    Msimpl. 
    reflexivity.
  - intros.
    replace (2 * S m)%nat with (S (S (2 * m)))%nat in H by lia.
    rewrite H.
    simpl.
    autorewrite with eval_db.
    bdestruct_all.
    Msimpl.
    rewrite (Mmult_assoc _ _ hadamard).
    Qsimpl.
    apply IHm.
    reflexivity.
    replace 2%nat with (2 ^ 1)%nat by reflexivity. (* one weird bit *)
    apply WF_uc_eval.
Qed.

(* More natural proof in our development -- doesn't require expanding
   the definitions of H, SKIP. *)

Require Import Equivalences.
Lemma repeat_H_id' : forall (n : nat),
  Nat.Even n ->
  repeat_H n ≡ SKIP.
Proof.
  intros.
  destruct H as [m ?].
  generalize dependent n.
  induction m.
  - intros.
    rewrite Nat.mul_0_r in H.
    rewrite H.
    simpl.
    reflexivity.
  - intros.
    replace (2 * S m)%nat with (S (S (2 * m)))%nat in H by lia.
    rewrite H.
    simpl.
    rewrite <- useq_assoc.
    rewrite H_H_id.
    rewrite ID_equiv_SKIP by lia.
    rewrite SKIP_id_l.
    apply IHm.
    reflexivity.
Qed.

(* Proof of circuit size. Note that we are just counting the number
   of gates used, which only works as a measure of circuit depth if
   all gates in the program run in serial. *)

Fixpoint gate_count {dim} (u : base_ucom dim) : nat :=
  match u with
  | u1 ; u2 => gate_count u1 + gate_count u2
  | _ => 1
  end.

Lemma repeat_H_num_gates : forall (n : nat),
  gate_count (repeat_H n) = (n + 1)%nat. (* + 1 because SKIP counts as a gate *)
Proof.
  intros.
  induction n; simpl; auto.
Qed.
