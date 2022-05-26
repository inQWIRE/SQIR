Require Import GHZ.
Require Import ExtractionGateSet.

(** Alternate definition of GHZ used for extraction. *)

Fixpoint ghz (n : nat) : ucom U :=
  match n with
  | 0        => SKIP
  | 1        => H 0
  | S (S n'' as n') => ghz n' >> CX n'' n'      
  end.

Lemma ghz_same : forall dim n, 
  uc_eval dim (ghz n) = UnitarySem.uc_eval (GHZ.GHZ dim n).
Proof.
  intros dim n.
  induction n; simpl.
  reflexivity.
  destruct n.
  reflexivity.
  remember (ghz (S n)) as ghzn.
  remember (GHZ dim (S n)) as GHZn.
  unfold uc_eval in *.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem ghz_correct : forall n : nat, 
  (0 < n)%nat -> uc_eval n (ghz n) × n ⨂ ∣0⟩ = GHZ.ghz n.
Proof.
  intros.
  rewrite ghz_same.
  apply GHZ.GHZ_correct.
  assumption.
Qed.
