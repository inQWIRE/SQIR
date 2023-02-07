Require Import RCIR Psatz SQIR.ExtractionGateSet Resource ModMult ExtrShor NumTheory.

Lemma bcgcount_bygatectrl_MAJ :
  forall a b c d, bcgcount (bygatectrl d (MAJ a b c)) <= 3.
Proof.
  intros. simpl. lia.
Qed.

Lemma bcgcount_2bygatectrl_MAJ :
  forall a b c d e, bcgcount (bygatectrl e (bygatectrl d (MAJ a b c))) <= 3.
Proof.
  intros.
  simpl. lia.
Qed.

Lemma bcgcount_bygatectrl_UMA :
  forall a b c d, bcgcount (bygatectrl d (UMA a b c)) <= 3.
Proof.
  intros. simpl. lia.
Qed.

Lemma bcgcount_2bygatectrl_UMA :
  forall a b c d e, bcgcount (bygatectrl e (bygatectrl d (UMA a b c))) <= 3.
Proof.
  intros. simpl. lia.
Qed.

Lemma bcgcount_MAJseq' :
  forall i n c0, bcgcount (MAJseq' i n c0) <= 3 * i + 3.
Proof.
  intros.
  induction i; simpl; lia.
Qed.

Lemma bcgcount_MAJseq :
  forall n, 0 < n -> bcgcount (MAJseq n) <= 3 * n.
Proof.
  intros. unfold MAJseq.
  specialize (bcgcount_MAJseq' (n - 1) n 0) as G.
  lia.
Qed.

Lemma bcgcount_bygatectrl_MAJseq' :
  forall i n c0 q, bcgcount (bygatectrl q (MAJseq' i n c0)) <= 3 * i + 3.
Proof.
  intros.
  induction i; simpl; lia.
Qed.

Lemma bcgcount_2bygatectrl_MAJseq' :
  forall i n c0 q q', bcgcount (bygatectrl q (bygatectrl q' (MAJseq' i n c0))) <= 3 * i + 3.
Proof.
  intros.
  induction i; simpl; lia.
Qed.

Lemma bcgcount_bygatectrl_MAJseq :
  forall n q, 0 < n -> bcgcount (bygatectrl q (MAJseq n)) <= 3 * n.
Proof.
  intros. unfold MAJseq.
  specialize (bcgcount_bygatectrl_MAJseq' (n - 1) n 0 q) as G.
  lia.
Qed.

Lemma bcgcount_2bygatectrl_MAJseq :
  forall n q q', 0 < n -> bcgcount (bygatectrl q (bygatectrl q' (MAJseq n))) <= 3 * n.
Proof.
  intros. unfold MAJseq.
  specialize (bcgcount_2bygatectrl_MAJseq' (n - 1) n 0 q q') as G.
  lia.
Qed.

Lemma bcgcount_UMAseq' :
  forall i n c0, bcgcount (UMAseq' i n c0) <= 3 * i + 3.
Proof.
  intros.
  induction i; simpl; lia.
Qed.

Lemma bcgcount_UMAseq :
  forall n, 0 < n -> bcgcount (UMAseq n) <= 3 * n.
Proof.
  intros. unfold UMAseq.
  specialize (bcgcount_UMAseq' (n - 1) n 0) as G.
  lia.
Qed.

Lemma bcgcount_bygatectrl_UMAseq' :
  forall i n c0 q, bcgcount (bygatectrl q (UMAseq' i n c0)) <= 3 * i + 3.
Proof.
  intros.
  induction i; simpl; lia.
Qed.

Lemma bcgcount_bygatectrl_UMAseq :
  forall n q, 0 < n -> bcgcount (bygatectrl q (UMAseq n)) <= 3 * n.
Proof.
  intros. unfold UMAseq.
  specialize (bcgcount_bygatectrl_UMAseq' (n - 1) n 0 q) as G.
  lia.
Qed.

Lemma bcgcount_2bygatectrl_UMAseq' :
  forall i n c0 q q', bcgcount (bygatectrl q (bygatectrl q' (UMAseq' i n c0))) <= 3 * i + 3.
Proof.
  intros.
  induction i; simpl; lia.
Qed.

Lemma bcgcount_2bygatectrl_UMAseq :
  forall n q q', 0 < n -> bcgcount (bygatectrl q (bygatectrl q' (UMAseq n))) <= 3 * n.
Proof.
  intros. unfold UMAseq.
  specialize (bcgcount_2bygatectrl_UMAseq' (n - 1) n 0 q q') as G.
  lia.
Qed.

Lemma bcgcount_adder01 :
  forall n, 0 < n -> bcgcount (adder01 n) <= 6 * n.
Proof.
  intros. simpl.
  specialize (bcgcount_MAJseq n H) as G1.
  specialize (bcgcount_UMAseq n H) as G2.
  lia.
Qed.

Lemma bcgcount_bygatectrl_adder01 :
  forall n q, 0 < n -> bcgcount (bygatectrl q (adder01 n)) <= 6 * n.
Proof.
  intros. simpl.
  specialize (bcgcount_bygatectrl_MAJseq n q H) as G1.
  specialize (bcgcount_bygatectrl_UMAseq n q H) as G2.
  lia.
Qed.

Lemma bcgcount_2bygatectrl_adder01 :
  forall n q q', 0 < n -> bcgcount (bygatectrl q (bygatectrl q' (adder01 n))) <= 6 * n.
Proof.
  intros. simpl.
  specialize (bcgcount_2bygatectrl_MAJseq n q q' H) as G1.
  specialize (bcgcount_2bygatectrl_UMAseq n q q' H) as G2.
  lia.
Qed.

Local Opaque adder01.

Lemma bcgcount_negator0' :
  forall i, bcgcount (negator0' i) <= i + 1.
Proof.
  intros.
  induction i; simpl; lia.
Qed.

Lemma bcgcount_negator0 :
  forall n, bcgcount (negator0 n) <= n + 1.
Proof.
  intros. apply bcgcount_negator0'.
Qed.

Lemma bcgcount_bygatectrl_negator0' :
  forall i q, bcgcount (bygatectrl q (negator0' i)) <= i + 1.
Proof.
  intros.
  induction i; simpl; lia.
Qed.

Lemma bcgcount_bygatectrl_negator0 :
  forall n q, bcgcount (bygatectrl q (negator0 n)) <= n + 1.
Proof.
  intros. apply bcgcount_bygatectrl_negator0'.
Qed.

Lemma bcgcount_2bygatectrl_negator0' :
  forall i q q', bcgcount (bygatectrl q (bygatectrl q' (negator0' i))) <= i + 5.
Proof.
  intros.
  induction i; simpl; lia.
Qed.

Lemma bcgcount_2bygatectrl_negator0 :
  forall n q q', bcgcount (bygatectrl q (bygatectrl q' (negator0 n))) <= n + 5.
Proof.
  intros. apply bcgcount_2bygatectrl_negator0'.
Qed.

Lemma bcgcount_bygatectrl_subtractor01 :
  forall n q, 0 < n -> bcgcount (bygatectrl q (subtractor01 n)) <= 8 * n + 4.
Proof.
  intros. simpl.
  specialize (bcgcount_bygatectrl_negator0 n q) as G1.
  specialize (bcgcount_bygatectrl_adder01 n q H) as G2.
  rewrite bygatectrl_bcinv. rewrite bcgcount_bcinv.
  lia.
Qed.

Lemma bcgcount_2bygatectrl_subtractor01 :
  forall n q q', 0 < n -> bcgcount (bygatectrl q (bygatectrl q' (subtractor01 n))) <= 8 * n + 12.
Proof.
  intros. simpl.
  specialize (bcgcount_2bygatectrl_negator0 n q q') as G1.
  specialize (bcgcount_2bygatectrl_adder01 n q q' H) as G2.
  do 2 rewrite bygatectrl_bcinv. rewrite bcgcount_bcinv.
  lia.
Qed.

Lemma bcgcount_swapper02' :
  forall i n, bcgcount (swapper02' i n) <= i + 1.
Proof.
  intros. induction i; simpl; lia.
Qed.

Lemma bcgcount_swapper02 :
  forall n, bcgcount (swapper02 n) <= n + 1.
Proof.
  intros. specialize (bcgcount_swapper02' n n) as G. unfold swapper02. lia.
Qed.

Lemma bcgcount_bygatectrl_swapper02' :
  forall i n q, bcgcount (bygatectrl q (swapper02' i n)) <= i + 1.
Proof.
  intros. induction i; simpl; lia.
Qed.

Lemma bcgcount_bygatectrl_swapper02 :
  forall n q, bcgcount (bygatectrl q (swapper02 n)) <= n + 1.
Proof.
  intros. specialize (bcgcount_bygatectrl_swapper02' n n q) as G. unfold swapper02. lia.
Qed.

Lemma bcgcount_highb01 :
  forall n, 0 < n -> bcgcount (highb01 n) <= 6 * n + 1.
Proof.
  intros. simpl. 
  specialize (bcgcount_MAJseq n H) as G1.
  rewrite bcgcount_bcinv.
  lia.
Qed.

Lemma bcgcount_bygatectrl_highb01 :
  forall n q, 0 < n -> bcgcount (bygatectrl q (highb01 n)) <= 6 * n + 1.
Proof.
  intros. simpl. 
  specialize (bcgcount_bygatectrl_MAJseq n q H) as G1.
  rewrite bygatectrl_bcinv. rewrite bcgcount_bcinv.
  lia.
Qed.
Local Opaque highb01.

Lemma bcgcount_comparator01 :
  forall n, 0 < n -> bcgcount (comparator01 n) <= 8 * n + 5.
Proof.
  intros. simpl. 
  rewrite bcgcount_bcinv.
  specialize (bcgcount_negator0 n) as G1.
  specialize (bcgcount_highb01 n H) as G2.
  lia.
Qed.

Lemma bcgcount_bygatectrl_comparator01 :
  forall n q, 0 < n -> bcgcount (bygatectrl q (comparator01 n)) <= 8 * n + 5.
Proof.
  intros. simpl. 
  rewrite bygatectrl_bcinv. rewrite bcgcount_bcinv.
  specialize (bcgcount_bygatectrl_negator0 n q) as G1.
  specialize (bcgcount_bygatectrl_highb01 n q H) as G2.
  lia.
Qed.
Local Opaque comparator01.

Lemma bcgcount_modadder21 :
  forall n, 0 < n -> bcgcount (modadder21 n) <= 34 * n + 19.
Proof.
  intros. simpl.
  specialize (bcgcount_swapper02 n) as G1.
  specialize (bcgcount_adder01 n H) as G2.
  specialize (bcgcount_comparator01 n H) as G3.
  specialize (bcgcount_bygatectrl_negator0 n 1) as G4.
  specialize (bcgcount_bygatectrl_adder01 n 1 H) as G5.
  repeat rewrite bygatectrl_bcinv. repeat rewrite bcgcount_bcinv.
  lia.
Qed.

Lemma bcgcount_bygatectrl_modadder21 :
  forall n q, 0 < n -> bcgcount (bygatectrl q (modadder21 n)) <= 34 * n + 27.
Proof.
  intros. simpl.
  specialize (bcgcount_bygatectrl_swapper02 n q) as G1.
  specialize (bcgcount_bygatectrl_adder01 n q H) as G2.
  specialize (bcgcount_bygatectrl_comparator01 n q H) as G3.
  specialize (bcgcount_2bygatectrl_negator0 n q 1) as G4.
  specialize (bcgcount_2bygatectrl_adder01 n q 1 H) as G5.
  repeat rewrite bygatectrl_bcinv. repeat rewrite bcgcount_bcinv.
  lia.
Qed.
Local Opaque modadder21.

Lemma bcgcount_doubler1' :
  forall i n, bcgcount (doubler1' i n) <= i + 1.
Proof.
  intros.
  induction i; simpl; lia.
Qed.

Lemma bcgcount_doubler1 :
  forall n, 0 < n -> bcgcount (doubler1 n) <= n.
Proof.
  intros. unfold doubler1.
  specialize (bcgcount_doubler1' (n - 1) (2 + n)) as G.
  lia.
Qed.

Lemma bcgcount_bygatectrl_doubler1' :
  forall i n q, bcgcount (bygatectrl q (doubler1' i n)) <= i + 1.
Proof.
  intros.
  induction i; simpl; lia.
Qed.

Lemma bcgcount_bygatectrl_doubler1 :
  forall n q, 0 < n -> bcgcount (bygatectrl q (doubler1 n)) <= n.
Proof.
  intros. unfold doubler1.
  specialize (bcgcount_bygatectrl_doubler1' (n - 1) (2 + n) q) as G.
  lia.
Qed.

Local Opaque doubler1.

Lemma bcgcount_moddoubler01 :
  forall n, 0 < n -> bcgcount (moddoubler01 n) <= 17 * n + 9.
Proof.
  intros. simpl.
  specialize (bcgcount_doubler1 n H) as G1.
  specialize (bcgcount_comparator01 n H) as G2.
  specialize (bcgcount_bygatectrl_negator0 n 1) as G3.
  specialize (bcgcount_bygatectrl_adder01 n 1 H) as G4.
  repeat rewrite bygatectrl_bcinv. repeat rewrite bcgcount_bcinv.
  lia.
Qed.

Lemma bcgcount_bygatectrl_moddoubler01 :
  forall n q, 0 < n -> bcgcount (bygatectrl q (moddoubler01 n)) <= 17 * n + 17.
Proof.
  intros. simpl.
  specialize (bcgcount_bygatectrl_doubler1 n q H) as G1.
  specialize (bcgcount_bygatectrl_comparator01 n q H) as G2.
  specialize (bcgcount_2bygatectrl_negator0 n q 1) as G3.
  specialize (bcgcount_2bygatectrl_adder01 n q 1 H) as G4.
  repeat rewrite bygatectrl_bcinv. repeat rewrite bcgcount_bcinv.
  lia.
Qed.
Local Opaque moddoubler01.

Lemma bcgcount_swapper12' :
  forall i n, bcgcount (swapper12' i n) <= i + 1.
Proof.
  intros. induction i; simpl; lia.
Qed.

Lemma bcgcount_swapper12 :
  forall n, bcgcount (swapper12 n) <= n + 1.
Proof.
  intros. specialize (bcgcount_swapper12' n n) as G. unfold swapper12. lia.
Qed.

Lemma bcgcount_bygatectrl_swapper12' :
  forall i n q, bcgcount (bygatectrl q (swapper12' i n)) <= i + 1.
Proof.
  intros. induction i; simpl; lia.
Qed.

Lemma bcgcount_bygatectrl_swapper12 :
  forall n q, bcgcount (bygatectrl q (swapper12 n)) <= n + 1.
Proof.
  intros. specialize (bcgcount_bygatectrl_swapper12' n n q) as G. unfold swapper12. lia.
Qed.

Lemma bcgcount_modadder12 :
  forall n, 0 < n -> bcgcount (modadder12 n) <= 36 * n + 21.
Proof.
  intros. simpl.
  specialize (bcgcount_swapper12 n) as G1.
  specialize (bcgcount_modadder21 n H) as G2.
  lia.
Qed.

Lemma bcgcount_bygatectrl_modadder12 :
  forall n q, 0 < n -> bcgcount (bygatectrl q (modadder12 n)) <= 36 * n + 29.
Proof.
  intros. simpl.
  specialize (bcgcount_bygatectrl_swapper12 n q) as G1.
  specialize (bcgcount_bygatectrl_modadder21 n q H) as G2.
  lia.
Qed.
Local Opaque modadder12.

Lemma bcgcount_modsummer' :
  (*forall i n fC, 0 < n -> bcgcount (modsummer' i n fC) <= 84 * i * n + 36 * n + 21.*)
  forall i n fC, 0 < n -> bcgcount (modsummer' i n fC) <= 53 * i * n + 39 * i + 36 * n + 21.
Proof.
  intros.
  induction i; simpl.
  - destruct (fC 0).
    + specialize (bcgcount_modadder12 n H) as G.
      lia.
    + simpl. lia.
  - destruct (fC (S i)).
    + specialize (bcgcount_modadder12 n H) as G1.
      specialize (bcgcount_moddoubler01 n H) as G2.
      lia.
    + specialize (bcgcount_moddoubler01 n H) as G.
      simpl. lia.
Qed.

Lemma bcgcount_modsummer :
  forall n C, 0 < n -> bcgcount (modsummer n C) <= 53 * n * n + 22 * n - 18.
Proof.
  intros. unfold modsummer.
  specialize (bcgcount_modsummer' (n - 1) n (nat2fb C) H) as G.
  lia.
Qed.

Lemma bcgcount_bygatectrl_modsummer' :
  forall i n q fC, 0 < n -> bcgcount (bygatectrl q (modsummer' i n fC)) <= 53 * i * n + 47 * i + 36 * n + 29.
Proof.
  intros.
  induction i; simpl.
  - destruct (fC 0).
    + specialize (bcgcount_bygatectrl_modadder12 n q H) as G.
      lia.
    + simpl. lia.
  - destruct (fC (S i)).
    + specialize (bcgcount_bygatectrl_modadder12 n q H) as G1.
      specialize (bcgcount_bygatectrl_moddoubler01 n q H) as G2.
      lia.
    + specialize (bcgcount_bygatectrl_moddoubler01 n q H) as G.
      simpl. lia.
Qed.

Lemma bcgcount_bygatectrl_modsummer :
  forall n q C, 0 < n -> bcgcount (bygatectrl q (modsummer n C)) <= 53 * n * n + 30 * n - 18.
Proof.
  intros. unfold modsummer.
  specialize (bcgcount_bygatectrl_modsummer' (n - 1) n q (nat2fb C) H) as G.
  lia.
Qed.

Lemma bcgcount_modmult_half :
  forall n C, 0 < n -> bcgcount (modmult_half n C) <= 106 * n * n + 44 * n - 36.
Proof.
  intros. simpl.
  specialize (bcgcount_modsummer n C H) as G1.
  specialize (bcgcount_modsummer n 0 H) as G2.
  rewrite bcgcount_bcinv.
  lia.
Qed.

Lemma bcgcount_bygatectrl_modmult_half :
  forall n q C, 0 < n -> bcgcount (bygatectrl q (modmult_half n C)) <= 106 * n * n + 60 * n - 36.
Proof.
  intros. simpl.
  specialize (bcgcount_bygatectrl_modsummer n q C H) as G1.
  specialize (bcgcount_bygatectrl_modsummer n q 0 H) as G2.
  rewrite bygatectrl_bcinv. rewrite bcgcount_bcinv.
  lia.
Qed.

Local Opaque modmult_half.

Lemma bcgcount_modmult_full :
  forall n C Cinv, 0 < n -> bcgcount (modmult_full C Cinv n) <= 212 * n * n + 89 * n - 71.
Proof.
  intros. simpl.
  specialize (bcgcount_modmult_half n C H) as G1.
  specialize (bcgcount_modmult_half n Cinv H) as G2.
  specialize (bcgcount_swapper12 n) as G3.
  rewrite bcgcount_bcinv.
  nia.
Qed.

Lemma bcgcount_bygatectrl_modmult_full :
  forall n q C Cinv, 0 < n -> bcgcount (bygatectrl q (modmult_full C Cinv n)) <= 212 * n * n + 121 * n - 71.
Proof.
  intros. simpl.
  specialize (bcgcount_bygatectrl_modmult_half n q C H) as G1.
  specialize (bcgcount_bygatectrl_modmult_half n q Cinv H) as G2.
  specialize (bcgcount_bygatectrl_swapper12 n q) as G3.
  rewrite bygatectrl_bcinv, bcgcount_bcinv.
  nia.
Qed.

Local Opaque modmult_full.

Lemma bcgcount_swapperh1' :
  forall i n, bcgcount (swapperh1' i n) <= i + 1.
Proof.
  intros. induction i; simpl; lia.
Qed.

Lemma bcgcount_swapperh1 :
  forall n, bcgcount (swapperh1 n) <= n + 1.
Proof.
  intros. specialize (bcgcount_swapperh1' n n) as G. unfold swapperh1. lia.
Qed.

Lemma bcgcount_bygatectrl_swapperh1' :
  forall i n q, bcgcount (bygatectrl q (swapperh1' i n)) <= i + 1.
Proof.
  intros. induction i; simpl; lia.
Qed.

Lemma bcgcount_bygatectrl_swapperh1 :
  forall n q, bcgcount (bygatectrl q (swapperh1 n)) <= n + 1.
Proof.
  intros. specialize (bcgcount_bygatectrl_swapperh1' n n q) as G. unfold swapperh1. lia.
Qed.

Lemma bcgcount_genM0' :
  forall i f, bcgcount (genM0' i f) <= i + 1.
Proof.
  intros. induction i; simpl. lia.
  destruct (f i); simpl; lia.
Qed.

Lemma bcgcount_genM0 :
  forall M n, bcgcount (genM0 M n) <= n + 1.
Proof.
  intros. specialize (bcgcount_genM0' n (nat2fb M)) as G. unfold genM0. lia.
Qed.

Lemma bcgcount_bygatectrl_genM0' :
  forall i q f, bcgcount (bygatectrl q (genM0' i f)) <= i + 1.
Proof.
  intros. induction i; simpl. lia.
  destruct (f i); simpl; lia.
Qed.

Lemma bcgcount_bygatectrl_genM0 :
  forall M n q, bcgcount (bygatectrl q (genM0 M n)) <= n + 1.
Proof.
  intros. specialize (bcgcount_bygatectrl_genM0' n q (nat2fb M)) as G. unfold genM0. lia.
Qed.

Lemma bcgcount_modmult :
  forall M C Cinv n, 0 < n -> bcgcount (modmult M C Cinv n) <= 212 * n * n + 93 * n - 67.
Proof.
  intros. simpl.
  specialize (bcgcount_swapperh1 n) as G1.
  specialize (bcgcount_genM0 M n) as G2.
  specialize (bcgcount_modmult_full n C Cinv H) as G3.
  repeat rewrite bcgcount_bcinv.
  nia.
Qed.

Lemma bcgcount_bygatectrl_modmult :
  forall M C Cinv n q, 0 < n -> bcgcount (bygatectrl q (modmult M C Cinv n)) <= 212 * n * n + 125 * n - 67.
Proof.
  intros. simpl.
  specialize (bcgcount_bygatectrl_swapperh1 n q) as G1.
  specialize (bcgcount_bygatectrl_genM0 M n q) as G2.
  specialize (bcgcount_bygatectrl_modmult_full n q C Cinv H) as G3.
  do 2 rewrite bygatectrl_bcinv. repeat rewrite bcgcount_bcinv.
  nia.
Qed.

Local Opaque modmult.

Lemma bcgcount_reverser' :
  forall i n, bcgcount (reverser' i n) <= i + 1.
Proof.
  intros. induction i; simpl.
  unfold safe_swap. destruct (PeanoNat.Nat.eqb 0 (n - 1)); easy.
  unfold safe_swap. destruct (PeanoNat.Nat.eqb (S i) (n - 1 - S i)); simpl; lia.
Qed.

Lemma bcgcount_bygatectrl_reverser' :
  forall i n q, bcgcount (bygatectrl q (reverser' i n)) <= i + 1.
Proof.
  intros. induction i; simpl.
  unfold safe_swap. destruct (PeanoNat.Nat.eqb 0 (n - 1)); easy.
  unfold safe_swap. destruct (PeanoNat.Nat.eqb (S i) (n - 1 - S i)); simpl; lia.
Qed.

Lemma div2_leq :
  forall n, PeanoNat.Nat.div n 2 <= n.
Proof.
  intros. apply PeanoNat.Nat.div_le_upper_bound.
  easy. lia.
Qed.

Lemma bcgcount_reverser :
  forall n, 0 < n -> bcgcount (reverser n) <= n.
Proof.
  intros. unfold reverser.
  specialize (bcgcount_reverser' (PeanoNat.Nat.div (n - 1) 2) n) as G1.
  specialize (div2_leq (n - 1)) as G2.
  lia.
Qed.

Lemma bcgcount_bygatectrl_reverser :
  forall n q, 0 < n -> bcgcount (bygatectrl q (reverser n)) <= n.
Proof.
  intros. unfold reverser.
  specialize (bcgcount_bygatectrl_reverser' (PeanoNat.Nat.div (n - 1) 2) n q) as G1.
  specialize (div2_leq (n - 1)) as G2.
  lia.
Qed.

Lemma bcgcount_modmult_rev :
  forall M C Cinv n, 0 < n -> bcgcount (modmult_rev M C Cinv n) <= 212 * n * n + 943 * n + 967.
Proof.
  intros. simpl.
  rewrite bcgcount_bcinv.
  specialize (bcgcount_reverser n H) as G1.
  assert (0 < S (S n)) by lia.
  specialize (bcgcount_modmult M C Cinv (S (S n)) H0) as G2.
  nia.
Qed.

Lemma bcgcount_bygatectrl_modmult_rev :
  forall M C Cinv n q, 0 < n -> bcgcount (bygatectrl q (modmult_rev M C Cinv n)) <= 212 * n * n + 975 * n + 1031.
Proof.
  intros. simpl.
  rewrite bygatectrl_bcinv. rewrite bcgcount_bcinv.
  specialize (bcgcount_bygatectrl_reverser n q H) as G1.
  assert (0 < S (S n)) by lia.
  specialize (bcgcount_bygatectrl_modmult M C Cinv (S (S n)) q H0) as G2.
  nia.
Qed.

Local Opaque modmult.

Lemma ugcount_controlled_rotations :
  forall n, 0 < n -> ugcount (controlled_rotations n) <= n.
Proof.
  induction n; intros. lia.
  destruct n. simpl. lia.
  assert (0 < S n) by lia. apply IHn in H0.
  remember (S n) as Sn.
  do 3 (destruct Sn; try (simpl in *; lia)).
Qed.

Local Opaque controlled_rotations.

Lemma ugcount_QFT :
  forall n, 0 < n -> ugcount (QFT n) <= n * n.
Proof.
  induction n; intros. lia.
  destruct n. simpl. lia.
  assert (0 < S n) by lia. apply IHn in H0.
  remember (S n) as Sn.
  destruct Sn; try (simpl in *; lia).
  specialize (ugcount_controlled_rotations (S (S Sn)) H) as G.
  simpl in *. rewrite ugcount_map_qubits.
  lia.
Qed.

Lemma ugcount_reverse_qubits' :
  forall dim n, ugcount (reverse_qubits' dim n) <= Nat.max n 1.
Proof.
  intros. induction n. simpl. lia.
  destruct n; simpl in *; lia.
Qed.

Lemma ugcount_reverse_qubits :
  forall n, 0 < n -> ugcount (reverse_qubits n) <= n.
Proof.
  intros. unfold reverse_qubits.
  specialize (ugcount_reverse_qubits' n (PeanoNat.Nat.div n 2)) as G.
  specialize (div2_leq n) as G'.
  lia.
Qed.

(*
Lemma bcgcount_controlled_powers' :
  forall k f kmax bound,
    0 < k ->
    (forall i, i < k -> bcgcount (f i) <= bound) ->
    bcgcount (controlled_powers' f k kmax) <= gcCC4X * bound * k.
Proof.
  Local Opaque bcgcount gcCC4X.
  intros. induction k. lia.
  destruct k. simpl.
  - specialize (bcgcount_bccont (f 0) (kmax - 1)) as G.
    assert (0 < 1) by lia. specialize (H0 0 H1).
    nia.
  - assert (0 < S k) by lia.
    assert (forall i : nat, i < S k -> bcgcount (f i) <= bound) by (intros; apply H0; lia).
    specialize (IHk H1 H2).
    remember (S k) as Sk.
    destruct Sk.
    + specialize (bcgcount_bccont (f 0) (kmax - 1)) as G.
      assert (0 < 1) by lia. specialize (H0 0 H3).
      nia.
    + specialize (bcgcount_bccont (f (S Sk)) (kmax - Sk - 1)) as G.
      Local Transparent bcgcount.
      simpl in *.
      assert (bcgcount (f (S Sk)) <= bound) by (apply H0; lia).
      nia.
Qed.
*)

Lemma bcgcount_controlled_powers'_precise :
  forall k f kmax bound,
    0 < k ->
    (forall i q, i < k -> bcgcount (bygatectrl q (f i)) <= bound) ->
    bcgcount (controlled_powers' f k kmax) <= bound * k.
Proof.
  Local Opaque bcgcount gcCC4X.
  intros. induction k. lia.
  destruct k. simpl.
  - assert (0 < 1) by lia. specialize (H0 0 (kmax - 1) H1).
    nia.
  - assert (0 < S k) by lia.
    assert (forall i q : nat, i < S k -> bcgcount (bygatectrl q (f i)) <= bound) by (intros; apply H0; lia).
    specialize (IHk H1 H2).
    remember (S k) as Sk.
    simpl.
    destruct Sk.
    + simpl. specialize (H0 0 (kmax - 1) H).
      nia.
    + assert (S Sk < S (S Sk)) by lia.
      specialize (H0 (S Sk) (kmax - S Sk - 1) H3) as G.
      Local Transparent bcgcount.
      simpl in *. nia.
Qed.

Lemma bcelim_seq_bcskip :
  forall c1 c2, bcelim (c1; c2)%bccom = bcskip -> bcelim c1 = bcskip /\ bcelim c2 = bcskip.
Proof.
  intros. simpl in H.
  destruct (bcelim c1); destruct (bcelim c2); try easy.
Qed.

Lemma bcelim_bygatectrl_bcskip :
  forall c q,
    bcelim c = bcskip -> bcelim (bygatectrl q c) = bcskip.
Proof.
  intros. induction c; try easy.
  - simpl.
    destruct (bcelim c) eqn:E;
      try (simpl in H; rewrite E in H; easy).
  - simpl.
    apply bcelim_seq_bcskip in H. destruct H as [H1 H2].
    apply IHc1 in H1. apply IHc2 in H2.
    rewrite H1, H2.
    easy.
Qed.

Lemma bcelim_bygatectrl_not_bcskip :
  forall c q,
    bcelim c <> bcskip -> bcelim (bygatectrl q c) = bygatectrl q (bcelim c).
Proof.
  intros. induction c; try easy.
  - simpl. destruct (bcelim c) eqn:E; try easy.
    simpl in H. rewrite E in H. easy.
  - destruct (bcelim c1) eqn:E1.
    + simpl in H. rewrite E1 in H. apply IHc2 in H.
      simpl. rewrite E1. rewrite bcelim_bygatectrl_bcskip; easy.
      all : (simpl; rewrite IHc1 by easy; rewrite E1; simpl;
        destruct (bcelim c2) eqn:E2;
        try (rewrite IHc2 by easy; easy);
        try (rewrite bcelim_bygatectrl_bcskip; easy)).
Qed.

Lemma bcgcount_bygatectrl_bcelim :
  forall c q,
    bcgcount (bygatectrl q (bcelim c)) <= bcgcount (bcelim (bygatectrl q c)).
Proof.
  intros. induction c; try (simpl in *; lia).
  - simpl. destruct (bcelim c) eqn:E; try (simpl in *; lia).
  - simpl.
    destruct (bcelim c1) eqn:E11; destruct (bcelim (bygatectrl q c1)) eqn:E12;
      try (rewrite bcelim_bygatectrl_bcskip in E12; easy);
      try (rewrite bcelim_bygatectrl_not_bcskip, E11 in E12; try rewrite E11; easy).
    1-3 : rewrite bcelim_bygatectrl_not_bcskip, E11 in E12; try rewrite E11; try easy; inversion E12; subst;
      destruct (bcelim c2) eqn:E21; destruct (bcelim (bygatectrl n0 c2)) eqn:E22;
        try (rewrite bcelim_bygatectrl_bcskip in E22; easy);
        try (rewrite bcelim_bygatectrl_not_bcskip, E21 in E22; try rewrite E21; easy);
        try (rewrite bcelim_bygatectrl_not_bcskip, E21 in E22; try rewrite E21; try easy; inversion E22; subst; try easy; try lia).
     rewrite bcelim_bygatectrl_not_bcskip, E11 in E12; try rewrite E11; try easy; inversion E12; subst.
     destruct (bcelim c2) eqn:E21; destruct (bcelim (bygatectrl q c2)) eqn:E22;
        try (rewrite bcelim_bygatectrl_bcskip in E22; easy);
        try (rewrite bcelim_bygatectrl_not_bcskip, E21 in E22; try rewrite E21; easy);
        try (rewrite bcelim_bygatectrl_not_bcskip, E21 in E22; try rewrite E21; try easy; inversion E22; subst; try easy; try lia).
Qed.

Lemma ugcount_shor_circuit :
  forall a N,
    0 < N ->
    let m := Nat.log2 (2 * Nat.pow N 2)%nat in
    let n := Nat.log2 (2 * N) in
    ugcount (shor_circuit a N) <= (212 * n * n + 975 * n + 1031) * m + 4 * m + m * m.
Proof.
  intros. unfold shor_circuit.
  remember (212 * n * n + 975 * n + 1031) as rhs.
  replace (PeanoNat.Nat.log2 (2 * PeanoNat.Nat.pow N 2)) with m by easy.
  replace (PeanoNat.Nat.log2 (2 * N)) with n by easy.
  simpl. do 2 rewrite ugcount_invert.
  assert (0 < m) by (apply PeanoNat.Nat.log2_pos; simpl; lia).
  assert (0 < n) by (apply PeanoNat.Nat.log2_pos; simpl; lia).
  specialize (ugcount_npar m U_H H0) as G1.
  specialize (ugcount_reverse_qubits m) as G2.
  specialize (ugcount_QFT m H0) as G3.
  remember (fun x : nat => map_bccom (fun q : nat => m + q) (modmult_circuit a (modinv a N) N n x)) as f.
  assert (forall i q, i < m -> bcgcount (bygatectrl q (f i)) <= rhs). {
    intros. rewrite Heqf, bcgcount_bygatectrl_map_bccom.
    unfold modmult_circuit.
    specialize (bcgcount_bcelim (bygatectrl q (modmult_rev N (modexp a (PeanoNat.Nat.pow 2 i) N) (modexp (modinv a N) (PeanoNat.Nat.pow 2 i) N) n))) as G4.
    specialize (bcgcount_bygatectrl_modmult_rev N (modexp a (PeanoNat.Nat.pow 2 i) N) (modexp (modinv a N) (PeanoNat.Nat.pow 2 i) N) n q H1) as G5.
    specialize (bcgcount_bygatectrl_bcelim (modmult_rev N (modexp a (PeanoNat.Nat.pow 2 i) N) (modexp (modinv a N) (PeanoNat.Nat.pow 2 i) N) n) q) as G6.
    lia.
  }
  unfold controlled_powers.
  specialize (ugcount_leq_bcgcount (controlled_powers' f m m)) as T1.
  specialize (bcgcount_controlled_powers'_precise m f m rhs H0 H2) as T2.
  lia.
Qed.
