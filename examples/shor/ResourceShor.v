Require Import RCIR Psatz AltGateSet Resource ModMult AltShor.

Lemma bcgcount_bygatectrl_MAJ :
  forall a b c d, bcgcount (bygatectrl d (MAJ a b c)) <= 3.
Proof.
  intros. simpl. lia.
Qed.

Lemma bcgcount_bygatectrl_UMA :
  forall a b c d, bcgcount (bygatectrl d (UMA a b c)) <= 3.
Proof.
  intros. simpl. lia.
Qed.

Lemma bcgcount_bygatectrl_MAJseq' :
  forall i n c0 q, bcgcount (bygatectrl q (MAJseq' i n c0)) <= 3 * i + 3.
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

Lemma bcgcount_bygatectrl_adder01 :
  forall n q, 0 < n -> bcgcount (bygatectrl q (adder01 n)) <= 6 * n.
Proof.
  intros. simpl.
  specialize (bcgcount_bygatectrl_MAJseq n q H) as G1.
  specialize (bcgcount_bygatectrl_UMAseq n q H) as G2.
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

Local Opaque adder01.

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

Lemma bcgcount_bygatectrl_subtractor01 :
  forall n q, 0 < n -> bcgcount (bygatectrl q (subtractor01 n)) <= 8 * n + 4.
Proof.
  intros. simpl.
  specialize (bcgcount_bygatectrl_negator0 n q) as G1.
  specialize (bcgcount_bygatectrl_adder01 n q H) as G2.
  rewrite bygatectrl_bcinv. rewrite bcgcount_bcinv.
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

Lemma bcgcount_highb01 :
  forall n, 0 < n -> bcgcount (highb01 n) <= 6 * n + 1.
Proof.
  intros. simpl. 
  specialize (bcgcount_MAJseq n H) as G1.
  rewrite bcgcount_bcinv.
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

Lemma bcgcount_modadder12 :
  forall n, 0 < n -> bcgcount (modadder12 n) <= 36 * n + 21.
Proof.
  intros. simpl.
  specialize (bcgcount_swapper12 n) as G1.
  specialize (bcgcount_modadder21 n H) as G2.
  lia.
Qed.

Local Opaque modadder12.

Lemma bcgcount_modsummer' :
  forall i n fC, 0 < n -> bcgcount (modsummer' i n fC) <= 84 * i * n + 36 * n + 21.
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
  forall n C, 0 < n -> bcgcount (modsummer n C) <= 84 * n * n - 48 * n + 21.
Proof.
  intros. unfold modsummer.
  specialize (bcgcount_modsummer' (n - 1) n (nat2fb C) H) as G.
  lia.
Qed.

Lemma bcgcount_modmult_half :
  forall n C, 0 < n -> bcgcount (modmult_half n C) <= 168 * n * n - 96 * n + 42.
Proof.
  intros. simpl.
  specialize (bcgcount_modsummer n C H) as G1.
  specialize (bcgcount_modsummer n 0 H) as G2.
  rewrite bcgcount_bcinv.
  lia.
Qed.

Local Opaque modmult_half.

Lemma bcgcount_modmult_full :
  forall n C Cinv, 0 < n -> bcgcount (modmult_full C Cinv n) <= 336 * n * n - 191 * n + 85.
Proof.
  intros. simpl.
  specialize (bcgcount_modmult_half n C H) as G1.
  specialize (bcgcount_modmult_half n Cinv H) as G2.
  specialize (bcgcount_swapper12 n) as G3.
  rewrite bcgcount_bcinv.
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

Lemma bcgcount_modmult :
  forall M C Cinv n, 0 < n -> bcgcount (modmult M C Cinv n) <= 336 * n * n - 187 * n + 89.
Proof.
  intros. simpl.
  specialize (bcgcount_swapperh1 n) as G1.
  specialize (bcgcount_genM0 M n) as G2.
  specialize (bcgcount_modmult_full n C Cinv) as G3.
  repeat rewrite bcgcount_bcinv.
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

Lemma bcgcount_modmult_rev :
  forall M C Cinv n, 0 < n -> bcgcount (modmult_rev M C Cinv n) <= 336 * n * n + 1159 * n + 1059.
Proof.
  intros. simpl.
  rewrite bcgcount_bcinv.
  specialize (bcgcount_reverser n H) as G1.
  assert (0 < S (S n)) by lia.
  specialize (bcgcount_modmult M C Cinv (S (S n)) H0) as G2.
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

Lemma ugcount_shor_circuit :
  forall a N,
    0 < N ->
    let m := Nat.log2 (2 * Nat.pow N 2)%nat in
    let n := Nat.log2 (2 * N) in
    ugcount (shor_circuit a N) <= gcCC4X * (336 * n * n + 1159 * n + 1059) * m + 4 * m + m * m.
Proof.
  intros. unfold shor_circuit.
  remember (gcCC4X * (336 * n * n + 1159 * n + 1059) * m + 4 * m + m * m) as rhs.
  remember (336 * n * n + 1159 * n + 1059) as imm.
  replace (PeanoNat.Nat.log2 (2 * PeanoNat.Nat.pow N 2)) with m by easy.
  replace (PeanoNat.Nat.log2 (2 * N)) with n by easy.
  simpl. do 2 rewrite ugcount_invert.
  assert (0 < m) by (apply PeanoNat.Nat.log2_pos; simpl; lia).
  assert (0 < n) by (apply PeanoNat.Nat.log2_pos; simpl; lia).
  specialize (ugcount_npar m U_H H0) as G1.
  specialize (ugcount_reverse_qubits m) as G2.
  specialize (ugcount_QFT m H0) as G3.
  remember (fun x : nat => map_bccom (fun q : nat => m + q) (modmult_circuit a (ShorAux.modinv a N) N n x)) as f.
  assert (forall i, i < m -> bcgcount (f i) <= imm). {
    intros. rewrite Heqf, bcgcount_map_bccom.
    unfold modmult_circuit.
    specialize (bcgcount_bcelim (modmult_rev N (modexp a (PeanoNat.Nat.pow 2 i) N) (modexp (ShorAux.modinv a N) (PeanoNat.Nat.pow 2 i) N) n)) as G4.
    specialize (bcgcount_modmult_rev N (modexp a (PeanoNat.Nat.pow 2 i) N) (modexp (ShorAux.modinv a N) (PeanoNat.Nat.pow 2 i) N) n H1) as G5.
    lia.
  }
  unfold controlled_powers.
  specialize (ugcount_leq_bcgcount (controlled_powers' f m m)) as T1.
  specialize (bcgcount_controlled_powers' m f m imm H0 H2) as T2.
  lia.
Qed.
