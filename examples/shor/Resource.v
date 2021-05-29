Require Import RCIR Psatz AltGateSet.

Open Scope nat_scope.
Fixpoint ugcount (c : ucom U) : nat :=
  match c with
  | useq c1 c2 => (ugcount c1) + (ugcount c2)
  | _ => 1
  end.

Lemma control'_more_fuel :
  forall c n f,
    (fuel c < f) ->
    control' n c f = control n c.
Proof.
  induction c; intros; unfold control in *.
  - simpl in H. destruct f. lia.
    remember (fuel (c1 >> c2)) as fseq.
    simpl. rewrite IHc1, IHc2 by lia.
    symmetry.
    rewrite IHc1, IHc2 by (subst; simpl; lia).
    easy.
  - simpl in H. destruct u, f; try lia; try easy.
    + simpl. simpl in H. unfold fuel_CU1 in H.
      do 5 (destruct f; try lia). easy.
    + simpl. simpl in H. unfold fuel_CSWAP in H.
      do 3 (destruct f; try lia). easy.
    + simpl. simpl in H. unfold fuel_CCX in H.
      do 23 (destruct f; try lia). easy.
Qed.

Definition gcCC4X := 191.

Lemma ugcount_control :
  forall c n, ugcount (control n c) <= gcCC4X * ugcount c.
Proof.
  induction c; intros.
  - remember (gcCC4X * ugcount (c1 >> c2)) as rhs.
    unfold control. remember (fuel (c1 >> c2)) as f.
    simpl. simpl in Heqf.
    rewrite Heqrhs. 
    do 2 rewrite control'_more_fuel by lia.
    specialize (IHc1 n).
    specialize (IHc2 n).
    replace (ugcount (c1 >> c2)) with (ugcount c1 + ugcount c2) by easy.
    lia.
  - simpl. unfold control.
    destruct u; repeat (destruct l; simpl; try easy; try lia).
Qed.

Opaque gcCC4X.

(* Can be extended to C4X, CSWAP. But it is not used in Shor's so ignored here. *)
Fixpoint bcgcount (c : bccom) : nat :=
  match c with
  | bcseq c1 c2 => (bcgcount c1) + (bcgcount c2)
  | bccont n (bcx q) => 1
  | bccont n1 (bccont n2 (bcx q)) => 1
  | bccont n1 (bccont n2 (bccont n3 (bcx q))) => 1
  | bccont n c => gcCC4X * (bcgcount c)
  | _ => 1
  end.

Lemma ugcount_leq_bcgcount :
  forall c, ugcount (bc2ucom c) <= bcgcount c.
Proof.
  induction c; try (simpl; lia).
  destruct c. Local Transparent gcCC4X. 1-3 : simpl in *; lia.
  2: { replace (bc2ucom (bccont n (c1; c2)%bccom)) with (control n (bc2ucom c1 >> bc2ucom c2)) by easy.
       assert (ugcount (control n (bc2ucom c1 >> bc2ucom c2)) <= gcCC4X * ugcount (bc2ucom (c1; c2)%bccom)) by apply ugcount_control.
       replace (bcgcount (bccont n (c1; c2)%bccom)) with (gcCC4X * bcgcount (c1; c2)%bccom) by easy.
       nia.
  }
  destruct c.
  Local Opaque gcCC4X. simpl in *. Local Transparent gcCC4X. unfold gcCC4X. nia.
  Local Opaque gcCC4X. simpl in *. Local Transparent gcCC4X. unfold gcCC4X. nia.
  Local Opaque gcCC4X. simpl in *. Local Transparent gcCC4X. unfold gcCC4X. nia.
  2: { replace (bc2ucom (bccont n (bccont n0 (c1; c2)%bccom))) with (control n (bc2ucom (bccont n0 (c1; c2)%bccom))) by easy.
       specialize (ugcount_control (bc2ucom (bccont n0 (c1; c2)%bccom)) n) as G.
       replace (bcgcount (bccont n (bccont n0 (c1; c2)%bccom))) with (gcCC4X * bcgcount (bccont n0 (c1; c2)%bccom)).
       nia.
       Local Opaque gcCC4X. simpl. lia. Local Transparent gcCC4X.
  }
  destruct c.
  Local Opaque gcCC4X. simpl in *. Local Transparent gcCC4X. unfold gcCC4X. nia.
  Local Opaque gcCC4X. simpl in *. Local Transparent gcCC4X. unfold gcCC4X. nia.
  Local Opaque gcCC4X. simpl in *. Local Transparent gcCC4X. unfold gcCC4X. nia.
  2: { replace (bc2ucom (bccont n (bccont n0 (bccont n1 (c1; c2)%bccom)))) with (control n (bc2ucom (bccont n0 (bccont n1 (c1; c2)%bccom)))) by easy.
       specialize (ugcount_control (bc2ucom (bccont n0 (bccont n1 (c1; c2)%bccom))) n) as G.
       replace (bcgcount (bccont n (bccont n0 (bccont n1 (c1; c2)%bccom)))) with (gcCC4X * bcgcount (bccont n0 (bccont n1 (c1; c2)%bccom))).
       nia.
       Local Opaque gcCC4X. simpl. lia. Local Transparent gcCC4X.
  }
  replace (bc2ucom (bccont n (bccont n0 (bccont n1 (bccont n2 c))))) with (control n (bc2ucom (bccont n0 (bccont n1 (bccont n2 c))))) by easy.
  specialize (ugcount_control (bc2ucom (bccont n0 (bccont n1 (bccont n2 c)))) n) as G.
  replace (bcgcount (bccont n (bccont n0 (bccont n1 (bccont n2 c))))) with (gcCC4X * bcgcount (bccont n0 (bccont n1 (bccont n2 c)))).
  nia.
  Local Opaque gcCC4X. easy.
Qed.

Lemma control_useq :
  forall c1 c2 n, control n (c1 >> c2) = control n c1 >> control n c2.
Proof.
  intros. unfold control.
  remember (fuel (c1 >> c2)) as fseq.
  simpl in Heqfseq. replace (S (Nat.max (fuel c1) (fuel c2))) with (Nat.max (S (fuel c1)) (S (fuel c2))) in Heqfseq by lia.
  remember (S (fuel c1)) as Sf1.
  remember (S (fuel c2)) as Sf2.
  simpl.
  repeat (rewrite control'_more_fuel by lia).
  easy.
Qed.

(*
Lemma ugcount_csplit :
  forall c, ugcount (bc2ucom (csplit c)) = ugcount (bc2ucom c).
Proof.
  destruct c; try (simpl; lia).
  destruct c; try (simpl; lia).
  replace (ugcount (bc2ucom (csplit (bccont n (c1; c2)%bccom)))) with (ugcount (bc2ucom (bccont n c1)) + ugcount (bc2ucom (bccont n c2))) by easy.
  replace (bc2ucom (bccont n (c1; c2)%bccom)) with (control n (bc2ucom c1) >> control n (bc2ucom c2)).
  easy.
  simpl. rewrite control_useq. easy.
Qed.
*)

Lemma bcgcount_pos :
  forall c, bcgcount c > 0.
Proof.
  induction c; simpl; try lia.
  remember (bcgcount c) as f.
  assert (gcCC4X > 0). {
    Local Transparent gcCC4X. unfold gcCC4X. lia. Local Opaque gcCC4X.
  }
  repeat (destruct c; simpl; try lia).
Qed.

Lemma bcgcount_bcelim :
  forall c, bcgcount (bcelim c) <= bcgcount c.
Proof.
  assert (gcCC4X > 190). {
    Local Transparent gcCC4X. unfold gcCC4X. lia. Local Opaque gcCC4X.
  }
  induction c; try (simpl; lia).
  - assert (bcgcount c > 0) by apply bcgcount_pos.
    destruct (bcelim c) eqn:E;
      try (simpl; rewrite E; simpl;
           remember (bcgcount c) as f;
           do 10 (destruct c; simpl; try nia; try easy)).
    + simpl. rewrite E. simpl in *.
      remember (bcgcount b) as fb.
      remember (bcgcount c) as fc.
      do 5 (try (destruct b); try (destruct c); try easy; try (simpl in *; nia)).
    + simpl. rewrite E. simpl in *.
      do 4 (destruct c; try easy; try (simpl in *; nia)).
  - simpl.
    destruct (bcelim c1) eqn:E1;
      destruct (bcelim c2) eqn:E2;
      try (simpl in *; nia).
Qed.
