Require Export VectorStates.
Require Export Equivalences.

Local Open Scope ucom_scope.

(**********************)
(** Unitary Programs **)
(**********************)
(* Helper function. *)
Definition bitwise_xor n x y := 
  let n1f := nat_to_funbool n x in
  let n2f := nat_to_funbool n y in
  funbool_to_nat n (fun i => xorb (n1f i) (n2f i)).

Definition bitwise_product n x y :=
  product (nat_to_funbool n x) (nat_to_funbool n y) n.

Lemma bitwise_xor_bound : forall (n x y: nat), (bitwise_xor n x y < 2 ^ n)%nat. 
Proof.
  intros.
  unfold bitwise_xor. 
  apply funbool_to_nat_bound.
Qed.

Lemma bitwise_xor_eq: forall (n x: nat), (bitwise_xor n x x = 0)%nat.
Proof.
  intros.
  unfold bitwise_xor.
  erewrite funbool_to_nat_eq.
  2: { intros.
       rewrite xorb_nilpotent.
       reflexivity. }
  rewrite <- (nat_to_funbool_0 n).
 rewrite nat_to_funbool_inverse. 
 reflexivity.
 apply pow_positive. lia.
Qed.

Lemma bitwise_xor_0_l : forall n x,
  (x < 2 ^ n)%nat -> bitwise_xor n 0 x = x.
Proof.
  intros.
  unfold bitwise_xor.
  rewrite nat_to_funbool_0.
  replace (funbool_to_nat n (fun i : nat => false ⊕ nat_to_funbool n x i)) 
    with (funbool_to_nat n (nat_to_funbool n x)).
  apply nat_to_funbool_inverse; auto.
  apply f_equal2; auto.
  apply functional_extensionality.
  intros.
  rewrite xorb_false_l. 
  reflexivity.
Qed.

Lemma bitwise_xor_assoc : forall n x y z,
  bitwise_xor n x (bitwise_xor n y z) = bitwise_xor n (bitwise_xor n x y) z.
Proof.
  intros.
  unfold bitwise_xor.
  apply funbool_to_nat_eq.
  intros.
  rewrite 2 funbool_to_nat_inverse by assumption.
  rewrite <- xorb_assoc.
  reflexivity.
Qed.

Lemma bitwise_xor_comm: forall n x y,
          bitwise_xor n x y = bitwise_xor n y x.
Proof.
  intros.
  unfold bitwise_xor.
  eapply funbool_to_nat_eq.
  intros.
  rewrite <- xorb_comm.
  reflexivity.
Qed.

Lemma bitwise_xor_0_l_strong : forall n x y,
  (y < 2 ^ n)%nat -> bitwise_xor n y x = x -> y = O.
Proof.
  intros.
  assert (bitwise_xor n x (bitwise_xor n y x) = bitwise_xor n x x) by auto.
  rewrite (bitwise_xor_comm _ y) in H1.
  rewrite bitwise_xor_assoc in H1.
  rewrite bitwise_xor_eq in H1.
  rewrite bitwise_xor_0_l in H1 by auto.
  assumption.
Qed.

Lemma bitwise_product_xor_distr : forall n x y z,
  bitwise_product n (bitwise_xor n x y) z =
    (bitwise_product n x z) ⊕ (bitwise_product n y z).
Proof.
  intros.
  unfold bitwise_product. 
  assert (forall m, (n <= m)%nat ->
    product (nat_to_funbool m (bitwise_xor m x y)) (nat_to_funbool m z) n =
    product (nat_to_funbool m x) (nat_to_funbool m z) n
      ⊕ product (nat_to_funbool m y) (nat_to_funbool m z) n).
  { intros.
    induction n.
    reflexivity.
    simpl.
    rewrite IHn by lia.
    unfold bitwise_xor.
    rewrite funbool_to_nat_inverse by lia.
    rewrite andb_comm.
    rewrite andb_xorb_dist.  
    rewrite 2 (andb_comm (nat_to_funbool _ z _)).
    rewrite (xorb_assoc _ _ (xorb _ _)).
    rewrite <- (xorb_assoc _ (product _ _ _) (product _ _ _)).
    rewrite (xorb_comm (andb _ _) (product _ _ _)).
    repeat rewrite xorb_assoc.
    reflexivity. }
  apply H.
  lia.
Qed.

Definition to_injective n s f x :=
  let y := bitwise_xor n x s in 
  if (x <? y)%nat then f x else ((2 ^ n)%nat + f x)%nat.

Lemma to_injective_is_injective (n s:nat) (f:nat -> nat) : 
   (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> bitwise_xor n x y = s \/ x = y) ->
   (forall x y, (x < (2 ^ n))%nat -> (y < (2 ^ n))%nat -> 
        to_injective n s f x = to_injective n s f y -> x = y).
Proof.
  intros.
  unfold to_injective in H6.
  bdestruct (x <? bitwise_xor n x s).
  bdestruct (y <? bitwise_xor n y s).
  rewrite H3 in H6; auto.
  destruct H6; auto.
  rewrite <- H6 in H7.
  rewrite bitwise_xor_assoc, bitwise_xor_eq in H7.
  rewrite bitwise_xor_0_l in H7; auto.
  rewrite <- H6 in H8.
  rewrite (bitwise_xor_comm n x), bitwise_xor_assoc, bitwise_xor_eq in H8.
  rewrite bitwise_xor_0_l in H8; auto.
  lia.
  assert (f x < 2 ^ n)%nat by auto.
  lia.
  bdestruct (y <? bitwise_xor n y s).
  assert (f y < 2 ^ n)%nat by auto.
  lia.
  assert (f x = f y)%nat by lia.
  rewrite H3 in H9; auto.
  destruct H9; auto.
  rewrite <- H9 in H7.
  rewrite bitwise_xor_assoc, bitwise_xor_eq in H7.
  rewrite bitwise_xor_0_l in H7; auto.
  rewrite <- H9 in H8.
  rewrite (bitwise_xor_comm n x), bitwise_xor_assoc, bitwise_xor_eq in H8.
  rewrite bitwise_xor_0_l in H8; auto.
  lia.
Qed.

Lemma bitwise_xor_bijective: forall (n s: nat), 
   (n > 0)%nat -> (s < 2 ^ n)%nat ->
   weak_finite_bijection (2 ^ n) (fun i => bitwise_xor n i s).
Proof.
  intros.
  split. 
  intros.
  apply bitwise_xor_bound.
  exists (fun i => bitwise_xor n i s).
  repeat split; intros.
  apply bitwise_xor_bound.
  rewrite <- bitwise_xor_assoc, bitwise_xor_eq, bitwise_xor_comm.
  apply bitwise_xor_0_l.
  assumption.
  rewrite <- bitwise_xor_assoc, bitwise_xor_eq, bitwise_xor_comm.
  apply bitwise_xor_0_l.
  assumption.
Qed.

Lemma bitwise_xor_vsum_reorder: forall (n m s :nat) (f:nat -> nat) a, 
  (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
  vsum (2 ^ n) (fun i : nat => (a i) .* basis_vector m (f (bitwise_xor n i s))) =
  vsum (2 ^ n) (fun i : nat => (a (bitwise_xor n i s)) .* basis_vector m (f i)).
Proof.
  intros.
  rewrite vsum_reorder with (f0:= (fun i => bitwise_xor n i s)).
  erewrite vsum_eq.
  2: { intros.
       rewrite (bitwise_xor_comm _ (bitwise_xor _ _ _)).
       rewrite (bitwise_xor_comm _ _ s) at 2.
       rewrite bitwise_xor_assoc, bitwise_xor_eq, bitwise_xor_0_l.
       reflexivity.
       assumption. }
  reflexivity.
  apply bitwise_xor_bijective; auto.
Qed.



Definition MAJ {dim} a b c : base_ucom dim := CNOT c b ; CNOT c a ; CCX a b c.

Definition MAJ_neg {dim} a b c : base_ucom dim := CCX a b c; CNOT c a ; CNOT c b.

Definition UMA {dim} a b c : base_ucom dim := CCX a b c ; CNOT c a ; CNOT a b.


Fixpoint adder' dim n : base_ucom (2 * dim + 2) :=
  match n with
  | 0 => CNOT (2 * dim) (2 * dim + 1) 
  | S n' => (MAJ (dim - n) ((dim - n)+1) ((dim - n)+2); adder' dim n' ; UMA (dim - n) ((dim - n)+1) ((dim - n)+2))
  end.
Definition adder n := adder' n n.


Fixpoint comparator' dim n : base_ucom (2 * dim + 2) :=
  match n with
  | 0 => CNOT (2 * dim) (2 * dim + 1) 
  | S n' => (MAJ (dim - n) ((dim - n)+1) ((dim - n)+2);
              comparator' dim n' ; MAJ_neg (dim - n) ((dim - n)+1) ((dim - n)+2))
  end.
Definition comparator n := adder' n n.

Definition nat_to_binlist_rev n := rev (nat_to_binlist' n).

Compute (1 / 2)%nat.

Definition double_vector (n:nat) (x:Vector n) : (Vector (2 * n)) :=
    fun i j => if i mod 2 =? 0 then x (i / 2)%nat j else x ((i-1) / 2)%nat j.


(* how to define x + x? *)
Definition add_two (n x:nat) := @Mmult (2 ^ (2 * n + 2)) (2 ^ (2 * n + 2)) 1
                         (uc_eval (adder n)) (∣0⟩ ⊗ (double_vector n (basis_vector (2 ^ n) x)) ⊗ ∣0⟩).




