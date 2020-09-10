Require Export UnitarySem.
Require Import Dirac.

Local Open Scope ucom_scope.
Local Close Scope C_scope.
Local Close Scope R_scope.

(* This file provides abstractions for describing quantum states as vectors.
   - f_to_vec describes classical states as boolean functions
   - basis_vector describes classiacal states as natural numbers
   - vsum describes superposition states
   - vkron describes states as the tensor product of qubits *)

(*******************************)
(**      Classical States     **)
(*******************************)

(* General facts about (nat -> A) functions.

   TODO #1: These lemmas are probably already defined in Coq somewhere.
   TODO #2: For efficiency, instead of using functions indexed by natural
            numbers, we should use vectors/arrays. *)

(* update_at is the same function on lists.
   update is also defined in SF. *)

(* Update the value at one index of a boolean function. *)
Definition update {A} (f : nat -> A) (i : nat) (x : A) :=
  fun j => if j =? i then x else f j.

Lemma update_index_eq : forall {A} (f : nat -> A) i b, (update f i b) i = b.
Proof.
  intros. 
  unfold update.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma update_index_neq : forall {A} (f : nat -> A) i j b, i <> j -> (update f i b) j = f j.
Proof.
  intros. 
  unfold update.
  rewrite eqb_neq; auto.
Qed.

Lemma update_same : forall {A} (f : nat -> A) i b,
  b = f i -> update f i b = f.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold update.
  bdestruct (x =? i); subst; reflexivity.
Qed.

Lemma update_twice_eq : forall {A} (f : nat -> A) i b b',
  update (update f i b) i b' = update f i b'.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold update.
  bdestruct (x =? i); subst; reflexivity.
Qed.  

Lemma update_twice_neq : forall {A} (f : nat -> A) i j b b',
  i <> j -> update (update f i b) j b' = update (update f j b') i b.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold update.
  bdestruct (x =? i); bdestruct (x =? j); subst; easy.
Qed.

Definition shift {A} (f : nat -> A) k := fun i => f (i + k).

Lemma shift_0 : forall {A} (f : nat -> A), shift f 0 = f.
Proof.
  intros A f.
  unfold shift.
  apply functional_extensionality; intro x.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

Lemma shift_plus : forall {A} (f : nat -> A) i j, shift (shift f j) i = shift f (i + j).
Proof.
  intros A f i j.
  unfold shift.
  apply functional_extensionality; intro x.
  rewrite Nat.add_assoc.
  reflexivity.
Qed.

Lemma shift_simplify : forall {A} (f : nat -> A) i j ,
  shift f i j = f (j + i).
Proof. intros. unfold shift. reflexivity. Qed.

(* Convert a boolean function to a vector; examples: 
     f_to_vec 3 f --> I 1 ⊗ ∣ f 0 ⟩ ⊗ ∣ f 1 ⟩ ⊗ | f 2 ⟩ 
     f_to_vec 2 (shift f 2) -->  I 1 ⊗ ∣ f 2 ⟩ ⊗ ∣ f 3 ⟩ 
*)
Local Coercion Nat.b2n : bool >-> nat.
Fixpoint f_to_vec (n : nat) (f : nat -> bool) : Vector (2^n) :=
  match n with 
  | 0 => I 1
  | S n' =>  (f_to_vec n' f) ⊗ ∣ f n' ⟩
  end.

Lemma f_to_vec_WF : forall (n : nat) (f : nat -> bool),
  WF_Matrix (f_to_vec n f).
Proof.
  intros.
  induction n; simpl; try auto with wf_db.
  apply WF_kron; try lia; try assumption.
  destruct (f n); auto with wf_db.
Qed.
Hint Resolve f_to_vec_WF : wf_db.

(* Convert a natural number to a vector *)

Definition basis_vector (n k : nat) : Vector n :=
  fun i j => if (i =? k) && (j =? 0) then C1 else C0.

Lemma basis_vector_WF : forall n i, (i < n)%nat -> WF_Matrix (basis_vector n i).
Proof.
  unfold basis_vector, WF_Matrix.
  intros.
  bdestruct (n <=? x)%nat; bdestruct (1 <=? y)%nat; try lia.
  bdestructΩ (x =? i)%nat. reflexivity.
  bdestructΩ (x =? i)%nat. reflexivity.
  bdestructΩ (y =? 0)%nat. rewrite andb_false_r. reflexivity.
Qed.
Hint Resolve basis_vector_WF : wf_db.

Lemma basis_vector_product_eq : forall d n,
  n < d -> (basis_vector d n)† × basis_vector d n = I 1.
Proof.
  intros. 
  prep_matrix_equality.
  unfold basis_vector, adjoint, Mmult, I.
  bdestruct (x =? y); bdestruct (x <? 1); simpl.
  apply Csum_unique.
  exists n.
  repeat split; auto.
  bdestruct_all; simpl; lca.
  intros i Hi. bdestructΩ (i =? n). lca.
  all: apply Csum_0; intro i; bdestruct_all; simpl; lca.
Qed.

Lemma basis_vector_product_neq : forall d m n,
  (m < d)%nat -> (n < d)%nat -> (m <> n)%nat -> (basis_vector d m)† × basis_vector d n = Zero.
Proof.
  intros.
  prep_matrix_equality.
  unfold basis_vector, adjoint, Mmult, Zero.
  apply Csum_0. 
  intro i; bdestruct_all; lca.
Qed.

Lemma matrix_times_basis_eq : forall m n (A : Matrix m n) i j,
  WF_Matrix A ->
  (A × basis_vector n j) i 0 = A i j.
Proof.
  intros m n A i j WFA.
  unfold basis_vector.
  unfold Mmult.
  bdestruct (j <? n).
  2:{ rewrite Csum_0. rewrite WFA; auto. 
      intros j'. bdestruct (j' =? j); subst; simpl; try lca.
      rewrite WFA by auto. lca. }
  erewrite Csum_unique.
  reflexivity.
  exists j.
  repeat split; trivial.
  rewrite <- 2 beq_nat_refl; simpl; lca.
  intros j' Hj.
  rewrite eqb_neq; auto. simpl. lca.
Qed.  

Lemma equal_on_basis_vectors_implies_equal : forall m n (A B : Matrix m n),
  WF_Matrix A -> 
  WF_Matrix B ->
  (forall k, k < n -> A × (basis_vector n k) = B × (basis_vector n k)) ->
  A = B.
Proof.
  intros m n A B WFA WFB H.
  prep_matrix_equality.
  bdestruct (y <? n). 2: rewrite WFA, WFB; auto.
  rewrite <- matrix_times_basis_eq; trivial.
  rewrite H; trivial.
  rewrite matrix_times_basis_eq; easy.
Qed.

(* f_to_vec and basis_vector allow us to represent the same set of states.
   To prove this we need lemmas about converting between natural numbers
   and their binary representation. *)

(* takes [1;1;0;0] to 3, [0;0;1;0] to 4 *)
Fixpoint binlist_to_nat (l : list bool) : nat :=
  match l with
  | [] => 0
  | b :: l' => b + 2 * binlist_to_nat l'
  end.

Fixpoint funbool_to_list (len : nat) (f : nat -> bool) :=
  match len with
  | O => []
  | S len' => f len' :: funbool_to_list len' f
  end.

Definition funbool_to_nat (len : nat) (f : nat -> bool) :=
  binlist_to_nat (funbool_to_list len f).

Lemma funbool_to_nat_bound : forall n f, (funbool_to_nat n f < 2 ^ n)%nat.
Proof.
  intros n f.
  unfold funbool_to_nat.
  induction n; simpl. lia.
  destruct (f n); simpl; lia.
Qed.

Lemma funbool_to_nat_eq : forall n f f',
  (forall x, x < n -> f x = f' x)%nat ->
  funbool_to_nat n f = funbool_to_nat n f'.
Proof.
  intros.
  unfold funbool_to_nat.
  apply f_equal.
  induction n.
  reflexivity.
  simpl.
  rewrite H by lia.
  rewrite IHn; auto.
Qed.

Local Opaque Nat.mul.
Lemma funbool_to_nat_shift : forall n f k, (k < n)%nat ->
  funbool_to_nat n f  = (2 ^ (n - k) * funbool_to_nat k f + funbool_to_nat (n - k) (shift f k))%nat.
Proof.
  intros.
  unfold shift, funbool_to_nat.
  destruct n; try lia.
  induction n.
  destruct k; try lia.
  replace (1 - 0)%nat with (S O) by lia; simpl. reflexivity.
  remember (S n) as n'.
  replace (S n' - k)%nat with (S (n' - k))%nat by lia.
  simpl.
  replace (n' - k + k)%nat with n' by lia.
  bdestruct (n' =? k).
  subst.
  replace (S n - S n)%nat with O by lia; simpl.
  lia.
  rewrite IHn; lia.
Qed.
Local Transparent Nat.mul.

(* rewrite f_to_vec as basis_vector *)
Lemma basis_f_to_vec : forall n f,
  f_to_vec n f = basis_vector (2^n) (funbool_to_nat n f).
Proof.
  intros.
  induction n.
  - unfold funbool_to_nat; simpl.
    unfold basis_vector.
    unfold I.
    prep_matrix_equality.
    bdestruct (x =? 0); bdestruct (x =? y); subst; simpl; trivial.
    rewrite eqb_neq; auto.
    bdestructΩ (y <? 1); easy.
  - simpl.
    rewrite IHn.
    unfold funbool_to_nat; simpl.
    unfold basis_vector.
    prep_matrix_equality. unfold kron. 
    rewrite Nat.div_1_r.
    bdestruct (y =? 0).
    2: rewrite 2 andb_false_r; lca.
    rewrite 2 andb_true_r.
    rewrite Nat.mod_1_r, Nat.add_0_r.
    remember (binlist_to_nat (funbool_to_list n f)) as z.
    destruct (f n).
    + specialize (Nat.div_mod x 2) as DM.
      rewrite <- Nat.bit0_mod in *.
      destruct (Nat.testbit x 0); bdestruct (x / 2 =? z);
        simpl in *; bdestruct (x =? S (z + z)); try lia; try lca.
    + specialize (Nat.div_mod x 2) as DM.
      rewrite <- Nat.bit0_mod in *.
      destruct (Nat.testbit x 0); bdestruct (x / 2 =? z);
        simpl in *; bdestruct (x =? (z + z)); try lia; try lca.
Qed.

Fixpoint incr_bin (l : list bool) :=
  match l with
  | []        => [true]
  | false :: t => true :: t
  | true :: t  => false :: (incr_bin t)
  end.

Fixpoint nat_to_binlist' n :=
  match n with
  | O    => []
  | S n' => incr_bin (nat_to_binlist' n')
  end.
Definition nat_to_binlist len n := 
  let l := nat_to_binlist' n in
  l ++ (repeat false (len - length l)).

Fixpoint list_to_funbool len (l : list bool) : nat -> bool :=
  match l with
  | []    => fun _ => false
  | h :: t => update (list_to_funbool (len - 1)%nat t) (len - 1) h
  end.

Definition nat_to_funbool len n : nat -> bool :=
  list_to_funbool len (nat_to_binlist len n).

Lemma binlist_to_nat_append : forall l1 l2,
  binlist_to_nat (l1 ++ l2) = 
    (binlist_to_nat l1 +  2 ^ (length l1) * binlist_to_nat l2)%nat.
Proof. intros l1 l2. induction l1; simpl; lia. Qed.

Lemma binlist_to_nat_false : forall n, binlist_to_nat (repeat false n) = O.
Proof. induction n; simpl; lia. Qed.

Lemma binlist_to_nat_true : forall n, binlist_to_nat (repeat true n) = 2^n - 1.
Proof.
  induction n; simpl; trivial.
  rewrite IHn. clear.
  repeat rewrite Nat.add_0_r.
  rewrite <- Nat.add_succ_l.
  replace (S (2 ^ n - 1)) with (1 + (2 ^ n - 1)) by easy.
  rewrite <- le_plus_minus.
  rewrite <- Nat.add_sub_assoc.
  reflexivity.
  all: induction n; simpl; try lia.
Qed.

Lemma nat_to_binlist_eq_nat_to_binlist' : forall len n, 
  binlist_to_nat (nat_to_binlist len n) = binlist_to_nat (nat_to_binlist' n).
Proof.
  intros len n.
  unfold nat_to_binlist. 
  rewrite binlist_to_nat_append.
  rewrite binlist_to_nat_false. 
  lia.
Qed.

Lemma nat_to_binlist_inverse : forall len n,
  binlist_to_nat (nat_to_binlist len n) = n.
Proof.
  intros len n.
  rewrite nat_to_binlist_eq_nat_to_binlist'.
  induction n; simpl.
  reflexivity.
  assert (H : forall l, binlist_to_nat (incr_bin l) = S (binlist_to_nat l)).
  { clear.
    induction l; simpl.
    reflexivity.
    destruct a; simpl; try reflexivity.
    rewrite IHl. lia. }
  rewrite H, IHn.
  reflexivity.
Qed.

Lemma nat_to_binlist_corr : forall l n,
   nat_to_binlist' n = l ->
   binlist_to_nat l = n. (* Lemma this *)
Proof.
  intros.
  rewrite <- H.
  erewrite <- (nat_to_binlist_eq_nat_to_binlist' n n).
  rewrite nat_to_binlist_inverse.
  reflexivity.
Qed.

Lemma incr_bin_true_length : forall l,
  Forall (fun b => b = true) l ->
  length (incr_bin l) = S (length l).
Proof.
  intros.
  induction l; trivial.
  - inversion H; subst.
    simpl in *.
    rewrite IHl; easy.
Qed.

Lemma incr_bin_false_length : forall l,
  Exists (fun b => b <> true) l ->
  length (incr_bin l) = length l.
Proof.
  intros.
  induction l; inversion H; subst.
  - destruct a; simpl; easy.
  - destruct a; simpl; trivial.
    rewrite IHl; easy.
Qed.

Lemma all_true_repeat : forall l,
  Forall (fun b : bool => b = true) l ->
  l = repeat true (length l).
Proof.
  intros.
  induction l; simpl; trivial.
  inversion H; subst.
  rewrite <- IHl; easy.
Qed.  
  
Lemma nat_to_binlist_length' : forall k n,
    n < 2 ^ k -> length (nat_to_binlist' n) <= k.
Proof.
  intros.
  induction n; simpl; try lia.
  destruct (Forall_Exists_dec (fun b => b = true) (fun b => bool_dec b true)
                              (nat_to_binlist' n)) as [ALL | NALL].
  - rewrite incr_bin_true_length; trivial.
    apply le_lt_eq_dec in IHn; [| lia].
    destruct IHn; try lia.
    exfalso.
    apply all_true_repeat in ALL.
    apply nat_to_binlist_corr in ALL.
    rewrite binlist_to_nat_true in ALL.
    rewrite e in ALL.
    lia.
  - rewrite incr_bin_false_length; trivial.
    apply IHn; lia.
Qed.

Lemma nat_to_binlist_length : forall len n,
  (n < 2 ^ len)%nat -> length (nat_to_binlist len n) = len.
Proof.
  intros len n Hlen.
  unfold nat_to_binlist.
  rewrite app_length, repeat_length. 
  bdestruct (n =? 0); subst; simpl. lia.
  apply nat_to_binlist_length' in Hlen.
  lia.
Qed.

Lemma funbool_to_list_update_oob : forall f dim b n, (dim <= n)%nat ->
  funbool_to_list dim (update f n b) = funbool_to_list dim f.
Proof.
  intros.
  induction dim; trivial.
  simpl.
  rewrite IHdim by lia.
  unfold update.
  bdestruct (dim =? n); try lia.
  reflexivity.
Qed.

Lemma list_to_funbool_inverse : forall len l,
  length l = len ->
  funbool_to_list len (list_to_funbool len l) = l.
Proof.
  intros len l.
  generalize dependent len.
  induction l; intros len Hlen.
  simpl in Hlen; rewrite <- Hlen.
  simpl. reflexivity.
  simpl in Hlen; rewrite <- Hlen.
  simpl.
  replace (length l - 0)%nat with (length l) by lia.
  rewrite update_index_eq.
  rewrite funbool_to_list_update_oob by lia.
  rewrite IHl; reflexivity.
Qed.

Lemma nat_to_funbool_inverse : forall len n, 
  (n < 2 ^ len)%nat -> funbool_to_nat len (nat_to_funbool len n) = n.
Proof.
  intros.
  unfold nat_to_funbool, funbool_to_nat.
  rewrite list_to_funbool_inverse.
  apply nat_to_binlist_inverse.
  apply nat_to_binlist_length.
  assumption.
Qed.

Local Opaque Nat.mul.
Lemma nat_to_binlist'_even : forall n, (n > 0)%nat -> 
  nat_to_binlist' (2 * n) = false :: nat_to_binlist' n.
Proof.
  intros n Hn. 
  destruct n; try lia. clear.
  induction n.
  rewrite Nat.mul_1_r. simpl. reflexivity. 
  replace (2 * S (S n))%nat with (S (S (2 * S n))) by lia.
  simpl. rewrite IHn. reflexivity.
Qed.

Lemma nat_to_binlist'_odd : forall n,
  nat_to_binlist' (2 * n + 1) = true :: nat_to_binlist' n.
Proof.
  induction n.
  rewrite Nat.mul_0_r, Nat.add_0_l. simpl. reflexivity. 
  replace (2 * S n + 1)%nat with (S (S (2 * n + 1))) by lia.
  simpl. rewrite IHn. reflexivity.
Qed.

Lemma binlist_to_nat_inverse : forall l n i, 
  list_to_funbool n (nat_to_binlist' (binlist_to_nat l)) i = list_to_funbool n l i.
Proof.
  intros.
  generalize dependent n.
  induction l.
  reflexivity.
  intros.
  simpl.
  destruct a; simpl Nat.b2n. 
  rewrite Nat.add_comm.
  rewrite nat_to_binlist'_odd.
  simpl. unfold update.
  rewrite IHl. reflexivity.
  rewrite Nat.add_0_l.
  bdestruct (binlist_to_nat l =? 0).
  rewrite H in *.
  rewrite Nat.mul_0_r.
  simpl.
  unfold update.
  rewrite <- IHl.
  simpl.
  bdestruct_all; reflexivity.
  rewrite nat_to_binlist'_even by lia.
  simpl. unfold update.
  rewrite IHl. reflexivity.
Qed.

Lemma list_to_funbool_repeat_false : forall n i,
  list_to_funbool n (repeat false n) i = false.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl. rewrite Nat.sub_0_r.
  unfold update.
  rewrite IHn.
  bdestruct_all; reflexivity.
Qed.

Lemma funbool_to_nat_0 : forall n f, 
  funbool_to_nat n f = O -> forall i, (i < n)%nat -> f i = false.
Proof.
  intros.
  induction n.
  lia.
  intros.
  unfold funbool_to_nat in *. 
  simpl in *.
  destruct (f n) eqn:fn; simpl in *.
  inversion H.
  bdestruct (i =? n). subst. 
  assumption.
  apply IHn; lia.
Qed.

Lemma funbool_to_nat_inverse : forall len f i, (i < len)%nat -> 
  nat_to_funbool len (funbool_to_nat len f) i = f i.
Proof.
  intros.
  assert (list_to_funbool_append1 : forall l1 l2,
            (i >= length l2)%nat ->
            (len <= length l1 + length l2)%nat ->
            list_to_funbool len (l1 ++ l2) i = list_to_funbool len l1 i).
  { intros.
    generalize dependent len.
    induction l1; intros; simpl in *.
    generalize dependent len.
    induction l2.
    reflexivity.
    intros.
    simpl in *. 
    unfold update.  
    bdestructΩ (i =? len - 1).
    unfold update.
    bdestruct (i =? len - 1).
    reflexivity.
    apply IHl1; lia. }
  assert (list_to_funbool_append2 : forall l1 l2,
            (i < length l2)%nat ->
            (len >= length l1 + length l2)%nat ->
            list_to_funbool len (l1 ++ l2) i = 
              list_to_funbool (len - length l1) l2 i).
  { clear.
    intros.
    generalize dependent len.
    induction l1; intros; simpl in *.
    rewrite Nat.sub_0_r.
    reflexivity.
    unfold update.
    bdestructΩ (i =? len - 1).
    rewrite IHl1 by lia.
    replace (len - 1 - length l1)%nat with (len - S (length l1))%nat by lia.
    reflexivity. }
  unfold nat_to_funbool, funbool_to_nat, nat_to_binlist.
  remember (binlist_to_nat (funbool_to_list len f)) as n.
  bdestructΩ (len - length (nat_to_binlist' n) <=? i).
  rewrite list_to_funbool_append1.
  all: try rewrite repeat_length; try lia.
  subst.
  rewrite binlist_to_nat_inverse.
  clear - H.
  induction len.
  lia.
  simpl.
  rewrite Nat.sub_0_r.
  bdestruct (i =? len). subst.
  rewrite update_index_eq. 
  reflexivity.
  rewrite update_index_neq by lia.
  rewrite IHlen by lia.
  reflexivity.
  rewrite list_to_funbool_append2.
  all: try rewrite repeat_length; try lia.
  assert (f i = false).
  { subst.
    clear - H0.
    induction len.
    simpl in H0. lia.
    remember (binlist_to_nat (funbool_to_list (S len) f)) as n.
    bdestruct (n =? 0).
    subst. rewrite H in *.
    eapply funbool_to_nat_0. apply H. 
    lia.
    apply IHlen.
    subst. 
    simpl in *.
    destruct (f len); simpl Nat.b2n in *.
    rewrite Nat.add_comm in H0.
    rewrite nat_to_binlist'_odd in H0.
    simpl in H0. lia.
    rewrite Nat.add_0_l in *.
    rewrite nat_to_binlist'_even in H0 by lia.
    simpl in H0. lia. }
  rewrite list_to_funbool_repeat_false.
  rewrite H1.
  reflexivity.
Qed.
Local Transparent Nat.mul.

(* rewrite basis_vector as f_to_vec *)
Lemma basis_f_to_vec_alt : forall len n, (n < 2 ^ len)%nat -> 
  basis_vector (2 ^ len) n = f_to_vec len (nat_to_funbool len n).
Proof.
  intros.
  rewrite basis_f_to_vec.
  rewrite nat_to_funbool_inverse; auto.
Qed.

(* allows us to prove equivalence of unitary programs using 
   vector state reasoning *)
Lemma equal_on_basis_states_implies_equal : forall {dim} (A B : Square (2 ^ dim)),
  WF_Matrix A -> 
  WF_Matrix B ->
  (forall f, A × (f_to_vec dim f) = B × (f_to_vec dim f)) ->
  A = B.
Proof.
  intros dim A B WFA WFB H.
  apply equal_on_basis_vectors_implies_equal; trivial.
  intros k Lk.
  rewrite basis_f_to_vec_alt; auto.
Qed.

Lemma f_to_vec_update_oob : forall (n : nat) (f : nat -> bool) (i : nat) (b : bool),
  n <= i -> f_to_vec n (update f i b) = f_to_vec n f.
Proof.
  intros.
  induction n; simpl; try reflexivity.
  rewrite <- IHn by lia.
  unfold update.
  bdestructΩ (n =? i).  
  reflexivity.
Qed.

Lemma f_to_vec_shift_update_oob : forall (n : nat) (f : nat -> bool) (i j : nat) (b : bool),
  j + n <= i \/ i < j -> 
  f_to_vec n (shift (update f i b) j) = f_to_vec n (shift f j).
Proof.
  intros. destruct H.
  - induction n; simpl; try reflexivity.
    rewrite <- IHn by lia.
    unfold shift, update.
    bdestructΩ (n + j =? i).
    reflexivity.
  - induction n; simpl; try reflexivity.
    rewrite <- IHn by lia.
    unfold shift, update.
    bdestructΩ (n + j =? i).
    reflexivity.
Qed.

Lemma f_to_vec_split : forall (base n i : nat) (f : nat -> bool),
  i < n ->
  f_to_vec n f = (f_to_vec i f) ⊗ ∣ f i ⟩ ⊗ (f_to_vec (n - 1 - i) (shift f (i + 1))).
Proof.
  intros.
  induction n.
  - contradict H. lia.
  - bdestruct (i =? n).
    + subst.
      replace (S n - 1 - n)%nat with O by lia.
      simpl. Msimpl.
      reflexivity.
    + assert (i < n)%nat by lia.
      specialize (IHn H1).
      replace (S n - 1 - i)%nat with (S (n - 1 - i))%nat by lia.
      simpl.
      rewrite IHn.
      restore_dims; repeat rewrite kron_assoc. 
      unfold shift; simpl.
      replace (n - 1 - i + (i + 1))%nat with n by lia.
      reflexivity.
Qed.

(* lemmas to describe the action of various gates on f_to_vec states *)

Lemma f_to_vec_X : forall (n i : nat) (f : nat -> bool),
  i < n ->
  (uc_eval (X i)) × (f_to_vec n f) 
      = f_to_vec n (update f i (¬ (f i))).
Proof.
  intros.
  autorewrite with eval_db.
  rewrite (f_to_vec_split 0 n i f H). 
  simpl; replace (n - 1 - i) with (n - (i + 1)) by lia.
  repad. 
  Msimpl.
  rewrite (f_to_vec_split 0 (i + 1 + x) i) by lia.
  rewrite f_to_vec_update_oob by lia.
  rewrite f_to_vec_shift_update_oob by lia.
  rewrite update_index_eq. 
  replace (i + 1 + x - 1 - i) with x by lia.
  destruct (f i); simpl; autorewrite with ket_db; reflexivity.
Qed.

Lemma f_to_vec_CNOT : forall (n i j : nat) (f : nat -> bool),
  i < n -> j < n -> i <> j ->
  (uc_eval (SQIR.CNOT i j)) × (f_to_vec n f) 
      = f_to_vec n (update f j (f j ⊕ f i)).
Proof.
  intros.
  autorewrite with eval_db.
  repad.
  - repeat rewrite (f_to_vec_split 0 (i + (1 + d + 1) + x) i) by lia.
    rewrite f_to_vec_update_oob by lia.
    rewrite update_index_neq by lia.
    repeat rewrite (f_to_vec_split (0 + i + 1) (i + (1 + d + 1) + x - 1 - i) d) by lia.
    repeat rewrite shift_plus.
    replace (i + (1 + d + 1) + x - 1 - i - 1 - d) with x by lia.
    repeat rewrite f_to_vec_shift_update_oob by lia.
    repeat rewrite shift_simplify. 
    replace (d + (i + 1)) with (i + 1 + d) by lia.
    rewrite update_index_eq.
    distribute_plus.  
    restore_dims.
    repeat rewrite <- kron_assoc.
    destruct (f i); destruct (f (i + 1 + d)); simpl; Msimpl.
    all: autorewrite with ket_db; reflexivity.
  - repeat rewrite (f_to_vec_split 0 (j + (1 + d + 1) + x0) j); try lia.
    rewrite f_to_vec_update_oob by lia.
    rewrite update_index_eq.
    repeat rewrite (f_to_vec_split (j + 1) (j + (1 + d + 1) + x0 - 1 - j) d); try lia.
    repeat rewrite shift_plus.
    repeat rewrite f_to_vec_shift_update_oob by lia.
    repeat rewrite shift_simplify. 
    replace (d + (j + 1)) with (j + 1 + d) by lia.
    rewrite update_index_neq by lia.
    replace (j + (1 + d + 1) + x0 - 1 - j - 1 - d) with x0 by lia.
    distribute_plus.  
    restore_dims.
    repeat rewrite <- kron_assoc.
    destruct (f j); destruct (f (j + 1 + d)); simpl; Msimpl.
    all: autorewrite with ket_db; reflexivity.
Qed.    

Local Transparent SWAP.
Lemma f_to_vec_SWAP : forall (n i j : nat) (f : nat -> bool),
  i < n -> j < n -> i <> j ->
  uc_eval (SWAP i j) × (f_to_vec n f) = 
    f_to_vec n (update (update f j (f i)) i (f j)).
Proof.
  intros n i j f ? ? ?.
  unfold SWAP; simpl.
  repeat rewrite Mmult_assoc.
  rewrite 3 f_to_vec_CNOT by auto.
  repeat rewrite update_index_eq.
  repeat rewrite update_index_neq by lia.
  repeat rewrite update_index_eq.
  replace ((f j ⊕ f i) ⊕ (f i ⊕ (f j ⊕ f i))) with (f i).
  replace (f i ⊕ (f j ⊕ f i)) with (f j).
  rewrite update_twice_neq by auto.
  rewrite update_twice_eq.
  reflexivity.
  all: destruct (f i); destruct (f j); auto.
Qed.
Local Opaque SWAP.
                                  
Definition b2R (b : bool) : R := if b then 1%R else 0%R.
Local Coercion b2R : bool >-> R.

Lemma phase_shift_on_basis_state : forall (θ : R) (b : bool),
  phase_shift θ × ∣ b ⟩ = (Cexp (b * θ)) .* ∣ b ⟩.
Proof.
  intros.
  destruct b; solve_matrix; autorewrite with R_db.
  reflexivity.
  rewrite Cexp_0; reflexivity.
Qed.

Lemma f_to_vec_Rz : forall (n i : nat) (θ : R) (f : nat -> bool),
  (i < n)%nat ->
  (uc_eval (SQIR.Rz θ i)) × (f_to_vec n f) =
    (Cexp ((f i) * θ)) .* f_to_vec n f.
Proof.
  intros.
  autorewrite with eval_db.
  rewrite (f_to_vec_split 0 n i f H). 
  simpl; replace (n - 1 - i)%nat with (n - (i + 1))%nat by lia.
  repad. 
  Msimpl.
  rewrite phase_shift_on_basis_state.
  rewrite Mscale_kron_dist_r.
  rewrite Mscale_kron_dist_l.
  reflexivity.
Qed.

Local Open Scope C_scope.
Local Open Scope R_scope.
Lemma hadamard_on_basis_state : forall (b : bool),
  hadamard × ∣ b ⟩ = /√2 .* (∣ 0 ⟩ .+ (Cexp (b * PI)) .* ∣ 1 ⟩).
Proof.
  intros.
  destruct b; solve_matrix; autorewrite with R_db Cexp_db; lca.
Qed.

Lemma f_to_vec_H : forall (n i : nat) (f : nat -> bool),
  (i < n)%nat ->
  (uc_eval (SQIR.H i)) × (f_to_vec n f) 
      = /√2 .* ((f_to_vec n (update f i false)) .+ (Cexp ((f i) * PI)) .* f_to_vec n (update f i true)).
Proof.
  intros.
  autorewrite with eval_db.
  rewrite (f_to_vec_split 0 n i f H). 
  simpl; replace (n - 1 - i)%nat with (n - (i + 1))%nat by lia.
  repad. 
  Msimpl.
  rewrite hadamard_on_basis_state.
  rewrite Mscale_kron_dist_r, Mscale_kron_dist_l.
  rewrite kron_plus_distr_l, kron_plus_distr_r.
  rewrite Mscale_kron_dist_r, Mscale_kron_dist_l.
  rewrite 2 (f_to_vec_split 0 (i + 1 + x) i _) by lia.
  replace (i + 1 + x - 1 - i)%nat with x by lia.
  simpl.
  rewrite 2 update_index_eq.
  repeat rewrite f_to_vec_update_oob by lia.
  repeat rewrite f_to_vec_shift_update_oob by lia.
  reflexivity.
Qed.
Local Close Scope C_scope.
Local Close Scope R_scope.

(* some facts about projections -- may move to another file *)

(* Projector onto the space where qubit q is in classical state b. *)
Definition proj q dim (b : bool) := @pad 1 q dim (∣ b ⟩ × (∣ b ⟩)†).

Lemma WF_proj : forall q dim b, WF_Matrix (proj q dim b).
Proof. intros. unfold proj, pad. bdestruct_all; destruct b; auto with wf_db. Qed.
Hint Resolve WF_proj : wf_db.

Lemma f_to_vec_proj_eq : forall f q n b,
  q < n -> f q = b -> 
  proj q n b × (f_to_vec n f) = f_to_vec n f.
Proof.
  intros f q n b ? ?.
  rewrite (f_to_vec_split 0 n q) by lia. 
  replace (n - 1 - q)%nat with (n - (q + 1))%nat by lia.
  unfold proj, pad.
  gridify. 
  do 2 (apply f_equal2; try reflexivity). 
  destruct (f q); solve_matrix.
Qed.

Lemma f_to_vec_proj_neq : forall f q n b,
  q < n -> f q <> b ->
  proj q n b × (f_to_vec n f) = Zero.
Proof.
  intros f q n b ? H.
  rewrite (f_to_vec_split 0 n q) by lia. 
  replace (n - 1 - q)%nat with (n - (q + 1))%nat by lia.
  unfold proj, pad.
  gridify. 
  destruct (f q); destruct b; try easy; lma.
Qed.

Lemma proj_commutes_1q_gate : forall dim u q n b,
  q <> n ->
  proj q dim b × ueval_r dim n u = ueval_r dim n u × proj q dim b. 
Proof.
  intros dim u q n b neq.
  dependent destruction u; simpl.
  unfold proj, pad.
  gridify; trivial.
  all: destruct b; auto with wf_db.
Qed.

Lemma proj_commutes_2q_gate : forall dim q n1 n2 b,
  q <> n1 -> q <> n2 ->
  proj q dim b × ueval_cnot dim n1 n2 = ueval_cnot dim n1 n2 × proj q dim b. 
Proof.
  intros dim q n1 n2 b neq1 neq2.
  unfold proj, ueval_cnot, pad.
  gridify; trivial.
  all: destruct b; auto with wf_db.
Qed.

Lemma proj_commutes : forall dim q1 q2 b1 b2,
  proj q1 dim b1 × proj q2 dim b2 = proj q2 dim b2 × proj q1 dim b1.
Proof.
  intros dim q1 q2 b1 b2.
  unfold proj, pad.
  gridify; trivial.
  all: destruct b1; destruct b2; auto with wf_db.
  all: Qsimpl; reflexivity.
Qed.

Lemma proj_twice_eq : forall dim q b,
  proj q dim b × proj q dim b = proj q dim b.
Proof.
  intros dim q b.
  unfold proj, pad.
  gridify.
  destruct b; Qsimpl; reflexivity.
Qed.

Lemma proj_twice_neq : forall dim q b1 b2,
  b1 <> b2 -> proj q dim b1 × proj q dim b2 = Zero.
Proof.
  intros dim q b1 b2 neq.
  unfold proj, pad.
  gridify.
  destruct b1; destruct b2; try contradiction; Qsimpl; reflexivity.
Qed.

Lemma phase_shift_on_basis_state_adj : forall (θ : R) (b : bool),
  (∣ b ⟩)† × phase_shift θ = (Cexp (b * θ)) .* (∣ b ⟩)†.
Proof.
  intros.
  destruct b; solve_matrix; autorewrite with R_db.
  reflexivity.
  rewrite Cexp_0; reflexivity.
Qed.

Lemma proj_Rz_comm : forall dim q n b k,
  proj q dim b × uc_eval (SQIR.Rz k n) = uc_eval (SQIR.Rz k n) × proj q dim b. 
Proof.
  intros dim q n b k.
  unfold proj.
  autorewrite with eval_db.
  gridify.
  all: destruct b; auto with wf_db.
  all: repeat rewrite <- Mmult_assoc; rewrite phase_shift_on_basis_state.
  all: repeat rewrite Mmult_assoc; rewrite phase_shift_on_basis_state_adj. 
  all: rewrite Mscale_mult_dist_r, Mscale_mult_dist_l; reflexivity.
Qed.

Lemma proj_Rz : forall dim q b θ,
  uc_eval (SQIR.Rz θ q) × proj q dim b = Cexp (b * θ) .* proj q dim b. 
Proof.
  intros dim q b θ.
  unfold proj.
  autorewrite with eval_db.
  gridify.
  destruct b.
  all: repeat rewrite <- Mmult_assoc; rewrite phase_shift_on_basis_state.
  all: rewrite Mscale_mult_dist_l, Mscale_kron_dist_r, Mscale_kron_dist_l; 
       reflexivity.
Qed.

Lemma proj_CNOT_control : forall dim q m n b,
  (q <> n \/ m = n) ->
  proj q dim b × uc_eval (SQIR.CNOT m n) = uc_eval (SQIR.CNOT m n) × proj q dim b.
Proof.
  intros dim q m n b H.
  destruct H.
  bdestruct (m =? n).
  (* badly typed case *)
  1,3: subst; replace (uc_eval (SQIR.CNOT n n)) with (@Zero (2 ^ dim) (2 ^ dim));
       Msimpl_light; try reflexivity.
  1,2: autorewrite with eval_db; bdestructΩ (n <? n); reflexivity.
  bdestruct (q =? m).
  (* q = control *)
  subst. unfold proj.
  autorewrite with eval_db.
  gridify.
  destruct b; Qsimpl; reflexivity.
  destruct b; Qsimpl; reflexivity.
  (* disjoint qubits *)
  bdestructΩ (q =? n).
  apply proj_commutes_2q_gate; assumption.
Qed.

Lemma proj_CNOT_target : forall dim f q n,
  proj q dim ((f q) ⊕ (f n)) × proj n dim (f n) × uc_eval (SQIR.CNOT n q) = proj n dim (f n) × uc_eval (SQIR.CNOT n q) × proj q dim (f q).
Proof.
  intros dim f q n.
  unfold proj.
  autorewrite with eval_db.
  gridify. (* slow! *)
  all: try (destruct (f n); destruct (f (n + 1 + d)%nat));        
       try (destruct (f q); destruct (f (q + 1 + d)%nat));   
       auto with wf_db.
  all: simpl; Qsimpl; reflexivity.
Qed.

(* We can use 'proj' to state that qubit q is in classical state b. *)
Definition classical {dim} q b (ψ : Vector (2 ^ dim)) := proj q dim b × ψ = ψ.

Lemma f_to_vec_classical : forall n q f,
  (q < n)%nat -> classical q (f q) (f_to_vec n f).
Proof.
  intros n q f Hq.
  unfold classical, proj.
  induction n; try lia.
  unfold pad.
  replace (q + 1)%nat with (S q) by lia. 
  bdestructΩ (S q <=? S n); clear H.
  bdestruct (q =? n).
  - subst. replace (n - n)%nat with O by lia.
    simpl. Msimpl_light.
    restore_dims.
    rewrite kron_mixed_product.
    Msimpl_light; apply f_equal2; auto.
    destruct (f n); solve_matrix.
  - remember (n - q - 1)%nat as x.
    replace (n - q)%nat with (x + 1)%nat by lia.
    replace n with (q + 1 + x)%nat by lia.
    replace (2 ^ (x + 1))%nat with (2 ^ x * 2)%nat by unify_pows_two.
    rewrite <- id_kron.
    rewrite <- kron_assoc.
    replace (2 ^ (q + 1 + x) + (2 ^ (q + 1 + x) + 0))%nat with (2 ^ (q + 1 + x) * 2)%nat by lia.
    repeat rewrite Nat.pow_add_r.
    replace 1%nat with (1 * 1)%nat by lia. 
    rewrite kron_mixed_product; simpl.
    replace (q + 1 + x)%nat with n by lia.
    subst.
    Msimpl_light.
    2: destruct (f n); auto with wf_db.
    rewrite <- IHn at 2; try lia.
    unfold pad. 
    bdestructΩ (q + 1 <=? n); clear H0.
    replace (n - (q + 1))%nat with (n - q - 1)%nat by lia.
    restore_dims. reflexivity.
Qed.

(*******************************)
(**        Indexed Sum        **)
(*******************************)

Fixpoint vsum {d} n (f : nat -> Vector d) : Vector d :=
  match n with
  | 0 => Zero
  | S n' => vsum n' f .+  f n'
end.

Lemma vsum_WF : forall d n (f : nat -> Vector d), 
  (forall i, (i < n)%nat -> WF_Matrix (f i)) -> 
  WF_Matrix (vsum n f).
Proof.
  intros. 
  induction n; simpl; auto with wf_db.
  apply WF_plus; auto.
Qed.
Hint Resolve vsum_WF : wf_db.

Lemma vsum_eq : forall {d} n (f f' : nat -> Vector d),
  (forall i, (i < n)%nat -> f i = f' i) -> vsum n f = vsum n f'.
Proof.
  intros d n f f' Heq.
  induction n; simpl.
  reflexivity.
  rewrite Heq by lia.
  rewrite IHn. reflexivity.
  intros. apply Heq. lia.
Qed.

Lemma vsum_extend_r : forall d n (f : nat -> Vector d), 
  vsum n f .+ f n = vsum (S n) f.
Proof. reflexivity. Qed.

Lemma vsum_extend_l : forall d n (f : nat -> Vector d),
  (f O) .+ vsum n (shift f 1) = vsum (S n) f.
Proof.
  intros d n f.
  induction n.
  simpl. lma.
  remember (S n) as n'.
  simpl.
  rewrite <- IHn; clear IHn.  
  subst; simpl.
  rewrite shift_simplify.
  replace (n + 1)%nat with (S n) by lia. 
  lma.
Qed.

Lemma kron_vsum_distr_l : forall d1 d2 n (f : nat -> Vector d1) (ψ : Vector d2),
  ψ ⊗ vsum n f = vsum n (fun i => ψ ⊗ (f i)).
Proof.
  intros.
  induction n; simpl. lma.
  rewrite kron_plus_distr_l, IHn. reflexivity.
Qed.

Lemma kron_vsum_distr_r : forall d1 d2 n (f : nat -> Vector d1) (ψ : Vector d2),
  vsum n f ⊗ ψ = vsum n (fun i => (f i) ⊗ ψ).
Proof.
  intros.
  induction n; simpl. lma.
  rewrite kron_plus_distr_r, IHn. reflexivity.
Qed.

Lemma Mmult_vsum_distr_l : forall {d m} n (f : nat -> Vector d) (U : Matrix m d),
  U × vsum n f = vsum n (fun i => U × (f i)).
Proof.
  intros.
  induction n; simpl. 
  Msimpl. reflexivity.
  rewrite Mmult_plus_distr_l, IHn. reflexivity.
Qed.

Lemma Mscale_vsum_distr_r : forall {d} x n (f : nat -> Vector d),
  x .* vsum n f = vsum n (fun i => x .* f i).
Proof.
  intros d x n f.
  induction n; simpl. lma.
  rewrite Mscale_plus_distr_r, IHn. reflexivity.
Qed.

Lemma Mscale_vsum_distr_l : forall {d} n (f : nat -> C) (A : Vector d),
  vsum n (fun i => (f i) .* A) = Csum f n .* A.
Proof.
  intros d n f A.
  induction n; simpl. lma.
  rewrite Mscale_plus_distr_l, IHn. reflexivity.
Qed.

Lemma vsum_0 : forall d n (f : nat -> Vector d),
  (forall x, x < n -> f x = Zero) -> vsum n f = Zero.
Proof.
  intros d n f Hf.
  induction n; simpl. reflexivity.
  rewrite IHn, Hf. Msimpl. reflexivity.
  lia. intros. apply Hf. lia.
Qed.

Lemma vsum_plus : forall d n (f1 f2 : nat -> Vector d),
  vsum n (fun i => (f1 i) .+ (f2 i)) = vsum n f1 .+ vsum n f2.
Proof.
  intros d n f1 f2.
  induction n; simpl. lma.
  rewrite IHn. lma.
Qed.

Lemma vsum_swap_order : forall {d} m n (f : nat -> nat -> Vector d),
  vsum n (fun j => vsum m (fun i => f j i)) = vsum m (fun i => vsum n (fun j => f j i)).
Proof.
  intros d m n f.
  induction n; simpl. 
  rewrite vsum_0 by auto. reflexivity.
  rewrite IHn. rewrite vsum_plus. reflexivity.
Qed.

Lemma vsum_unique : forall d n (f : nat -> Vector d) (v : Vector d),
  (exists i, i < n /\ f i = v /\ (forall j, j < n -> j <> i -> f j = Zero)) -> 
  vsum n f = v.
Proof.
  intros d n f v H.
  destruct H as [i [? [? H]]].
  induction n; try lia.
  simpl.
  bdestruct (n =? i).
  rewrite (vsum_eq _ _ (fun _ : nat => Zero)).
  rewrite vsum_0. Msimpl. subst. reflexivity. auto.
  intros x ?. apply H; lia.
  rewrite IHn; try lia.
  rewrite H by lia. lma.
  intros. apply H; lia.
Qed.

(* Two natural ways to split a vsum into two parts *)
Lemma vsum_sum1 : forall d m n (f : nat -> Vector d),
  vsum (m + n) f = vsum m f .+ vsum n (shift f m).
Proof.
  intros d m n f.
  induction m.
  simpl. Msimpl. rewrite shift_0. reflexivity.
  replace (S m + n)%nat with (S (m + n))%nat  by lia.
  simpl. rewrite IHm.
  repeat rewrite Mplus_assoc.
  replace (S m) with (1 + m) by reflexivity. rewrite <- shift_plus.
  remember (shift f m) as f'.
  replace (f (m + n)) with (f' n).
  rewrite vsum_extend_r.
  replace (f m) with (f' 0).
  rewrite vsum_extend_l.
  reflexivity.
  subst. rewrite shift_simplify. rewrite Nat.add_0_l. reflexivity.
  subst. rewrite shift_simplify. rewrite Nat.add_comm. reflexivity.
Qed.

Local Opaque Nat.mul.
Lemma vsum_sum2 : forall d n (f : nat -> Vector d),
  vsum (2 * n) f = vsum n (fun i => f (2 * i)%nat) .+ vsum n (fun i => f (2 * i + 1)%nat).
Proof.
  intros d n f.
  induction n.
  rewrite Nat.mul_0_r. simpl. Msimpl. reflexivity.
  replace (2 * S n)%nat with (S (S (2 * n)))%nat  by lia.
  simpl vsum. 
  rewrite IHn; clear.
  replace (2 * n + 1)%nat with (S (2 * n)) by lia.
  lma.
Qed.
Local Transparent Nat.mul.

Lemma vsum_split : forall {d} (n i : nat) (v : nat -> Vector d),
  (i < n)%nat ->
  vsum n v = (vsum i v) .+ v i .+ (vsum (n - 1 - i) (shift v (i + 1))).
Proof.
  intros.
  induction n.
  - contradict H. lia.
  - bdestruct (i =? n).
    + subst.
      replace (S n - 1 - n)%nat with O by lia.
      simpl. Msimpl.
      reflexivity.
    + assert (i < n)%nat by lia.
      specialize (IHn H1).
      replace (S n - 1 - i)%nat with (S (n - 1 - i))%nat by lia.
      simpl.
      rewrite IHn.
      repeat rewrite Mplus_assoc. 
      unfold shift; simpl.
      replace (n - 1 - i + (i + 1))%nat with n by lia.
      reflexivity.
Qed.

Definition fswap (f : nat -> nat) x y :=
  fun i => if i =? x then f y else if i =? y then f x else f i.

Lemma fswap_simpl1 : forall f x y, fswap f x y x = f y.
Proof. 
  intros. 
  unfold fswap. 
  rewrite Nat.eqb_refl. 
  reflexivity. 
Qed.

Lemma fswap_simpl2 : forall f x y, fswap f x y y = f x.
Proof. 
  intros.
  unfold fswap. 
  bdestruct (y =? x).
  subst. reflexivity.
  rewrite Nat.eqb_refl. 
  reflexivity. 
Qed.

Lemma fswap_same : forall f x, fswap f x x = f.
Proof.
  intros.
  unfold fswap.
  apply functional_extensionality.
  intro i.
  bdestruct_all; auto.
Qed.

Lemma vsum_eq_up_to_fswap : forall {d} n f (v : nat -> Vector d) x y,
  (x < n)%nat -> (y < n)%nat ->
  vsum n (fun i => v (f i)) = vsum n (fun i => v (fswap f x y i)).
Proof.
  intros d n f v x y Hx Hy.
  bdestruct (x =? y).
  subst.
  apply vsum_eq.
  intros i Hi.
  unfold fswap.
  bdestruct_all; subst; reflexivity.
  bdestruct (x <? y).
  - rewrite 2 (vsum_split n y) by auto.
    rewrite 2 (vsum_split y x) by auto.
    rewrite fswap_simpl1, fswap_simpl2.
    unfold shift.
    erewrite (vsum_eq x (fun _ => v (fswap _ _ _ _))).
    2: { intros i Hi.
         unfold fswap.
         bdestruct_all.
         reflexivity. }
    erewrite (vsum_eq (y - 1 - x) (fun _ => v (fswap _ _ _ _))).
    2: { intros i Hi.
         unfold fswap.
         bdestruct_all.
         reflexivity. }
    erewrite (vsum_eq (n - 1 - y) (fun _ => v (fswap _ _ _ _))).
    2: { intros i Hi.
         unfold fswap.
         bdestruct_all.
         reflexivity. }
    repeat rewrite (Mplus_comm _ _ _ (v _)).
    repeat rewrite <- Mplus_assoc.
    rewrite (Mplus_comm _ _ (v (f x))).
    reflexivity.
  - rewrite 2 (vsum_split n x) by auto.
    rewrite 2 (vsum_split x y) by lia.
    rewrite fswap_simpl1, fswap_simpl2.
    unfold shift.
    erewrite (vsum_eq y (fun _ => v (fswap _ _ _ _))).
    2: { intros i Hi.
         unfold fswap.
         bdestruct_all.
         reflexivity. }
    erewrite (vsum_eq (x - 1 - y) (fun _ => v (fswap _ _ _ _))).
    2: { intros i Hi.
         unfold fswap.
         bdestruct_all.
         reflexivity. }
    erewrite (vsum_eq (n - 1 - x) (fun _ => v (fswap _ _ _ _))).
    2: { intros i Hi.
         unfold fswap.
         bdestruct_all.
         reflexivity. }
    repeat rewrite (Mplus_comm _ _ _ (v _)).
    repeat rewrite <- Mplus_assoc.
    rewrite (Mplus_comm _ _ (v (f y))).
    reflexivity.
Qed.

Definition finite_bijection (n : nat) (f : nat -> nat) :=
  (forall x, x < n <-> f x < n)%nat /\ 
  (exists g, (forall x, g (f x) = x) /\ (forall y, f (g y) = y)).

(* A weaker property sometimes easier to prove. *)
Definition weak_finite_bijection (n : nat) (f : nat -> nat) :=
  (forall x, x < n -> f x < n)%nat /\ 
  (exists g, (forall y, y < n -> g y < n)%nat /\
        (forall x, (x < n)%nat -> g (f x) = x) /\ 
        (forall y, (y < n)%nat -> f (g y) = y)).

Lemma finite_bijection_implies_weak : forall n f,
  finite_bijection n f -> weak_finite_bijection n f.
Proof.
  intros n f [Hf [g [Hg1 Hg2]]].
  repeat split.
  intros.
  rewrite <- Hf; auto.
  exists g. 
  repeat split; intros; auto.
  rewrite <- (Hg2 y) in H.
  rewrite <- Hf in H.
  assumption.
Qed.

Lemma weak_finite_bijection_is_injective : forall n f,
  weak_finite_bijection n f -> 
  forall x y, (x < n)%nat -> (y < n)%nat -> f x = f y -> x = y.
Proof.
  intros n f [_ [g [_ [Hg _]]]] x y ? ? H.
  rewrite <- (Hg x) by assumption.
  rewrite <- (Hg y) by assumption.
  rewrite H.
  reflexivity.
Qed.

Lemma fswap_at_boundary_weak_finite_bijection : forall n f x,
  weak_finite_bijection (S n) f ->
  (x < S n)%nat -> f x = n ->
  weak_finite_bijection n (fswap f x n).
Proof.
  intros n f x Hf Hx Hfx.
  split.
  - (* f is bounded *)
    assert (forall y, y < S n -> y <> x -> f y <> n)%nat.
    { intros y Hy H contra.
      rewrite <- Hfx in contra.
      eapply weak_finite_bijection_is_injective in contra.
      contradiction.
      apply Hf.
      assumption.
      assumption. }
    intros.
    destruct Hf as [Hf _].
    unfold fswap.
    bdestruct_all; subst.
    assert (f (f x) < S (f x))%nat.
    apply Hf. lia.
    specialize (H (f x)). lia.
    assert (f x0 < S (f x))%nat.
    apply Hf. lia.
    specialize (H x0). lia.
  - (* f is a bijection *)
    destruct Hf as [Hf [g [Hg1 [Hg2 Hg3]]]].
    exists (compose (fswap (fun x : nat => x) x n) g).
    unfold fswap, compose.
    split; intros.
    assert (g y < S n). 
    apply Hg1. lia.
    assert (g y <> x).
    intro contra. 
    rewrite <- contra in Hfx.
    rewrite Hg3 in Hfx; lia.
    bdestruct_all; subst; lia. 
    clear Hfx.
    split; intros.
    bdestruct (x0 =? x); subst.
    bdestruct_all; subst; auto.
    symmetry. auto.     
    contradict H1. auto.
    bdestruct (x0 =? n); subst.
    bdestruct_all; subst; auto.
    bdestruct_all; subst; auto.
    contradict H0. symmetry. auto.
    contradict H1. symmetry. auto.
    bdestruct (g y =? x); subst.
    bdestruct_all; subst; auto.
    bdestruct (g y =? n); subst.
    bdestruct_all; subst; auto.
    bdestruct_all; subst; auto.
Qed.
  
(* vsum terms can be arbitrarily reordered *)
Lemma vsum_reorder : forall {d} n (v : nat -> Vector d) f,
  weak_finite_bijection n f ->
  vsum n v = vsum n (fun i => v (f i)).
Proof.
  intros.
  generalize dependent f.
  induction n.
  reflexivity.
  intros f [Hf [g [Hg1 [Hg2 Hg3]]]].
  assert (g n < S n)%nat.
  apply Hg1. lia.
  rewrite (vsum_eq_up_to_fswap _ f _ (g n) n) by auto.
  simpl.
  rewrite fswap_simpl2.
  rewrite Hg3 by auto.
  specialize (IHn (fswap f (g n) n)).
  rewrite <- IHn.
  reflexivity.
  apply fswap_at_boundary_weak_finite_bijection.
  split.
  all: auto.
  exists g. auto.
Qed.

(*******************************)
(** Indexed Kronecker Product **)
(*******************************)

(* This could also be defined over (f : nat -> Vector d) *)
Fixpoint vkron n (f : nat -> Vector 2) : Vector (2 ^ n) :=
  match n with
  | 0    => I 1
  | S n' => vkron n' f ⊗ f n'
  end.

Lemma vkron_WF : forall n (f : nat -> Vector 2), 
  (forall i, (i < n)%nat -> WF_Matrix (f i)) -> 
  WF_Matrix (vkron n f).
Proof.
  intros. 
  induction n; simpl; auto with wf_db.
  apply WF_kron; auto. lia.
Qed.
Hint Resolve vkron_WF : wf_db.

Lemma vkron_extend_r : forall n f, 
  vkron n f ⊗ f n = vkron (S n) f.
Proof. reflexivity. Qed.

Lemma vkron_extend_l : forall n (f : nat -> Vector 2),
  (forall i, WF_Matrix (f i)) ->
  (f O) ⊗ vkron n (shift f 1) = vkron (S n) f.
Proof.
  intros n f WF.
  induction n.
  simpl. Msimpl. reflexivity.
  remember (S n) as n'.
  simpl.
  rewrite <- IHn; clear IHn.  
  subst; simpl.
  restore_dims; rewrite <- kron_assoc.
  rewrite shift_simplify.
  replace (n + 1)%nat with (S n) by lia.
  reflexivity.
Qed.

Lemma kron_n_f_to_vec : forall n (A : Square 2) f,
  n ⨂ A × f_to_vec n f = vkron n (fun k => A × ∣ f k ⟩ ).
Proof.
  intros n A f.
  induction n; simpl. 
  Msimpl. reflexivity.
  restore_dims.
  rewrite kron_mixed_product.
  rewrite IHn.
  reflexivity.
Qed.

Lemma Mscale_vkron_distr_r : forall n x (f : nat -> Vector 2),
  vkron n (fun i => x .* f i) = x ^ n .* vkron n f.
Proof.
  intros n x f.
  induction n.
  simpl. Msimpl. reflexivity.
  simpl.
  rewrite IHn. 
  distribute_scale.
  rewrite Cmult_comm.
  reflexivity.
Qed.

Lemma vkron_split : forall n i (f : nat -> Vector 2),
  i < n ->
  vkron n f = (vkron i f) ⊗ f i ⊗ (vkron (n - 1 - i) (shift f (i + 1))).
Proof.
  intros.
  induction n; try lia.
  bdestruct (i =? n).
  subst.
  replace (S n - 1 - n)%nat with O by lia.
  simpl. Msimpl.
  reflexivity.
  assert (i < n)%nat by lia.
  specialize (IHn H1).
  replace (S n - 1 - i)%nat with (S (n - 1 - i))%nat by lia.
  simpl.
  rewrite IHn.
  unfold shift.
  replace (n - 1 - i + (i + 1))%nat with n by lia.
  restore_dims; repeat rewrite kron_assoc. 
  reflexivity.
Qed.

Lemma vkron_eq : forall n (f f' : nat -> Vector 2),
  (forall i, i < n -> f i = f' i) -> vkron n f = vkron n f'.
Proof.
  intros n f f' Heq.
  induction n; simpl.
  reflexivity.
  rewrite Heq by lia.
  rewrite IHn. reflexivity.
  intros. apply Heq. lia.
Qed.

(* Of the lemmas below, the important two are vkron_to_vsum1 and vsum_to_vkron2 
   (TODO: better names). Both lemmas provide a way to convert from an indexed
   Kronecker product to an index sum. vkron_to_vsum1 is used in the QPE proof
   and vsum_to_vkron2 is used in the QPE and Deutsch-Josza proofs. *)

Lemma basis_vector_prepend_0 : forall n k,
  n <> 0 -> k < n ->
  ∣0⟩ ⊗ basis_vector n k = basis_vector (2 * n) k.
Proof.
  intros.
  unfold basis_vector; solve_matrix. (* solve_matrix doesn't work? *)
  repeat rewrite andb_true_r.
  bdestruct (x / n =? 0).
  rewrite H1. apply Nat.div_small_iff in H1; auto.
  rewrite Nat.mod_small by auto.
  destruct (x =? k); lca.
  assert (H1' := H1).
  rewrite Nat.div_small_iff in H1'; auto.
  destruct (x / n)%nat; try lia.
  bdestructΩ (x =? k).
  destruct n0; lca.
  destruct (x / n)%nat; try lca.
  destruct n0; lca.
Qed.

Lemma basis_vector_prepend_1 : forall n k,
  n <> 0 -> k < n ->
  ∣1⟩ ⊗ basis_vector n k = basis_vector (2 * n) (k + n).
Proof.
  intros.
  unfold basis_vector; solve_matrix.
  all: repeat rewrite andb_true_r.
  specialize (Nat.div_mod x n H) as DM.
  destruct (x / n)%nat.
  rewrite Nat.mul_0_r, Nat.add_0_l in DM.
  assert (x < n)%nat.
  rewrite DM. apply Nat.mod_upper_bound; auto.
  bdestructΩ (x =? k + n)%nat.
  lca.
  destruct n0.
  bdestruct (x mod n =? k).
  bdestructΩ (x =? k + n); lca.
  bdestructΩ (x =? k + n); lca.
  assert (x >= 2 * n)%nat.
  assert (n * S (S n0) >= 2 * n)%nat.
  clear. induction n0; lia.
  lia.
  bdestructΩ (x =? k + n); lca.
  destruct (x /  n)%nat; try lca.
  destruct n0; lca.
Qed.

Local Opaque Nat.mul Nat.div Nat.modulo.
Lemma basis_vector_append_0 : forall n k,
  n <> 0 -> k < n ->
  basis_vector n k ⊗ ∣0⟩ = basis_vector (2 * n) (2 * k).
Proof.
  intros.
  unfold basis_vector; solve_matrix.
  rewrite Nat.div_1_r.
  bdestruct (y =? 0); subst.
  2: repeat rewrite andb_false_r; lca.
  bdestruct (x =? 2 * k); subst.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul by auto.
  rewrite Nat.eqb_refl.
  rewrite Nat.mod_mul, Nat.mod_0_l by auto. 
  lca.
  bdestruct (x / 2 =? k); simpl; try lca.
  destruct (x mod 2) eqn:m.
  contradict H1.
  rewrite <- H2.
  apply Nat.div_exact; auto.
  destruct n0; try lca.
  rewrite Nat.mod_0_l by auto.
  lca.
Qed.

Lemma basis_vector_append_1 : forall n k,
  n <> 0 -> k < n ->
  basis_vector n k ⊗ ∣1⟩ = basis_vector (2 * n) (2 * k + 1).
Proof.
  intros.
  unfold basis_vector; solve_matrix.
  rewrite Nat.div_1_r.
  bdestruct (y =? 0); subst.
  2: repeat rewrite andb_false_r; lca.
  bdestruct (x =? 2 * k + 1); subst. 
  Search ((_ + _)/ _).
  rewrite Nat.mul_comm. 
  rewrite Nat.div_add_l by auto.
  replace (1 / 2) with 0 by auto.
  rewrite Nat.add_0_r.
  rewrite Nat.eqb_refl.
  rewrite Nat.add_comm, Nat.mod_add by auto. 
  replace (1 mod 2) with 1 by auto. 
  replace (0 mod 1) with 0 by auto.  
  lca. 
  bdestruct (x / 2 =? k); simpl; try lca.
  destruct (x mod 2) eqn:m.   
  replace (0 mod 1) with 0 by auto; lca.
  destruct n0; try lca.
  contradict H1.
  rewrite <- H2.
  remember 2 as two.
  rewrite <- m.
  subst.
  apply Nat.div_mod; auto.
Qed.
Local Transparent Nat.mul Nat.div Nat.modulo.

Lemma vkron_to_vsum1 : forall n (c : R),
  n > 0 -> 
  vkron n (fun k => ∣0⟩ .+ Cexp (c * 2 ^ (n - k - 1)) .* ∣1⟩) = 
    vsum (2 ^ n) (fun k => Cexp (c * INR k) .* basis_vector (2 ^ n) k).
Proof.
  intros n c Hn.
  destruct n; try lia.
  induction n.
  simpl. Msimpl. 
  rewrite Rmult_0_r, Cexp_0, Mscale_1_l.
  replace (basis_vector 2 0) with ∣0⟩ by solve_matrix.
  replace (basis_vector 2 1) with ∣1⟩ by solve_matrix.
  reflexivity. 
  remember (S n) as n'.
  rewrite <- vkron_extend_l; auto with wf_db.
  replace (shift (fun k : nat => ∣0⟩ .+ Cexp (c * 2 ^ (S n' - k - 1)) .* ∣1⟩) 1) with (fun k : nat => ∣0⟩ .+ Cexp (c * 2 ^ (n' - k - 1)) .* ∣1⟩).
  2: { unfold shift. 
       apply functional_extensionality; intro k.
       replace (S n' - (k + 1) - 1)%nat with (n' - k - 1)%nat by lia.
       reflexivity. }
  rewrite IHn by lia.
  replace (S n' - 0 - 1)%nat with n' by lia.
  remember (2 ^ n')%nat as N.
  assert (HN: (N > 0)%nat).
  subst. apply pow_positive. lia.
  replace (2 ^ n')%R with (INR N).
  2: { subst. rewrite pow_INR. simpl INR. replace (1+1)%R with 2%R by lra.
       reflexivity. }
  replace (2 ^ S n')%nat with (2 * N)%nat.
  2: { subst. unify_pows_two. }
  clear - HN.
  rewrite kron_plus_distr_r.
  rewrite 2 kron_vsum_distr_l.
  replace (2 * N) with (N + N) by lia.
  rewrite vsum_sum1.
  replace (N + N) with (2 * N) by lia.
  rewrite (vsum_eq _ (fun i : nat => ∣0⟩ ⊗ (Cexp (c * INR i) .* basis_vector N i)) (fun k : nat => Cexp (c * INR k) .* basis_vector (2 * N) k)).
  rewrite (vsum_eq _ (fun i : nat => Cexp (c * INR N) .* ∣1⟩ ⊗ (Cexp (c * INR i) .* basis_vector N i)) (shift (fun k : nat => Cexp (c * INR k) .* basis_vector (2 * N) k) N)).
  reflexivity.
  intros i Hi.
  rewrite shift_simplify.
  distribute_scale.
  rewrite <- Cexp_add, <- Rmult_plus_distr_l, <- plus_INR. 
  rewrite basis_vector_prepend_1 by lia.
  rewrite Nat.add_comm.
  reflexivity.
  intros i Hi.
  distribute_scale.
  rewrite basis_vector_prepend_0 by lia.
  reflexivity.
Qed.

Fixpoint product (x y : nat -> bool) n :=
  match n with
  | O => false
  | S n' => xorb ((x n') && (y n')) (product x y n')
  end.

Lemma product_comm : forall f1 f2 n, product f1 f2 n = product f2 f1 n.
Proof.
  intros f1 f2 n.
  induction n; simpl; auto.
  rewrite IHn, andb_comm.
  reflexivity.
Qed.

Lemma product_update_oob : forall f1 f2 n b dim, (dim <= n)%nat ->
  product f1 (update f2 n b) dim = product f1 f2 dim.
Proof.
  intros.
  induction dim; trivial.
  simpl.
  rewrite IHdim by lia.
  unfold update.
  bdestruct (dim =? n); try lia.
  reflexivity.
Qed.

Lemma product_0 : forall f n, product (fun _ : nat => false) f n = false.
Proof.
  intros f n.
  induction n; simpl; auto.
  rewrite IHn; reflexivity.
Qed.

Lemma nat_to_funbool_0 : forall n, nat_to_funbool n 0 = (fun _ => false).
Proof.
  intro n.
  unfold nat_to_funbool, nat_to_binlist.
  simpl.
  replace (n - 0)%nat with n by lia.
  induction n; simpl.
  reflexivity.
  replace (n - 0)%nat with n by lia.
  rewrite update_same; rewrite IHn; reflexivity.
Qed.

Local Open Scope R_scope.
Local Open Scope C_scope.
Local Opaque Nat.mul.
Lemma vkron_to_vsum2 : forall n (f : nat -> bool),
  (n > 0)%nat -> 
  vkron n (fun k => ∣0⟩ .+ (-1) ^ f k .* ∣1⟩) = 
    vsum (2 ^ n) (fun k => (-1) ^ (product f (nat_to_funbool n k) n) .* basis_vector (2 ^ n) k).
Proof.
  intros n f ?.
  destruct n; try lia.
  clear.
  induction n.
  - simpl.
    repeat rewrite Nat.mul_1_r.
    simpl. Msimpl.
    unfold nat_to_funbool; simpl.
    rewrite 2 update_index_eq.
    replace (basis_vector 2 0) with ∣0⟩ by solve_matrix.
    replace (basis_vector 2 1) with ∣1⟩ by solve_matrix.
    destruct (f O); simpl; restore_dims; lma. 
  - remember (S n) as n'.
    simpl vkron.
    rewrite IHn; clear.
    replace (2 ^ S n')%nat with (2 * 2 ^ n')%nat by reflexivity. 
    rewrite vsum_sum2.
    rewrite <- vsum_plus.
    rewrite kron_vsum_distr_r.
    replace (2 * 2 ^ n')%nat with (2 ^ n' * 2)%nat by lia.
    apply vsum_eq.
    intros i Hi.
    distribute_plus.
    distribute_scale.
    rewrite (basis_vector_append_0 (2 ^ n')); auto; try lia.
    rewrite (basis_vector_append_1 (2 ^ n')); auto; try lia.
    apply f_equal2; apply f_equal2; try reflexivity.
    apply f_equal2; try reflexivity.
    simpl.
    destruct i.
    rewrite Nat.mul_0_r. 
    unfold nat_to_funbool, nat_to_binlist; simpl.
    replace (n' - 0)%nat with n' by lia.
    rewrite update_index_eq.
    rewrite andb_false_r, xorb_false_l.
    rewrite product_update_oob by lia.
    reflexivity.
    unfold nat_to_funbool, nat_to_binlist.
    rewrite nat_to_binlist'_even by lia.
    simpl.
    replace (n' - 0)%nat with n' by lia.
    rewrite update_index_eq.
    rewrite andb_false_r, xorb_false_l.
    rewrite product_update_oob by lia.
    reflexivity. 
    repeat rewrite RtoC_pow.
    rewrite <- RtoC_mult.
    rewrite <- pow_add.
    simpl.
    unfold nat_to_funbool, nat_to_binlist.
    rewrite nat_to_binlist'_odd by lia.
    simpl.
    replace (n' - 0)%nat with n' by lia.
    rewrite update_index_eq.
    rewrite andb_true_r.
    rewrite product_update_oob by lia.
    remember (product f (list_to_funbool n' (nat_to_binlist' i ++ repeat false (n' - length (nat_to_binlist' i)))) n') as p.
    destruct (f n'); destruct p; simpl; lca.
Qed.
Local Transparent Nat.mul.

Lemma H_spec : (* slightly different from hadamard_on_basis_state *)
  forall b : bool, hadamard × ∣ b ⟩ = / √ 2 .* (∣ 0 ⟩ .+ (-1)^b .* ∣ 1 ⟩).
Proof.
  intro b.
  destruct b; simpl; autorewrite with ket_db.
  replace (/ √ 2 * (-1 * 1))%C with (- / √ 2)%C by lca.
  reflexivity. reflexivity.
Qed.

Lemma H_kron_n_spec : forall n x, (n > 0)%nat ->
  n ⨂ hadamard × f_to_vec n x = 
    /√(2 ^ n) .* vsum (2 ^ n) (fun k => (-1) ^ (product x (nat_to_funbool n k) n) .* basis_vector (2 ^ n) k).
Proof. 
  intros n x Hn. 
  rewrite kron_n_f_to_vec.
  erewrite (vkron_eq _ (fun k : nat => hadamard × ∣ x k ⟩)).
  2: { intros i Hi.
       rewrite H_spec.
       reflexivity. }
  rewrite Mscale_vkron_distr_r.
  apply f_equal2.  
  repeat rewrite <- RtoC_inv by nonzero.
  rewrite RtoC_pow. 
  rewrite <- Rinv_pow by nonzero. 
  rewrite <- sqrt_pow by lra. 
  reflexivity.
  apply vkron_to_vsum2.
  assumption.
Qed.

Lemma H0_kron_n_spec_alt : forall n, (n > 0)%nat ->
  n ⨂ hadamard × n ⨂ ∣0⟩ = 
    /√(2 ^ n) .* vsum (2 ^ n) (fun k => basis_vector (2 ^ n) k).
Proof. 
  intros.
  replace (n ⨂ ∣0⟩) with (f_to_vec n (fun _ => false)).
  replace (1^n)%nat with (S O).
  rewrite H_kron_n_spec by assumption.
  apply f_equal2; try reflexivity.
  apply vsum_eq.
  intros.
  rewrite product_0; simpl. lma.
  symmetry. apply Nat.pow_1_l. 
  clear.
  induction n; try reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.





