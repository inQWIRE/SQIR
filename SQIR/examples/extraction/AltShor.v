Require Import Shor.
Require Import AltGateSet.

(* Redefining Shor's alg. using the new gate set *)

Fixpoint controlled_rotations n : ucom U :=
  match n with
  | 0 | 1 => SKIP
  | 2     => CU1 (2 * PI / 2 ^ n) 1 0
  | S n'  => controlled_rotations n' >> CU1 (2 * PI / 2 ^ n) n' 0
  end.

Fixpoint QFT n : ucom U :=
  match n with
  | 0    => SKIP
  | 1    => H 0
  | S n' => H 0 >> controlled_rotations n >> map_qubits S (QFT n')
  end.

Fixpoint reverse_qubits' dim n : ucom U :=
  match n with
  | 0    => SKIP
  | 1    => SWAP 0 (dim - 1)
  | S n' => reverse_qubits' dim n' >> SWAP n' (dim - n' - 1)
  end.
Definition reverse_qubits n := reverse_qubits' n (n/2)%nat.
Definition QFT_w_reverse n := QFT n >> reverse_qubits n.

Fixpoint controlled_powers_var' (f : nat -> bccom) k kmax : bccom :=
  match k with
  | O    => bcskip
  | S O  => bccont (kmax - 1) (f O)
  | S k' => bcseq (controlled_powers_var' f k' kmax)
                 (bccont (kmax - k' - 1) (f k'))
  end.
Definition controlled_powers_var (f : nat -> bccom) k : ucom U := 
  bc2ucom (controlled_powers_var' f k k).

(* TODO: move to RCIR *)
Fixpoint map_bccom (f : nat -> nat) (bc : bccom) : bccom :=
  match bc with
  | bcskip => bcskip
  | bcx a => bcx (f a)
  | bcswap a b => bcswap (f a) (f b)
  | bccont a bc1 => bccont (f a) (map_bccom f bc1)
  | bcseq bc1 bc2 => bcseq (map_bccom f bc1) (map_bccom f bc2)
  end.

Definition QPE_var k (f : nat -> bccom) : ucom U :=
  npar k U_H >>
  controlled_powers_var (fun x => map_bccom (fun q => k + q)%nat (f x)) k >>
  invert (QFT_w_reverse k).

(** Proofs **)

Lemma controlled_rotations_same : forall n,
  uc_eval n (controlled_rotations n) = 
    UnitarySem.uc_eval (QPE.controlled_rotations n).
Proof.
  destruct n; try reflexivity.
  destruct n; try reflexivity.
  induction n; try reflexivity.
  replace (controlled_rotations (S (S (S n)))) 
    with (controlled_rotations (S (S n)) >> 
          CU1 (2 * PI / 2 ^ (S (S (S n)))) (S (S n)) 0) 
    by reflexivity.
  replace (QPE.controlled_rotations (S (S (S n))))
    with (cast (QPE.controlled_rotations (S (S n))) (S (S (S n))); 
            UnitaryOps.control (S (S n)) (Rz (2 * PI / 2 ^ (S (S (S n)))) 0))%ucom
    by reflexivity.
  remember (S (S n)) as n'.
  replace (S n') with (n' + 1)%nat by lia.
  erewrite change_dim.
  unfold uc_eval in *.
  simpl.
  rewrite <- (pad_dims_r (to_base_ucom _ _)).
  rewrite <- (pad_dims_r (QPE.controlled_rotations _)).
  rewrite IHn.
  reflexivity.
  apply controlled_rotations_WT.
  lia.
  admit. (* uc_well_typed (to_base_ucom n' (controlled_rotations n')) *) 
Admitted.

Lemma QFT_same : forall n,
  uc_eval n (QFT n) = UnitarySem.uc_eval (QPE.QFT n).
Proof.
  destruct n; try reflexivity.
  induction n; try reflexivity.
  replace (QFT (S (S n))) 
    with (H 0 >> controlled_rotations (S (S n)) >> map_qubits S (QFT (S n))) 
    by reflexivity.
  replace (QPE.QFT (S (S n))) 
    with (SQIR.H 0 ; QPE.controlled_rotations (S (S n)) ; 
          cast (UnitaryOps.map_qubits S (QPE.QFT (S n))) (S (S n)))%ucom 
    by reflexivity. 
  Local Opaque H controlled_rotations QFT QPE.controlled_rotations QPE.QFT.
  erewrite change_dim.
  simpl.
  apply f_equal2; [ | apply f_equal2]; try reflexivity.
  rewrite map_qubits_same.
  specialize (pad_dims_l (to_base_ucom (S n) (QFT (S n))) (S O)) as aux.
  simpl in aux. 
  replace (fun q : nat => S q) with S in aux by reflexivity.
  rewrite <- aux; clear aux. 
  specialize (pad_dims_l (QPE.QFT (S n)) (S O)) as aux.
  simpl in aux. 
  replace (fun q : nat => S q) with S in aux by reflexivity.
  rewrite <- aux; clear aux. 
  rewrite <- IHn. 
  reflexivity.
  admit. (* well_formed (QFT (S n)) *)
  rewrite <- change_dim.
  apply controlled_rotations_same.
Admitted.

Lemma reverse_qubits_same : forall n,
  uc_eval n (reverse_qubits n) = UnitarySem.uc_eval (QPE.reverse_qubits n).
Proof.
  assert (H : forall n dim, uc_eval dim (reverse_qubits' dim n) = 
                         UnitarySem.uc_eval (QPE.reverse_qubits' dim n)).
  { intros n dim.
    destruct n; try reflexivity.
    induction n; try reflexivity.
    unfold uc_eval in *.
    simpl in *.
    rewrite IHn.
    reflexivity. }
  intro n.
  unfold reverse_qubits.
  apply H.
Qed.

Lemma QFT_w_reverse_same : forall n,
  uc_eval n (QFT_w_reverse n) = UnitarySem.uc_eval (QPE.QFT_w_reverse n).
Proof.
  intro n.
  unfold uc_eval; simpl.
  rewrite <- QFT_same, <- reverse_qubits_same.
  reflexivity.
Qed.

Lemma controlled_powers_var_same : forall n (f : nat -> bccom) k (f' : nat -> base_ucom n),
  (* some precondition relating f and f' *)
  uc_eval (k + n) (controlled_powers_var f k) = 
    UnitarySem.uc_eval (QPE.controlled_powers_var f' k).
Proof.
  assert (H : forall n f k kmax f',
    uc_eval (kmax + n) (bc2ucom (controlled_powers_var' f k kmax)) =
      UnitarySem.uc_eval (@QPE.controlled_powers_var' n f' k kmax)).
  { intros n f k kmax f'.
    destruct k; try reflexivity.
    induction k.
    unfold uc_eval; simpl.  
    admit.
    admit. }
  intros.
  apply H.
Admitted.



(* ... and so on, ending with QPE_var_same *)

(* Finally, the defn of shor_circuit + its correctness property: *)
Definition modexp a x N := a ^ x mod N.
Definition modmult_circuit a ainv N n i := 
  RCIR.bcelim (ModMult.modmult_rev N (modexp a (2 ^ i) N) (modexp ainv (2 ^ i) N) n).
Definition num_qubits n : nat := n + modmult_rev_anc n.

(* requires 0 < a < N, gcd a N = 1 
   returns a circuit + the number of qubits used *)
Definition shor_circuit a N := 
  let m := Nat.log2 (2 * N^2)%nat in
  let n := Nat.log2 (2 * N) in
  let ainv := modinv a N in
  let numq := num_qubits n in
  let f i := modmult_circuit a ainv N n i in
  (X (m + n - 1) >> QPE_var m f, (m + numq)%nat, m).

(* Final correctness property is a wrapper around Shor_correct_full_implementation
   in Shor.v *)

(*
Lemma Shor_correct_full_implementation :
  exists β, 
    β>0 /\
    forall (a N : nat),
      (0 < a < N)%nat ->
      (Nat.gcd a N = 1)%nat ->
      let m := Nat.log2 (2 * N^2)%nat in
      let n := Nat.log2 (2 * N)%nat in
      probability_of_success_var a (ord a N) N m n (modmult_rev_anc n) (f_modmult_circuit a (modinv a N) N n) >= β / (Nat.log2 N)^4.
Proof.

*)
