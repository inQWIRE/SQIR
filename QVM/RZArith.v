Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import PQASM.
Require Import CLArith.

Local Open Scope exp_scope.
Local Open Scope nat_scope.

Local Opaque CNOT. Local Opaque CCX.

(* 
  This file contains an implementation and proof of correctness for the modular
  multiplier circuit based on QFT.

  @Liyi: Link to relevant paper?
  https://arxiv.org/abs/quant-ph/0205095
  The modular multiplier circuit computes ((A * x) % N) where A and N are integer
  constants and x is an integer variable. The main definition in this file is 
  (rz_modmult_full y x n c A Ainv N). The main correctness property is
  rz_modmult_full_sem.

  @Liyi: Describe the different arguments to rz_modmult_full and summarize what
  rz_modmult_full_sem is saying.
  In rz_modmult_full (y:var) (x:var) (n:nat) (c:posi) (A:nat) (Ainv :nat) (N:nat),
  y is a group of n ancilla qubits, x is the input number, (n-2) is the qubit size of x.
  c is an ancilla qubit for storing data, A is the input number and Ainv is the invers of A,
  such that (A * Ainv) mod N = 1, N is the mod factor.
  The result of the circuit will produce (A*x) mod N in the y group qubits,
  while the x group will be all zero. If users want to make the values to x,
  feel free to add a swap gates between x and y.

*)


(*********** Definitions ***********)

Fixpoint rz_adder' (x:var) (n:nat) (size:nat) (M: nat -> bool) :=
  match n with 
  | 0 => SKIP (x,0)
  | S m => rz_adder' x m size M ; if M m then SR (size - n) x else SKIP (x,m)
  end.

Definition rz_adder (x:var) (n:nat) (M:nat -> bool) := rz_adder' x n n M.

Fixpoint rz_sub' (x:var) (n:nat) (size:nat) (M: nat -> bool) :=
  match n with 
  | 0 => SKIP (x,0)
  | S m => rz_sub' x m size M ; if M m then SRR (size - n) x else SKIP (x,m)
  end.

Definition rz_sub (x:var) (n:nat) (M:nat -> bool) := rz_sub' x n n M.

Definition rz_compare_half (x:var) (n:nat) (c:posi) (M:nat) := 
  Exp (rz_sub x n (nat2fb M)) ;; RQFT x ;; Exp (CNOT (x,0) c).

Definition rz_compare (x:var) (n:nat) (c:posi) (M:nat) := 
 rz_compare_half x n c M ;; (inv_pexp (Exp (rz_sub x n (nat2fb M)) ;; RQFT x)).

Definition qft_cu (x:var) (c:posi) := 
  RQFT x ;; Exp (CNOT (x,0) c) ;; QFT x.

Definition qft_acu (x:var) (c:posi) := 
  RQFT x ;; Exp (X (x,0); CNOT (x,0) c; X (x,0)) ;; QFT x.

Definition one_cu_adder (x:var) (n:nat) (c:posi) (M:nat -> bool) := CU c (rz_adder x n M).

Definition mod_adder_half (x:var) (n:nat) (c:posi) (A:nat -> bool) (M:nat -> bool) :=
  Exp (rz_adder x n A; (rz_sub x n M)) ;; qft_cu x c ;; Exp (one_cu_adder x n c M).

Definition clean_hbit (x:var) (n:nat) (c:posi) (M:nat -> bool) := 
  Exp (rz_sub x n M) ;; qft_acu x c ;; Exp( inv_exp (rz_sub x n M)).

Definition mod_adder (x:var) (n:nat) (c:posi) (A:nat -> bool) (M:nat -> bool) :=
  mod_adder_half x n c A M ;; clean_hbit x n c A.

(* modular multiplier: takes [x][0] -> [x][ax%N] where a and N are constant. *)
Fixpoint rz_modmult' (y:var) (x:var) (n:nat) (size:nat) (c:posi) (A:nat) (M:nat) :=
   match n with
   | 0 => Exp (SKIP (y,0))
   | S m => rz_modmult' y x m size c A M;;
           PCU (x,size - n) (mod_adder y size c (nat2fb ((2^m * A) mod M)) (nat2fb M))
   end.

Definition rz_modmult_half y x size c A M := 
   QFT y ;; rz_modmult' y x size size c A M ;; RQFT y.

Definition rz_modmult_full (y:var) (x:var) (n:nat) (c:posi) (A:nat) (Ainv :nat) (N:nat) :=
  rz_modmult_half y x n c A N ;; inv_pexp (rz_modmult_half x y n c Ainv N).

Definition vars_for_rz' (size:nat) := gen_vars size (x_var::(y_var::[])).

Definition vars_for_rz (size:nat) := 
       fun x => if x =? z_var then (size * 2,1,id_nat,id_nat) else vars_for_rz' size x.

Definition real_rz_modmult_rev (M C Cinv size:nat) :=
    rz_modmult_full y_var x_var size (z_var,0) C Cinv M.

Definition trans_rz_modmult_rev (M C Cinv size:nat) :=
        trans_pexp (vars_for_rz size) (2*size+1) (real_rz_modmult_rev M C Cinv size) (avs_for_arith size).

(*An alternative implementation for comparison on efficiency. *)
Definition one_cu_sub (x:var) (n:nat) (c:posi) (M:nat -> bool) := CU c (rz_sub x n M).

Definition rz_modadder_alt (c1:posi) (x:var) (n:nat) (c:posi) (A:nat -> bool) (M:nat -> bool) :=
  Exp (one_cu_adder x n c1 A; (rz_sub x n M)) ;; qft_cu x c ;; Exp (one_cu_adder x n c M; one_cu_sub x n c1 A)
      ;; qft_acu x c;; (Exp (one_cu_adder x n c1 A)).

Fixpoint rz_modmult_alt' (y:var) (x:var) (n:nat) (size:nat) (c:posi) (A:nat) (M:nat) :=
   match n with
   | 0 => Exp (SKIP (y,0))
   | S m => rz_modmult_alt' y x m size c A M;;
            rz_modadder_alt (x,size-n) y size c (nat2fb ((2^m * A) mod M)) (nat2fb M)
   end.

Definition rz_modmult_half_alt y x size c A M := 
   QFT y ;; rz_modmult_alt' y x size size c A M ;; RQFT y.

Definition rz_modmult_full_alt (y:var) (x:var) (n:nat) (c:posi) (A:nat) (Ainv :nat) (N:nat) :=
  rz_modmult_half_alt y x n c A N ;; inv_pexp (rz_modmult_half_alt x y n c Ainv N).

Definition real_rz_modmult_rev_alt (M C Cinv size:nat) :=
    rz_modmult_full_alt y_var x_var size (z_var,0) C Cinv M.

Definition trans_rz_modmult_rev_alt (M C Cinv size:nat) :=
        trans_pexp (vars_for_rz size) (2*size+1) (real_rz_modmult_rev_alt M C Cinv size) (avs_for_arith size).


(*********** Proofs ***********)

Fixpoint natsum n (f : nat -> nat) :=
  match n with
  | 0 => 0
  | S n' => f n' + natsum n' f
  end.

Lemma natsum_mod :
  forall n f M,
    M <> 0 ->
    (natsum n f) mod M = natsum n (fun i => f i mod M) mod M.
Proof.
  induction n; intros. easy.
  simpl. rewrite Nat.add_mod by easy. rewrite IHn by easy. 
  rewrite <- Nat.add_mod by easy. rewrite Nat.add_mod_idemp_l by easy. easy.
Qed.

Lemma parity_decompose :
  forall n, exists k, n = 2 * k \/ n = 2 * k + 1.
Proof.
  induction n. exists 0. lia. 
  destruct IHn as [k [H | H]]. exists k. lia. exists (S k). lia.
Qed.

Lemma Natodd_Ntestbit_even :
  forall k, Nat.odd (2 * k) = N.testbit (N.of_nat (2 * k)) 0.
Proof.
  induction k. easy.
  replace (2 * (S k)) with (S (S (2 * k))) by lia.
  rewrite Nat.odd_succ_succ. rewrite IHk.
  do 2 rewrite N.bit0_odd.
  replace (N.of_nat (S (S (2 * k)))) 
   with (N.succ (N.succ (N.of_nat (2 * k)))) by lia.
   rewrite N.odd_succ_succ. easy.
Qed.

Lemma Natodd_Ntestbit_odd :
  forall k, Nat.odd (2 * k + 1) = N.testbit (N.of_nat (2 * k + 1)) 0.
Proof.
  induction k. easy.
  replace (2 * (S k) + 1) with (S (S (2 * k + 1))) by lia.
  rewrite Nat.odd_succ_succ. rewrite IHk.
  do 2 rewrite N.bit0_odd.
  replace (N.of_nat (S (S (2 * k + 1)))) 
     with (N.succ (N.succ (N.of_nat (2 * k + 1)))) by lia.
  rewrite N.odd_succ_succ. easy.
Qed.

Lemma nat_is_odd_testbit:
  forall n, N.testbit (N.of_nat n) 0 = true -> Nat.odd n = true.
Proof.
  intros.
  specialize (parity_decompose n) as [k [Hk | Hk]]; subst.
  rewrite Natodd_Ntestbit_even.
  assumption.
  rewrite Natodd_Ntestbit_odd.
  assumption.
Qed.

Lemma nat_is_even_testbit:
  forall n, N.testbit (N.of_nat n) 0 = false -> Nat.even n = true.
Proof.
  intros.
  assert (Nat.odd n = false).
  specialize (parity_decompose n) as [k [Hk | Hk]]; subst.
  rewrite Natodd_Ntestbit_even.
  assumption.
  rewrite Natodd_Ntestbit_odd.
  assumption.
  unfold Nat.odd in H0.
  apply negb_false_iff in H0.
  assumption.
Qed.

Lemma Nattestbit_Ntestbit :
  forall m n,
    Nat.testbit n m = N.testbit (N.of_nat n) (N.of_nat m).
Proof.
  induction m; intros. simpl. specialize (parity_decompose n) as [k [Hk | Hk]]; subst.
   apply Natodd_Ntestbit_even. apply Natodd_Ntestbit_odd.
  remember (N.of_nat (S m)) as NSm. simpl. rewrite IHm. rewrite Nnat.Nat2N.inj_div2.
   rewrite <- N.testbit_succ_r_div2 by lia. subst. rewrite Nnat.Nat2N.inj_succ. easy.
Qed.  

Definition bindecomp n x := natsum n (fun i => Nat.b2n ((nat2fb x) i) * 2^i).

Lemma bindecomp_spec :
  forall n x,
    bindecomp n x = x mod 2^n.
Proof.
  unfold bindecomp. induction n; intros. easy.
  simpl. rewrite IHn. unfold nat2fb. rewrite N2fb_Ntestbit. rewrite <- Nattestbit_Ntestbit.
  rewrite Nat.testbit_spec'. replace (2 ^ n + (2 ^ n + 0)) with ((2 ^ n) * 2) by lia. 
  rewrite Nat.mod_mul_r. lia. apply Nat.pow_nonzero. easy. easy.
Qed.

Lemma bindecomp_seq :
  forall n x, bindecomp (S n) x = bindecomp n x + Nat.b2n ((nat2fb x) n) * 2^n.
Proof.
 intros.
 unfold bindecomp.
 simpl. lia.
Qed.

Lemma f_num_nat2fb : forall n f, (forall i, i >= n -> f i = false) -> (exists x, f = nat2fb x).
Proof.
  intros.
  specialize (f_num_0 f n) as eq1.
  destruct eq1.
  assert (f = cut_n f n).
  unfold cut_n.
  apply functional_extensionality; intro.
  bdestruct (x0 <? n). easy.
  rewrite H. easy. easy.
  exists x. rewrite H1. easy.
Qed.

Lemma add_to_sem : forall n q r, 0 < q <= n ->
                 (forall i , i >= n -> r i = false) ->
                 (addto r q) = cut_n (fbrev n (sumfb false (fbrev n r) (nat2fb (2^(n-q))))) n.
Proof.
  intros. unfold cut_n,addto,fbrev.
  apply functional_extensionality; intro.
  bdestruct (x <? q).
  bdestruct (x <? n).
Admitted. 

Lemma add_to_n_sem : forall n q r, 0 < q <= n ->
                 (forall i , i >= n -> r i = false) ->
                 (addto_n r q) = cut_n (fbrev n (sumfb false (fbrev n r) (nat2fb (2^n - 2^(n-q))))) n.
Proof.
  intros. unfold addto_n.
  apply functional_extensionality; intro.
  bdestruct (x <? q).
  rewrite negatem_arith.
  assert ((forall i : nat, i >= n -> fbrev q r i = false)).
  intros. unfold fbrev.
  bdestruct (i <? q). lia. rewrite H0. easy. lia.
  specialize (f_num_nat2fb n (fbrev q r) H2) as eq1.
  destruct eq1.
  rewrite H3.
  rewrite cut_n_mod.
  assert (2 ^ q <> 0).
  apply Nat.pow_nonzero. lia.
  rewrite sumfb_correct_carry0.
  assert ((2 ^ q - 1 - 0) = ((2 ^ q -1) mod 2^q)).
  rewrite Nat.mod_small by lia.
  lia. rewrite H5.
  rewrite cut_n_fbrev_flip.
  rewrite cut_n_mod.
  rewrite <- Nat.add_mod by lia.
  assert (forall i : nat, i >= n -> fbrev n r i = false).
  intros. unfold fbrev.
  bdestruct (i <? n). lia. rewrite H0. easy. lia.
  specialize (f_num_nat2fb n (fbrev n r) H6) as eq2.
  destruct eq2.
  rewrite H7.
  rewrite sumfb_correct_carry0.
  rewrite cut_n_fbrev_flip.
  rewrite cut_n_mod.
  Check Nat.add_mod.
Admitted. 

Lemma sumfb_assoc : forall f g h n, 
          (forall i, i >= n -> f i = false) -> (forall i, i >= n -> g i = false) 
             -> (forall i, i >= n -> h i = false) ->
         sumfb false f (sumfb false g h) = sumfb false (sumfb false f g) h. 
Proof.
  intros.
  rewrite <- (cut_n_eq n f).
  rewrite <- (cut_n_eq n g).
  rewrite <- (cut_n_eq n h).
  specialize (f_num_0 f n) as eq1.
  specialize (f_num_0 g n) as eq2.
  specialize (f_num_0 h n) as eq3.
  destruct eq1. destruct eq2. destruct eq3.
  rewrite H2. rewrite H3. rewrite H4.
  repeat rewrite sumfb_correct_carry0.
  rewrite plus_assoc. easy.
  easy. easy. easy.
Qed.

Definition get_phi_r (v:val) := match v with qval r1 r2 => r2 | _ => allfalse end.

Lemma sr_rotate_get_r : forall n size f x, 0 < n <= size -> get_r_qft (sr_rotate' f x n size) x
                 = get_phi_r (times_rotate (f (x,0)) size).
Proof.
  induction n;intros; simpl. lia.
  unfold get_r_qft.
  bdestruct (n =? 0). subst. 
  rewrite eupdate_index_eq.
  unfold get_phi_r.
  assert (size - 0=size) by lia. rewrite H0. easy.
  rewrite eupdate_index_neq by iner_p.
  unfold get_r_qft in IHn. rewrite IHn. easy. lia.
Qed.

Lemma sr_rotate'_phi : forall m n size f x, m <= n <= size -> phi_modes f x size
             -> phi_modes ((sr_rotate' f x m n)) x size.
Proof.
  induction m; intros ; simpl; try easy.
  unfold phi_modes in *. intros.
  unfold phi_mode in *. 
  bdestruct (m =? i). subst.
  rewrite eupdate_index_eq.
  unfold times_rotate.
  apply H0 in H1. destruct (f (x,i)) eqn:eq1. lia. lia. lia.
  rewrite eupdate_index_neq by iner_p.
  apply IHm with (size := size). lia. easy. lia.
Qed.

Lemma rz_adder_well_typed : forall n x size M f aenv tenv, n <= size ->
             phi_modes f x size -> well_typed_exp tenv (rz_adder' x n size M)
             -> right_mode_env aenv tenv f -> phi_modes (exp_sem aenv (rz_adder' x n size M) f) x size.
Proof.
  induction n; intros.
  simpl in *. easy.
  simpl in *.
  inv H1.
  specialize (IHn x size M f aenv tenv).
  assert (n <= size) by lia.
  specialize (IHn H1 H0 H6 H2).
  unfold phi_modes in *. 
  intros.
  unfold phi_mode in *.
  destruct (M n) eqn:eq1. simpl.
  unfold sr_rotate.
  specialize (sr_rotate'_phi (S (size - S n)) (S (size - S n)) size 
                 (exp_sem aenv (rz_adder' x n size M) f) x) as eq2.
  assert (S (size - S n) <= S (size - S n) <= size) by lia.
  assert (phi_modes (exp_sem aenv (rz_adder' x n size M) f) x size).
  unfold phi_modes. unfold phi_mode. apply IHn.
  specialize (eq2 H4 H5).
  unfold phi_modes in eq2. unfold phi_mode in eq2. apply eq2; try lia.
  simpl. apply IHn; lia.
Qed. 

Lemma rz_adder_gt : forall n size aenv M f x, n <= size ->
                (forall i, i >= size -> get_r_qft f x i = false) ->
               (forall i, i >= size -> get_r_qft (exp_sem aenv (rz_adder' x n size M) f) x i = false).
Proof.
  induction n; intros; simpl.
  unfold get_r_qft in *.
  destruct (f (x,0)). easy. easy. rewrite H0. easy. easy.
  destruct (M n). simpl.
  unfold sr_rotate.
  rewrite sr_rotate_get_r ; try lia.
  unfold get_r_qft in IHn.
  destruct ((exp_sem aenv (rz_adder' x n size M) f (x, 0))) eqn:eq1.
  unfold get_phi_r. 
  unfold times_rotate. destruct b. easy. easy.
  unfold get_phi_r.
  unfold times_rotate. easy.
  unfold get_phi_r.
  unfold times_rotate.
  specialize (IHn size aenv M f x).
  assert (n <= size) by lia.
  specialize (IHn H2).
  rewrite eq1 in IHn.
  specialize (IHn H0).
  assert ((S (size - S n)) = size - n) by lia.
  rewrite H3.
  unfold rotate,addto.
  bdestruct (i <? size - n). lia. rewrite IHn. easy. lia.
  simpl. apply IHn. lia. apply H0. lia.
Qed.

Lemma rz_adder_sem : forall n size f x A M aenv tenv, n <= size -> phi_modes f x size ->
                 (forall i, i <= size -> well_typed_exp tenv (rz_adder' x i size (nat2fb M)))
                   -> right_mode_env aenv tenv f ->
                  M < 2^size -> A < 2^size ->
                  fbrev size (get_r_qft f x) = nat2fb A ->
                  (get_r_qft (exp_sem aenv (rz_adder' x n size (nat2fb M)) f) x)
                    = (fbrev size (nat2fb ((A + (bindecomp n M)) mod 2^size))).
Proof.
  induction n;intros;simpl.
  unfold bindecomp. simpl.
  rewrite plus_0_r.
  rewrite Nat.mod_small by lia.
  rewrite <- H5.
  rewrite fbrev_twice_same. easy.
  destruct (nat2fb M n) eqn:eq1.
  simpl.
  unfold sr_rotate.
  rewrite sr_rotate_get_r by lia.
  unfold get_phi_r.
  specialize (IHn size f x A M aenv tenv).
  assert (n <= size) by lia.
  specialize (IHn H6 H0 H1 H2 H3 H4 H5).
  unfold get_r_qft in IHn.
  specialize (H1 n H6).
  apply rz_adder_well_typed with (aenv:=aenv) (f:= f) in H1 as eq3; try easy.
  unfold phi_modes in eq3. assert (0 < size) by lia. specialize (eq3 0 H7).
  unfold phi_mode in eq3.
  specialize (rz_adder_gt n size aenv (nat2fb M) f x) as X1.
  assert (n <= size) by lia.
  specialize (X1 H6).
  assert ((forall i : nat, i >= size -> get_r_qft f x i = false)).
  intros.
  specialize (nat2fb_bound size A H4 i H9) as X2.
  rewrite <- H5 in X2.
  unfold fbrev in X2. bdestruct (i <? size). lia.
  easy. specialize (X1 H9).
  unfold get_r_qft in X1.
  destruct (exp_sem aenv (rz_adder' x n size (nat2fb M)) f (x, 0)) eqn:eq2. lia. lia.
  unfold times_rotate,rotate.
  rewrite (add_to_sem size); (try easy; try lia).
  rewrite cut_n_fbrev_flip.
  rewrite IHn. rewrite fbrev_twice_same.
  rewrite sumfb_correct_carry0.
  assert ((size - S (size - S n)) = n) by lia.
  rewrite H10.
  rewrite bindecomp_seq. rewrite eq1. simpl.
  rewrite plus_0_r.
  rewrite cut_n_mod.
  assert (2 ^ n = 2 ^ n mod 2 ^ size).
  rewrite Nat.mod_small. easy.
  apply Nat.pow_lt_mono_r; try lia. 
  assert (((A + bindecomp n M) mod 2 ^ size + 2 ^ n)
          = ((A + bindecomp n M) mod 2 ^ size + 2 ^ n mod 2^size)).
  rewrite <- H11. easy. rewrite H12.
  rewrite <- Nat.add_mod by lia.
  rewrite plus_assoc. easy.
  simpl.
  rewrite IHn with (A := A) (tenv:=tenv); try easy.
  rewrite bindecomp_seq.
  rewrite eq1. simpl. rewrite plus_0_r. easy. lia.
Qed.

Lemma well_typed_exp_rz_adder_aux : forall m size tenv f x M, S m <= size 
            -> phi_modes f x size
           -> well_typed_exp tenv (rz_adder' x (S m) size (nat2fb M))
            -> well_typed_exp tenv (rz_adder' x m size (nat2fb M)).
Proof.
 induction m;intros. simpl. constructor.
 simpl. constructor.
 apply IHm with (f:=f). lia. easy.
 inv H1. inv H5. simpl. constructor. easy. easy.
 simpl in H1. inv H1. inv H5.
 easy.
Qed.

Lemma well_typed_exp_rz_adder_1 : forall m n size tenv f x M, m+n <= size 
            -> phi_modes f x size
           -> well_typed_exp tenv (rz_adder' x (m + n) size (nat2fb M))
            -> well_typed_exp tenv (rz_adder' x m size (nat2fb M)).
Proof.
 induction n;intros.
 rewrite plus_0_r in H1. easy.
 assert ((m + S n) = S (m + n)) by lia.
 rewrite H2 in H1.
 simpl in H1.
 apply IHn with (f := f) ; try lia. easy.
 inv H1. easy.
Qed.

Lemma well_typed_exp_rz_adder : forall size tenv f x M, phi_modes f x size
           -> well_typed_exp tenv (rz_adder x size (nat2fb M))
            -> (forall i, i <= size -> well_typed_exp tenv (rz_adder' x i size (nat2fb M))).
Proof.
 intros.
 remember (size - i) as n.
 unfold rz_adder in H1.
 assert ((rz_adder' x size size (nat2fb M)) = (rz_adder' x (i + (size - i)) size (nat2fb M))).
 assert (i + (size - i)= size) by lia. rewrite H2. easy.
 unfold rz_adder in H0.
 rewrite H2 in H0.
 apply well_typed_exp_rz_adder_1 with (f:=f) in H0. easy. lia. easy.
Qed.

Lemma rz_adder_full : forall size f x A M aenv tenv, phi_modes f x size ->
                   well_typed_exp tenv (rz_adder x size (nat2fb M))
                   -> right_mode_env aenv tenv f ->
                  M < 2^size -> A < 2^size ->
                  fbrev size (get_r_qft f x) = nat2fb A ->
                  (get_r_qft (exp_sem aenv (rz_adder x size (nat2fb M)) f) x)
                    = (fbrev size (nat2fb ((A + M) mod 2^size))).
Proof.
  intros. unfold rz_adder. rewrite rz_adder_sem with (A:=A) (tenv := tenv); try easy.
  rewrite bindecomp_spec.
  rewrite (Nat.mod_small M) by easy. easy.
  apply well_typed_exp_rz_adder with (f:=f); easy.
Qed.

Lemma srr_rotate_get_r : forall n size f x, 0 < n <= size -> get_r_qft (srr_rotate' f x n size) x
                 = get_phi_r (times_r_rotate (f (x,0)) size).
Proof.
  induction n;intros; simpl. lia.
  unfold get_r_qft.
  bdestruct (n =? 0). subst. 
  rewrite eupdate_index_eq.
  unfold get_phi_r.
  assert (size - 0=size) by lia. rewrite H0. easy.
  rewrite eupdate_index_neq by iner_p.
  unfold get_r_qft in IHn. rewrite IHn. easy. lia.
Qed.

Lemma srr_rotate'_phi : forall m n size f x, m <= n <= size -> phi_modes f x size
             -> phi_modes ((srr_rotate' f x m n)) x size.
Proof.
  induction m; intros ; simpl; try easy.
  unfold phi_modes in *. intros.
  unfold phi_mode in *. 
  bdestruct (m =? i). subst.
  rewrite eupdate_index_eq.
  unfold times_r_rotate.
  apply H0 in H1. destruct (f (x,i)) eqn:eq1. lia. lia. lia.
  rewrite eupdate_index_neq by iner_p.
  apply IHm with (size := size). lia. easy. lia.
Qed.

Lemma rz_sub_well_typed : forall n x size M f aenv tenv, n <= size ->
             phi_modes f x size -> well_typed_exp tenv (rz_sub' x n size M)
             -> right_mode_env aenv tenv f -> phi_modes (exp_sem aenv (rz_sub' x n size M) f) x size.
Proof.
  induction n; intros.
  simpl in *. easy.
  simpl in *.
  inv H1.
  specialize (IHn x size M f aenv tenv).
  assert (n <= size) by lia.
  specialize (IHn H1 H0 H6 H2).
  unfold phi_modes in *. 
  intros.
  unfold phi_mode in *.
  destruct (M n) eqn:eq1. simpl.
  unfold srr_rotate.
  specialize (srr_rotate'_phi (S (size - S n)) (S (size - S n)) size 
                 (exp_sem aenv (rz_sub' x n size M) f) x) as eq2.
  assert (S (size - S n) <= S (size - S n) <= size) by lia.
  assert (phi_modes (exp_sem aenv (rz_sub' x n size M) f) x size).
  unfold phi_modes. unfold phi_mode. apply IHn.
  specialize (eq2 H4 H5).
  unfold phi_modes in eq2. unfold phi_mode in eq2. apply eq2; try lia.
  simpl. apply IHn; lia.
Qed. 

Lemma rz_sub_gt : forall n size aenv M f x, n <= size ->
                (forall i, i >= size -> get_r_qft f x i = false) ->
               (forall i, i >= size -> get_r_qft (exp_sem aenv (rz_sub' x n size M) f) x i = false).
Proof.
  induction n; intros; simpl.
  unfold get_r_qft in *.
  destruct (f (x,0)). easy. easy. rewrite H0. easy. easy.
  destruct (M n). simpl.
  unfold srr_rotate.
  rewrite srr_rotate_get_r ; try lia.
  unfold get_r_qft in IHn.
  destruct ((exp_sem aenv (rz_sub' x n size M) f (x, 0))) eqn:eq1.
  unfold get_phi_r. 
  unfold times_r_rotate. destruct b. easy. easy.
  unfold get_phi_r.
  unfold times_r_rotate. easy.
  unfold get_phi_r.
  unfold times_r_rotate.
  specialize (IHn size aenv M f x).
  assert (n <= size) by lia.
  specialize (IHn H2).
  rewrite eq1 in IHn.
  specialize (IHn H0).
  assert ((S (size - S n)) = size - n) by lia.
  rewrite H3.
  unfold r_rotate,addto_n.
  bdestruct (i <? size - n). lia. rewrite IHn. easy. lia.
  simpl. apply IHn. lia. apply H0. lia.
Qed.

Lemma rz_sub_sem : forall n size f x A M aenv tenv, n <= size -> phi_modes f x size ->
                 (forall i, i <= size -> well_typed_exp tenv (rz_sub' x i size (nat2fb M)))
                   -> right_mode_env aenv tenv f ->
                  M < 2^size -> A < 2^size ->
                  fbrev size (get_r_qft f x) = nat2fb A ->
                  (get_r_qft (exp_sem aenv (rz_sub' x n size (nat2fb M)) f) x)
                    = (fbrev size (nat2fb ((A + 2^size - (bindecomp n M)) mod 2^size))).
Proof.
  induction n;intros;simpl.
  unfold bindecomp. simpl.
  assert ((A + 2 ^ size - 0) = A + 2^size) by lia. rewrite H6.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small by lia.
  rewrite <- H5.
  rewrite fbrev_twice_same. easy.
  destruct (nat2fb M n) eqn:eq1.
  simpl.
  unfold srr_rotate.
  rewrite srr_rotate_get_r by lia.
  unfold get_phi_r.
  specialize (IHn size f x A M aenv tenv).
  assert (n <= size) by lia.
  specialize (IHn H6 H0 H1 H2 H3 H4 H5).
  unfold get_r_qft in IHn.
  specialize (H1 n H6).
  apply rz_sub_well_typed with (aenv:=aenv) (f:= f) in H1 as eq3; try easy.
  unfold phi_modes in eq3. assert (0 < size) by lia. specialize (eq3 0 H7).
  unfold phi_mode in eq3.
  specialize (rz_sub_gt n size aenv (nat2fb M) f x) as X1.
  assert (n <= size) by lia.
  specialize (X1 H6).
  assert ((forall i : nat, i >= size -> get_r_qft f x i = false)).
  intros.
  specialize (nat2fb_bound size A H4 i H9) as X2.
  rewrite <- H5 in X2.
  unfold fbrev in X2. bdestruct (i <? size). lia.
  easy. specialize (X1 H9).
  unfold get_r_qft in X1.
  destruct (exp_sem aenv (rz_sub' x n size (nat2fb M)) f (x, 0)) eqn:eq2. lia. lia.
  unfold times_r_rotate,r_rotate.
  rewrite (add_to_n_sem size); (try easy; try lia).
  rewrite cut_n_fbrev_flip.
  rewrite IHn. rewrite fbrev_twice_same.
  rewrite sumfb_correct_carry0.
  assert ((size - S (size - S n)) = n) by lia.
  rewrite H10.
  rewrite bindecomp_seq. rewrite eq1. simpl.
  rewrite plus_0_r.
  rewrite cut_n_mod.
  assert (2^n < 2^size).
  apply Nat.pow_lt_mono_r_iff. lia. lia.
  assert (2 ^ n <> 0).
  apply Nat.pow_nonzero. lia.
  assert ((2 ^ size - 2 ^ n) = (2 ^ size - 2 ^ n) mod 2 ^ size).
  rewrite Nat.mod_small. easy. lia.
  rewrite H13.
  rewrite <- Nat.add_mod by lia.
  assert (bindecomp n M < 2^n).
  rewrite bindecomp_spec.
  apply Nat.mod_upper_bound ; lia.
  assert (2 ^ S n <= 2^size).
  apply Nat.pow_le_mono_r; lia.
  simpl in H15.
  assert (A + 2 ^ size - bindecomp n M + (2 ^ size - 2 ^ n) = 
           (2 ^ size + (A + 2 ^ size - (bindecomp n M + 2 ^ n)))) by lia.
  rewrite H16.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia. rewrite plus_0_l.
  rewrite Nat.mod_mod by lia. easy.
  simpl.
  rewrite IHn with (A := A) (tenv:=tenv); try easy.
  rewrite bindecomp_seq.
  rewrite eq1. simpl. rewrite plus_0_r. easy. lia.
Qed.


Lemma well_typed_exp_rz_sub_aux : forall m size tenv f x M, S m <= size 
            -> phi_modes f x size
           -> well_typed_exp tenv (rz_sub' x (S m) size (nat2fb M))
            -> well_typed_exp tenv (rz_sub' x m size (nat2fb M)).
Proof.
 induction m;intros. simpl. constructor.
 simpl. constructor.
 apply IHm with (f:=f). lia. easy.
 inv H1. inv H5. simpl. constructor. easy. easy.
 simpl in H1. inv H1. inv H5.
 easy.
Qed.

Lemma well_typed_exp_rz_sub_1 : forall m n size tenv f x M, m+n <= size 
            -> phi_modes f x size
           -> well_typed_exp tenv (rz_sub' x (m + n) size (nat2fb M))
            -> well_typed_exp tenv (rz_sub' x m size (nat2fb M)).
Proof.
 induction n;intros.
 rewrite plus_0_r in H1. easy.
 assert ((m + S n) = S (m + n)) by lia.
 rewrite H2 in H1.
 simpl in H1.
 apply IHn with (f := f) ; try lia. easy.
 inv H1. easy.
Qed.

Lemma well_typed_exp_rz_sub : forall size tenv f x M, phi_modes f x size
           -> well_typed_exp tenv (rz_sub x size (nat2fb M))
            -> (forall i, i <= size -> well_typed_exp tenv (rz_sub' x i size (nat2fb M))).
Proof.
 intros.
 remember (size - i) as n.
 unfold rz_sub in H1.
 assert ((rz_sub' x size size (nat2fb M)) = (rz_sub' x (i + (size - i)) size (nat2fb M))).
 assert (i + (size - i)= size) by lia. rewrite H2. easy.
 unfold rz_sub in H0.
 rewrite H2 in H0.
 apply well_typed_exp_rz_sub_1 with (f:=f) in H0. easy. lia. easy.
Qed.

Lemma rz_sub_full : forall size f x A M aenv tenv, phi_modes f x size ->
                    well_typed_exp tenv (rz_sub x size (nat2fb M))
                   -> right_mode_env aenv tenv f ->
                  M < 2^size -> A < 2^size ->
                  fbrev size (get_r_qft f x) = nat2fb A ->
                  (get_r_qft (exp_sem aenv (rz_sub x size (nat2fb M)) f) x)
                    = (fbrev size (nat2fb ((A + 2^size - M) mod 2^size))).
Proof.
  intros. unfold rz_sub. rewrite rz_sub_sem with (A:=A) (tenv := tenv); try easy.
  rewrite bindecomp_spec.
  rewrite (Nat.mod_small M) by easy. easy.
  apply well_typed_exp_rz_sub with (f := f); easy.
Qed.

Lemma efresh_rz_adder: forall n c x size M aenv, fst c <> x -> n <= size -> exp_fresh aenv c (rz_adder' x n size M).
Proof.
  induction n;intros; simpl.
  constructor. destruct c. iner_p.
  constructor. apply IHn. easy. lia.
  destruct (M n).
  constructor.
  unfold or_not_r. left. easy.
  constructor. destruct c. iner_p.
Qed.

Lemma efresh_rz_sub: forall n c x size M aenv, fst c <> x -> n <= size -> exp_fresh aenv c (rz_sub' x n size M).
Proof.
  induction n;intros; simpl.
  constructor. destruct c. iner_p.
  constructor. apply IHn. easy. lia.
  destruct (M n).
  constructor.
  unfold or_not_r. left. easy.
  constructor. destruct c. iner_p.
Qed.

Lemma highbit_means_lt : forall size X M, X < 2^ S size -> M < 2^size -> X < 2 * M 
         -> fbrev (S size) (nat2fb ((X + 2^S size - M) mod 2^S size)) 0 = (X <? M).
Proof.
  intros. unfold fbrev.
  bdestruct (0 <? size). simpl.
  assert ((size - 0 - 0) = size) by lia. rewrite H3.
  unfold nat2fb.
  rewrite N2fb_Ntestbit.
  bdestruct (X <? M).
  apply Ntestbit_in_pow2n_pow2Sn.
  assert ((2 ^ size + (2 ^ size + 0)) = 2^ S size). simpl. easy.
  rewrite H5.
  split.
  assert (2^size <= (X + 2 ^ S size - M) mod 2 ^ S size).
  assert ((X + 2 ^ S size - M) = 2^S size - (M - X)) by lia.
  rewrite H6.
  assert ((2 ^ S size - (M - X)) < 2 ^ S size) by lia.
  rewrite Nat.mod_small by lia.
  assert (M - X < 2^size) by lia. lia.
  assert (N.of_nat(2 ^ size) <= N.of_nat ((X + 2 ^ S size - M) mod 2 ^ S size))%N by lia.
  simpl in *. rewrite Nofnat_pow in H7. simpl in H7. lia.
  assert ((X + 2 ^ S size - M) mod 2 ^ S size < 2 ^ S size).
  apply Nat.mod_upper_bound. lia.
  assert (N.of_nat ((X + 2 ^ S size - M) mod 2 ^ S size) < N.of_nat (2 ^ S size))%N by lia.
  rewrite Nofnat_pow in H7. 
  assert (N.of_nat (S size) = N.succ (N.of_nat size)) by lia.
  rewrite H8 in H7. simpl in *. lia.
  apply Ntestbit_lt_pow2n.
  assert ((2 ^ size + (2 ^ size + 0)) = 2^ S size). simpl. easy.
  rewrite H5. clear H5.
  assert ((X + 2 ^ S size - M) mod 2 ^ S size < 2 ^ size).
  assert ((X + 2 ^ S size - M) = 2 ^ S size + (X - M)) by lia.
  rewrite H5. clear H5.
  assert (2^ size <> 0).
  apply Nat.pow_nonzero. lia.
  rewrite Nat.add_mod by (simpl;lia).
  rewrite Nat.mod_same by (simpl;lia).
  rewrite plus_0_l.
  rewrite Nat.mod_mod by (simpl;lia).
  rewrite Nat.mod_small by (simpl;lia).
  simpl. lia.
  assert (N.of_nat ((X + 2 ^ S size - M) mod 2 ^ S size) < N.of_nat (2 ^ size))%N by lia.
  rewrite Nofnat_pow in H6. 
  simpl in *. lia. 
  bdestruct (0 <? S size).
  assert (size = 0) by lia. subst. simpl in *. lia.
  lia.
Qed.

Lemma rz_compare_half_sem : forall size f c x A M aenv l l' tenv tenv',
                    phi_modes f x (S size) -> aenv x = S size -> fst c <> x
                     -> nor_mode f c -> get_cua (f c) = false ->
                    well_typed_pexp aenv l tenv (rz_compare_half x (S size) c M) l' tenv'
                   -> right_mode_env aenv tenv f ->
                  M < 2^size -> A < 2^S size -> A < 2*M ->
                  fbrev (S size) (get_r_qft f x) = nat2fb A ->
                  get_cua ((prog_sem aenv (rz_compare_half x (S size) c M) f) c) = (A <? M).
Proof.
  intros. unfold rz_compare_half. 
  remember (rz_sub x (S size) (nat2fb M)) as e1. simpl.
  rewrite Heqe1. clear Heqe1.
  unfold turn_rqft.
  inv H4. inv H14. inv H13.
  rewrite rz_sub_full with (A:=A) (tenv:= env'0); try easy.
  rewrite H0.
  rewrite cnot_sem.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  rewrite assign_seq_lt by lia.
  rewrite assign_seq_out by iner_p.
  rewrite efresh_exp_sem_irrelevant with (p := c).
  rewrite H3.
  unfold get_cua. bt_simpl.
  unfold fbrev. bdestruct (0 <? S size). simpl.
  assert ((size - 0 - 0) = size) by lia. rewrite H12.
  rewrite <- highbit_means_lt with (size := size); try easy.
  unfold fbrev.
  bdestruct (0 <? S size). simpl.
  rewrite H12. easy. lia. lia.
  apply efresh_rz_sub; try easy.
  unfold nor_mode.
  rewrite assign_seq_out by iner_p.
  rewrite efresh_exp_sem_irrelevant with (p := c).
  apply H2.
  apply efresh_rz_sub; try easy.
  unfold nor_mode.
  rewrite assign_seq_lt by lia. lia.
  unfold nor_mode.
  rewrite assign_seq_out by iner_p.
  rewrite efresh_exp_sem_irrelevant with (p := c).
  apply H2.
  apply efresh_rz_sub; try easy.
  simpl. lia.
Qed.

Lemma rz_compare_sem : forall size f c x A M aenv l l' tenv tenv',
                    phi_modes f x (S size) -> aenv x = S size -> fst c <> x
                     -> nor_mode f c -> get_cua (f c) = false ->
                    well_typed_pexp aenv l tenv (rz_compare_half x (S size) c M) l' tenv'
                   -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
                  pexp_fresh aenv c (Exp (rz_sub x (S size) (nat2fb M));; RQFT x) ->
                  M < 2^size -> A < 2^size ->
                  fbrev (S size) (get_r_qft f x) = nat2fb A ->
                  well_formed_ls l -> exp_neu_prop l ->
                     prog_sem aenv (rz_compare x (S size) c M) f = f[c|-> put_cu (f c) (A <? M)].
Proof.
  intros. unfold rz_compare. unfold rz_compare_half in *. 
  inv H4.
  remember (rz_sub x (S size) (nat2fb M);; RQFT x) as e1. 
  remember (prog_sem aenv e1 f) as g.
  simpl.
  rewrite <- Heqg.
  rewrite cnot_sem.
  rewrite inv_pexp_reverse_1 with (tenv:= tenv) (tenv' := env') (f:=f) (l := l) (l' := l'0); try easy.
  rewrite Heqg.
  rewrite Heqe1 in *.
  remember (rz_sub x (S size) (nat2fb M)) as e2. simpl in *.
  unfold turn_rqft.
  inv H18. inv H17.
  rewrite rz_sub_full with (A:=A) (tenv:= env'0); try easy.
  rewrite H0.
  rewrite assign_seq_lt by lia.
  rewrite assign_seq_out by iner_p.
  rewrite efresh_exp_sem_irrelevant with (p := c).
  rewrite H3.
  unfold get_cua. bt_simpl.
  unfold fbrev. bdestruct (0 <? S size). simpl.
  assert ((size - 0 - 0) = size) by lia. rewrite H16.
  assert ((nat2fb ((A + (2 ^ size + (2 ^ size + 0)) - M)
                mod (2 ^ size + (2 ^ size + 0))) size) = (A <? M)).
  unfold nat2fb.
  rewrite N2fb_Ntestbit.
  bdestruct (A <? M).
  apply Ntestbit_in_pow2n_pow2Sn.
  assert ((2 ^ size + (2 ^ size + 0)) = 2^ S size). simpl. easy.
  rewrite H18.
  split.
  assert (2^size <= (A + 2 ^ S size - M) mod 2 ^ S size).
  assert ((A + 2 ^ S size - M) = 2^S size - (M - A)) by lia.
  rewrite H20.
  assert ((2 ^ S size - (M - A)) < 2 ^ S size) by lia.
  rewrite Nat.mod_small by lia.
  assert (M - A < 2^size) by lia. lia.
  assert (N.of_nat(2 ^ size) <= N.of_nat ((A + 2 ^ S size - M) mod 2 ^ S size))%N by lia.
  simpl in *. rewrite Nofnat_pow in H23. simpl in H23. lia.
  assert ((A + 2 ^ S size - M) mod 2 ^ S size < 2 ^ S size).
  apply Nat.mod_upper_bound. lia.
  assert (N.of_nat ((A + 2 ^ S size - M) mod 2 ^ S size) < N.of_nat (2 ^ S size))%N by lia.
  rewrite Nofnat_pow in H23. 
  assert (N.of_nat (S size) = N.succ (N.of_nat size)) by lia.
  rewrite H24 in H23. simpl in *. lia.
  apply Ntestbit_lt_pow2n.
  assert ((2 ^ size + (2 ^ size + 0)) = 2^ S size). simpl. easy.
  rewrite H18. clear H18.
  assert ((A + 2 ^ S size - M) mod 2 ^ S size < 2 ^ size).
  assert ((A + 2 ^ S size - M) = 2 ^ S size + (A - M)) by lia.
  rewrite H18. clear H18.
  assert (2^ size <> 0).
  apply Nat.pow_nonzero. lia.
  rewrite Nat.add_mod by (simpl;lia).
  rewrite Nat.mod_same by (simpl;lia).
  rewrite plus_0_l.
  rewrite Nat.mod_mod by (simpl;lia).
  rewrite Nat.mod_small by (simpl;lia).
  simpl. lia.
  assert (N.of_nat ((A + 2 ^ S size - M) mod 2 ^ S size) < N.of_nat (2 ^ size))%N by lia.
  rewrite Nofnat_pow in H20. 
  simpl in *. lia. rewrite H17. easy. lia.
  inv H8. inv H18. easy. simpl. lia. simpl. lia.
  subst. simpl. unfold turn_rqft.
  unfold nor_mode. simpl.
  rewrite assign_seq_lt. lia. rewrite H0. lia.
  subst.
  unfold nor_mode.
  rewrite fresh_pexp_sem_irrelevant with (p := c).
  apply H2. easy.
Qed.


(*phi_mode proofs.*)

Inductive exp_scope (aenv: var -> nat) : var -> nat -> exp -> Prop :=
    | skip_scope : forall x n p, exp_scope aenv x n (SKIP p)
    | x_scope : forall x n p, exp_scope aenv x n (X p)
    | sr_scope : forall x n y m, exp_scope aenv x n (SR m y)
    | srr_scope : forall x n y m, exp_scope aenv x n (SRR m y)
    | lshift_scope_hit : forall x n, 0 < aenv x <= n -> exp_scope aenv x n (Lshift x)
    | lshift_scope_nhit : forall x n y, x <> y -> exp_scope aenv x n (Lshift y)
    | rshift_scope_hit : forall x n, 0 < aenv x <= n -> exp_scope aenv x n (Rshift x)
    | rshift_scope_nhit : forall x n y, x <> y -> exp_scope aenv x n (Rshift y)
    | rev_scope_hit : forall x n, 0 < aenv x <= n -> exp_scope aenv x n (Rev x)
    | rev_scope_nhit : forall x n y, x <> y -> exp_scope aenv x n (Rev y)
    | cu_scope : forall x n p e, exp_scope aenv x n e -> exp_scope aenv x n (CU p e)
    | hcnot_scope : forall x n p1 p2, exp_scope aenv x n (HCNOT p1 p2)
    | rz_scope : forall x n q p, exp_scope aenv x n (RZ q p)
    | rrz_scope : forall x n q p, exp_scope aenv x n (RRZ q p)
    | seq_scope : forall x n e1 e2, exp_scope aenv x n e1 -> exp_scope aenv x n e2 -> exp_scope aenv x n (Seq e1 e2).


Lemma escope_rz_adder: forall m x size M y n aenv, exp_scope aenv y n (rz_adder' x m size M).
Proof.
  induction m;intros; simpl. constructor.
  constructor. apply IHm.
  destruct (M m).  constructor. constructor.
Qed.

Lemma escope_rz_sub: forall m x size M y n aenv, exp_scope aenv y n (rz_sub' x m size M).
Proof.
  induction m;intros; simpl. constructor.
  constructor. apply IHm.
  destruct (M m).  constructor. constructor.
Qed.

Lemma sr_rotate'_phi_modes : forall n size f x y m, phi_modes f y m -> phi_modes (sr_rotate' f x n size) y m.
Proof.
  induction n;intros;simpl. easy.
  unfold phi_modes in *.
  intros.
  unfold phi_mode in *.
  bdestruct ((y,i) ==? (x,n)). rewrite H1.
  rewrite eupdate_index_eq.
  unfold times_rotate.
  specialize (H n). inv H1. apply H in H0.
  destruct (f (x,n)); try lia.
  rewrite eupdate_index_neq by iner_p.
  apply IHn with (m := m). easy. lia.
Qed.

Lemma srr_rotate'_phi_modes : forall n size f x y m, phi_modes f y m -> phi_modes (srr_rotate' f x n size) y m.
Proof.
  induction n;intros;simpl. easy.
  unfold phi_modes in *.
  intros.
  unfold phi_mode in *.
  bdestruct ((y,i) ==? (x,n)). rewrite H1.
  rewrite eupdate_index_eq.
  unfold times_r_rotate.
  specialize (H n). inv H1. apply H in H0.
  destruct (f (x,n)); try lia.
  rewrite eupdate_index_neq by iner_p.
  apply IHn with (m := m). easy. lia.
Qed.

Lemma lshift'_phi_modes : forall n size f x y m, size < m -> phi_modes f y m -> phi_modes (lshift' n size f x) y m.
Proof.
  induction n;intros;simpl.
  unfold phi_modes in *.
  intros.
  unfold phi_mode in *.
  bdestruct ((y,i) ==? (x,0)). 
  rewrite H2.
  rewrite eupdate_index_eq.
  specialize (H0 size). apply H0 in H. inv H2. easy.
  rewrite eupdate_index_neq by iner_p.
  apply H0. lia.
  unfold phi_modes in *.
  intros.
  unfold phi_mode in *.
  bdestruct ((y, i) ==? (x, S n)). inv H2.
  rewrite eupdate_index_eq. apply H0. lia.
  rewrite eupdate_index_neq by iner_p. apply IHn with (m := m). lia.
  easy. lia.
Qed.

Lemma rshift'_phi_modes : forall n size f x y m, n <= size < m -> phi_modes f y m -> phi_modes (rshift' n size f x) y m.
Proof.
  induction n;intros;simpl.
  unfold phi_modes in *.
  intros.
  unfold phi_mode in *.
  bdestruct ((y,i) ==? (x,size)). 
  rewrite H2.
  rewrite eupdate_index_eq.
  specialize (H0 0). 
  assert (0 < m) by lia. apply H0 in H3. inv H2. easy.
  rewrite eupdate_index_neq by iner_p.
  apply H0. lia.
  unfold phi_modes in *.
  intros.
  unfold phi_mode in *.
  bdestruct ((y, i) ==? (x, n)). inv H2.
  rewrite eupdate_index_eq. apply H0. lia.
  rewrite eupdate_index_neq by iner_p. apply IHn with (m := m). lia.
  easy. lia.
Qed.

Lemma phi_modes_exp : forall e aenv f x size, exp_scope aenv x size e
           -> phi_modes f x size -> phi_modes (exp_sem aenv e f) x size.
Proof.
  induction e; intros.
  simpl; easy.
  simpl.
  unfold phi_modes in *.
  unfold phi_mode in *. intros.
  bdestruct (p ==? (x, i)).
  subst.
  rewrite eupdate_index_eq.
  unfold exchange.
  specialize (H0 i H1).
  destruct (f (x, i)); try lia.
  rewrite eupdate_index_neq by easy. apply H0. easy.
  simpl.
  destruct (get_cua (f p)). apply IHe. inv H. easy. easy. easy.
  simpl.
  unfold phi_modes in *.
  unfold phi_mode in *. intros.
  bdestruct (p ==? (x, i)).
  subst.
  rewrite eupdate_index_eq.
  unfold times_rotate.
  specialize (H0 i H1).
  destruct (f (x, i)); try lia.
  rewrite eupdate_index_neq by easy. apply H0. easy.
  simpl.
  unfold phi_modes in *.
  unfold phi_mode in *. intros.
  bdestruct (p ==? (x, i)).
  subst.
  rewrite eupdate_index_eq.
  unfold times_r_rotate.
  specialize (H0 i H1).
  destruct (f (x, i)); try lia.
  rewrite eupdate_index_neq by easy. apply H0. easy.
  simpl.
  apply sr_rotate'_phi_modes. easy.
  simpl.
  apply srr_rotate'_phi_modes. easy.
  simpl.
  unfold phi_modes in *.
  unfold phi_mode in *. intros.
  bdestruct (p1 ==? (x, i)).
  subst.
  rewrite eupdate_index_eq.
  unfold hexchange.
  specialize (H0 i H1).
  destruct (f (x, i)); try lia.
  rewrite eupdate_index_neq by easy. apply H0. easy.
  simpl.
  unfold lshift.
  bdestruct (x0 =? x). subst.
  apply lshift'_phi_modes. inv H. lia. lia.
  easy.
  unfold phi_modes in *.
  unfold phi_mode in *. intros.
  rewrite lshift'_irrelevant. apply H0; try lia. iner_p.
  simpl.
  unfold rshift.
  bdestruct (x0 =? x). subst.
  apply rshift'_phi_modes. inv H. lia. lia.
  easy.
  unfold phi_modes in *.
  unfold phi_mode in *. intros.
  rewrite rshift'_irrelevant. apply H0; try lia. iner_p.
  simpl.
  unfold reverse.
  unfold phi_modes in *.
  unfold phi_mode in *.
  intros.
  simpl.
  bdestruct (x0 =? x). 
  bdestruct (i <? aenv x). simpl.
  subst.
  apply H0. inv H. lia. lia.
  simpl. apply H0. lia. simpl. apply H0. lia.
  simpl.
  inv H.
  specialize (IHe1 aenv f x size H5 H0).
  specialize (IHe2 aenv (exp_sem aenv e1 f) x size H6 IHe1). easy.
Qed.

Lemma adder_sub_seq : forall size f x B A M aenv tenv,
                 phi_modes f x size -> exp_scope aenv x size (rz_adder x size (nat2fb A))
                 ->  well_typed_exp tenv (rz_adder x size (nat2fb A))
                -> well_typed_exp tenv (rz_sub x size (nat2fb M))
                   -> right_mode_env aenv tenv f -> 
                  1 < M < 2^size -> A < 2^size -> B < 2^size ->
                  fbrev size (get_r_qft f x) = nat2fb B ->
                  (get_r_qft (exp_sem aenv (rz_adder x size (nat2fb A); (rz_sub x size (nat2fb M))) f) x)
                    = (fbrev size (nat2fb (((B + A) + 2^size - M) mod 2^size))).
Proof.
  intros.
  specialize (rz_adder_full size f x B A aenv tenv H H1 H3 H5 H6 H7) as eq1.
  simpl.
  assert (fbrev size (get_r_qft (exp_sem aenv (rz_adder x size (nat2fb A)) f) x) 
               = (nat2fb ((B + A) mod 2 ^ size))).
  rewrite eq1. rewrite fbrev_twice_same. easy.
  rewrite rz_sub_full with (A:= ((B + A) mod 2 ^ size)) (tenv:=tenv); try easy.
  assert (2 ^ size - M = (2 ^ size - M) mod 2^size).
  rewrite Nat.mod_small by lia. easy.
  assert (((B + A) mod 2 ^ size + 2 ^ size - M) =
              ((B + A) mod 2 ^ size + (2 ^ size - M))) by lia.
  rewrite H10. rewrite H9.
  rewrite <- Nat.add_mod by lia.
  assert ((B + A + (2 ^ size - M)) = ((B + A + 2 ^ size - M))) by lia.
  rewrite H11. easy.
  apply phi_modes_exp. easy. easy.
  apply well_typed_right_mode_exp; try easy.
  apply Nat.mod_upper_bound. lia.
Qed.

Lemma qft_cu_sem : forall l tenv tenv' aenv f x c size, phi_modes f x (S size) -> aenv x = S size
          -> nor_mode f c -> fst c <> x ->
          well_typed_pexp aenv l tenv (RQFT x) l tenv' -> right_mode_env aenv tenv f ->
           qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
                  well_formed_ls l -> exp_neu_prop l ->
          prog_sem aenv (qft_cu x c) f = f[c |-> put_cu (f c) ((get_r_qft f x 0) ⊕ get_cua (f c))].
Proof.
  intros.
  unfold qft_cu.
  remember (RQFT x) as e.
  assert (QFT x = inv_pexp e). rewrite Heqe. simpl. easy.
  rewrite H9. simpl.
  rewrite cnot_sem.
  rewrite fresh_pexp_sem_out.
  assert ((prog_sem aenv (inv_pexp e) (prog_sem aenv e f))
          = prog_sem aenv (e ;; inv_pexp e) f). simpl. easy.
  rewrite H10.
  rewrite inv_pexp_correct_rev with (tenv := tenv) (tenv' := tenv') (l:= l) (l':=l); try easy.
  apply eupdate_same_1. easy.
  rewrite Heqe. simpl.
  unfold turn_rqft,turn_qft.
  rewrite assign_seq_out; try iner_p.
  rewrite assign_seq_lt; try lia.
  assert (get_cua (nval (get_r_qft f x 0) (get_r (f (x, 0)))) = (get_r_qft f x 0)).
  unfold get_cua. easy.
  rewrite H11. easy.
  rewrite Heqe. simpl. constructor.
  unfold or_not_eq. left. lia.
  rewrite Heqe. simpl.
  unfold turn_rqft.
  unfold nor_mode.
  rewrite assign_seq_lt; try lia.
  rewrite Heqe. simpl.
  unfold nor_mode,turn_rqft.
  rewrite assign_seq_out; easy. 
Qed.

Lemma qft_acu_sem : forall l tenv tenv' aenv f x c size, phi_modes f x (S size) -> aenv x = S size
          -> nor_mode f c -> fst c <> x ->
          well_typed_pexp aenv l tenv (RQFT x) l tenv' -> right_mode_env aenv tenv f ->
           qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
                  well_formed_ls l -> exp_neu_prop l ->
          prog_sem aenv (qft_acu x c) f = f[c |-> put_cu (f c) ((¬ (get_r_qft f x 0)) ⊕ get_cua (f c))].
Proof.
  intros.
  unfold qft_acu.
  remember (RQFT x) as e.
  assert (QFT x = inv_pexp e). rewrite Heqe. simpl. easy.
  rewrite H9. simpl.
  rewrite cnot_sem.
  destruct c.
  rewrite eupdate_index_eq.
  rewrite eupdate_twice_neq by iner_p.
  rewrite eupdate_twice_eq.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by iner_p.
  assert (((prog_sem aenv e f) [(x, 0)
    |-> exchange (exchange (prog_sem aenv e f (x, 0)))]) = (prog_sem aenv e f)).
  rewrite eupdate_same. easy.
  unfold exchange.
  destruct (prog_sem aenv e f (x, 0)) eqn:eq1.
  assert ((¬ (¬ b)) = b) by btauto. rewrite H10. 1-3:easy.
  rewrite H10.
  rewrite fresh_pexp_sem_out.
  assert ((prog_sem aenv (inv_pexp e) (prog_sem aenv e f))
          = prog_sem aenv (e ;; inv_pexp e) f). simpl. easy.
  rewrite H11.
  rewrite inv_pexp_correct_rev with (tenv := tenv) (tenv' := tenv') (l:=l) (l':=l); try easy.
  apply eupdate_same_1. easy.
  rewrite Heqe. simpl.
  unfold turn_rqft,turn_qft.
  rewrite assign_seq_out; try iner_p.
  rewrite assign_seq_lt; try lia.
  unfold exchange. unfold get_cua. easy.
  rewrite Heqe. simpl. constructor.
  unfold or_not_eq. left. lia.
  unfold nor_mode. rewrite eupdate_index_eq.
  rewrite Heqe. simpl.
  unfold turn_rqft.
  rewrite assign_seq_lt; try lia. unfold exchange. lia.
  rewrite Heqe.
  simpl.
  unfold nor_mode,turn_rqft.
  rewrite eupdate_index_neq.
  rewrite assign_seq_out; easy. destruct c. iner_p. 
Qed.

Lemma get_r_qft_out : forall x c v f, fst c <> x -> get_r_qft (f[c |-> v]) x = get_r_qft f x.
Proof.
  intros. unfold get_r_qft.
  destruct c.
  rewrite eupdate_index_neq by iner_p. easy.
Qed.

Lemma env_eq_well_typed : forall e tenv tenv', Env.Equal tenv tenv' 
                 -> well_typed_exp tenv e -> well_typed_exp tenv' e.
Proof.
 intros.
 induction H0. constructor.
 constructor.
 eapply mapsto_equal. apply H0. easy.
 apply x_had.
 eapply mapsto_equal. apply H0. easy.
 constructor.
 eapply mapsto_equal. apply H0. easy.
 apply IHwell_typed_exp. easy.
 constructor.
 eapply mapsto_equal. apply H0. easy.
 eapply mapsto_equal. apply H1. easy.
 constructor.
 eapply mapsto_equal. apply H0. easy.
 apply rz_had.
 eapply mapsto_equal. apply H0. easy.
 constructor.
 eapply mapsto_equal. apply H0. easy.
 apply rrz_had.
 eapply mapsto_equal. apply H0. easy.
 apply sr_had with (n:=n).
 eapply mapsto_equal. apply H0. easy. easy.
 apply srr_had with (n:=n).
 eapply mapsto_equal. apply H0. easy. easy.
 constructor.
 eapply mapsto_equal. apply H0. easy.
 apply lshift_had.
 eapply mapsto_equal. apply H0. easy.
 constructor.
 eapply mapsto_equal. apply H0. easy.
 apply rshift_had.
 eapply mapsto_equal. apply H0. easy.
 constructor.
 eapply mapsto_equal. apply H0. easy.
 apply rev_had.
 eapply mapsto_equal. apply H0. easy.
 constructor.
 apply IHwell_typed_exp1; easy.
 apply IHwell_typed_exp2; easy.
Qed.

Lemma env_eq_right_mode : forall tenv tenv' aenv f, Env.Equal tenv tenv'
          -> right_mode_env aenv tenv f -> right_mode_env aenv tenv' f.
Proof.
  intros.
  unfold right_mode_env in *. intros.
  specialize (H0 t p H1).
  apply mapsto_equal with (s2 := tenv) in H2. apply H0. easy.
  apply EnvFacts.Equal_sym. easy.
Qed.

Lemma exp_neu_rz_adder' : forall n l x size A, exp_neu l (rz_adder' x n size A) l.
Proof.
  induction n; intros; try easy.
  constructor. 
  simpl. econstructor.
  apply IHn.
  destruct (A n). constructor. constructor.
Qed.

Lemma exp_neu_rz_sub' : forall n l x size A, exp_neu l (rz_sub' x n size A) l.
Proof.
  induction n; intros; try easy.
  constructor. 
  simpl. econstructor.
  apply IHn.
  destruct (A n). constructor. constructor.
Qed.

Lemma exp_neu_rz_adder_sub : forall l x size A M,
           exp_neu l (rz_adder x size A; rz_sub x size M) l.
Proof.
  intros. econstructor.
  apply exp_neu_rz_adder'.
  apply exp_neu_rz_sub'.
Qed.

Lemma exp_neu_same : forall e l l1 l2, exp_neu l e l1 -> exp_neu l e l2 -> l1 = l2.
Proof.
  induction e; intros; simpl.
  1-2:inv H; inv H0; easy.
  inv H. inv H0. easy.
  1-5:inv H; inv H0; easy.
  inv H. inv H0. easy.
  rewrite H1 in H3. contradiction.
  inv H0. rewrite H2 in H3. contradiction.
  easy.
  inv H. inv H0. easy.
  rewrite H1 in H3. contradiction.
  inv H0. rewrite H2 in H3. contradiction.
  easy. inv H. inv H0.
  easy.
  rewrite H1 in H3. contradiction.
  inv H0. rewrite H2 in H3. contradiction.
  easy.
  inv H. inv H0.
  specialize (IHe1 l l' l'0 H4 H3). subst.
  apply IHe2 with (l := l'0). easy. easy.
Qed.

Lemma mod_adder_half_sem : forall size f x c A B M aenv l l' tenv tenv',
         phi_modes f x (S size) -> aenv x = S size -> nor_mode f c -> fst c <> x ->
         get_cua (f c) = false ->
           exp_scope aenv x (S size) (rz_adder x (S size) (nat2fb A); rz_sub x (S size) (nat2fb M))
        -> well_typed_pexp aenv l tenv (mod_adder_half x (S size) c (nat2fb A) (nat2fb M)) l' tenv'
        -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f
        -> 1 < M < 2^size -> A < M -> B < M ->
        fbrev (S size) (get_r_qft f x) = nat2fb B ->
                  well_formed_ls l -> exp_neu_prop l ->
      (get_r_qft (prog_sem aenv (mod_adder_half x (S size) c (nat2fb A) (nat2fb M)) f) x)
           = (fbrev (S size) (nat2fb (((B + A) mod M)))).
Proof.
  intros.
  unfold mod_adder_half.
  remember ((rz_adder x (S size) (nat2fb A); rz_sub x (S size) (nat2fb M))) as e1.
  Local Opaque qft_cu one_cu_adder.
  simpl.
  Local Transparent qft_cu one_cu_adder.
  remember ((exp_sem aenv e1 f)) as g.
  assert (get_r_qft g x = 
       fbrev (S size) (nat2fb ((B + A + 2 ^ S size - M) mod 2 ^ S size))).
  subst.
  inv H5. inv H19. inv H18. inv H20. inv H22. inv H4. inv H15. inv H16.
  rewrite adder_sub_seq with (B := B) (tenv:=env'0) ; try easy.
  1-3:simpl;lia.
  inv H5. inv H20. inv H24. inv H20. inv H26.
  remember (rz_adder x (S size) (nat2fb A);
            rz_sub x (S size) (nat2fb M)) as e1.
  rewrite qft_cu_sem with (tenv := env'0) (tenv' := env'1) (size := size) (l:=l'1); try easy.
  rewrite efresh_exp_sem_irrelevant.
  rewrite H3. bt_simpl. rewrite H15.
  rewrite highbit_means_lt with (X := B + A) (M := M) ; try (simpl;lia).
  unfold one_cu_adder.
  Local Opaque rz_adder. 
  simpl.
  Local Transparent rz_adder.
  rewrite eupdate_index_eq.
  rewrite get_put_cu ; try easy.
  bdestruct (B + A <? M).
  rewrite efresh_exp_sem_out; try (apply efresh_rz_adder; try easy).
  rewrite get_r_qft_out; try easy.
  inv H23. inv H28.
  rewrite rz_adder_full with (A:= ((B + A + 2 ^ S size - M) mod 2 ^ S size)) (tenv:= tenv'); try easy.
  assert (2^S size <> 0).
  apply Nat.pow_nonzero; lia.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_mod by lia.
  rewrite <- Nat.add_mod by lia.
  assert (M < 2^S size) by (simpl;lia).
  assert (B + A + 2 ^ S size - M + M = B + A + 2^S size) by lia.
  rewrite H26.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small by lia.
  rewrite Nat.mod_small by lia. easy.
  apply phi_modes_exp; try easy.
  inv H19. inv H21. inv H25.
  assert (Env.Equal env'0 tenv').
  apply EnvFacts.Equal_trans with (m' := (Env.add x (Phi (aenv x)) env'1)).
  apply EnvFacts.Equal_trans with (m' := (Env.add x (Phi (aenv x)) ((Env.add x Nor env'0)))).
  unfold Env.Equal. intros.
  bdestruct (x =? y). subst.
  rewrite find_add.
  apply Env.find_1 in H19. easy.
  repeat rewrite EnvFacts.add_neq_o by lia.
  easy.
  unfold Env.Equal. intros.
  bdestruct (x =? y). subst.
  rewrite find_add.
  rewrite find_add. easy.
  rewrite EnvFacts.add_neq_o by lia.
  apply EnvFacts.Equal_sym in H33.
  unfold Env.Equal in H33.
  rewrite EnvFacts.add_neq_o with (m := env'1) by lia. easy.
  apply EnvFacts.Equal_sym. easy.
  apply well_typed_right_mode_exp; try easy.
  apply env_eq_well_typed with (tenv := env'0). easy.
  easy.
  apply env_eq_right_mode with (tenv := env'0). easy. easy.
  simpl. lia.
  apply Nat.mod_upper_bound.
  apply Nat.pow_nonzero ; lia.
  rewrite H15.
  rewrite fbrev_twice_same. easy.
  rewrite get_r_qft_out by easy.
  rewrite H15.
  assert ((B + A + 2 ^ S size - M) = (B + A - M) + 2^S size) by lia.
  rewrite H18.
  assert (2^S size <> 0).
  apply Nat.pow_nonzero; lia.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  assert (B + A < 2 ^ S size). simpl. lia.
  rewrite Nat.mod_small by lia.
  assert (B+A < 2*M) by lia.
  rewrite Nat.mod_eq by lia.
  assert (1 <= (B + A) / M < 2).
    { split.
      apply Nat.div_le_lower_bound; lia.
      apply Nat.div_lt_upper_bound; lia.
    }
  replace (M * ((B + A) / M)) with M by nia.
  easy.
  subst. constructor. apply efresh_rz_adder; easy.
  apply efresh_rz_sub; easy.
  apply phi_modes_exp. subst. easy. easy.
  unfold nor_mode.
  rewrite efresh_exp_sem_irrelevant. apply H1.
  subst. constructor. apply efresh_rz_adder; easy.
  apply efresh_rz_sub; easy. inv H21. constructor; try easy.
  apply well_typed_right_mode_exp; try easy.
  inv H19. easy. inv H19. easy.
  inv H19.
  apply qft_uniform_exp_trans; try easy.
  inv H19. apply qft_gt_exp_trans; try easy.
  subst. inv H19.
  specialize (exp_neu_rz_adder_sub l x (S size) (nat2fb A) (nat2fb M)) as eq5.
  apply exp_neu_same with (l1 := l'1)  in eq5. subst. easy. easy.
  inv H19.
  specialize (exp_neu_rz_adder_sub l x (S size) (nat2fb A) (nat2fb M)) as eq5.
  apply exp_neu_same with (l1 := l'1)  in eq5. subst. easy. easy.
Qed.

Lemma clean_hbit_sem: forall size f x c B A aenv l tenv tenv', 
         phi_modes f x (S size) -> aenv x = S size -> nor_mode f c -> fst c <> x ->
         well_typed_pexp aenv l tenv (Exp (rz_sub x (S size) (nat2fb A))) l tenv -> right_mode_env aenv tenv f ->
         A < 2^ size -> B < 2^size -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
         fbrev (S size) (get_r_qft f x) = nat2fb B -> well_typed_pexp aenv l tenv (RQFT x) l tenv' ->
                  well_formed_ls l -> exp_neu_prop l ->
        prog_sem aenv (clean_hbit x (S size) c (nat2fb A)) f =
                f[c |-> put_cu (f c) ((¬ (fbrev (S size)
                           (nat2fb ((B + 2^S size - A) mod 2^S size)) 0)) ⊕ get_cua (f c))].
Proof.
  intros.
  Local Opaque rz_sub qft_acu. simpl.
  Local Transparent rz_sub qft_acu.
  assert (A < 2^ S size) by (simpl;lia).
  assert (B < 2^ S size) by (simpl;lia). inv H3.
  specialize (rz_sub_full (S size) f x B A aenv tenv H H20 H4 H13 H14 H9) as eq1.
  rewrite qft_acu_sem with (tenv := tenv) (tenv' := tenv') (size := size) (l:=l); try easy.
  rewrite efresh_exp_sem_out.
  assert ((exp_sem aenv (inv_exp (rz_sub x (S size) (nat2fb A)))
   (exp_sem aenv (rz_sub x (S size) (nat2fb A)) f))
   = exp_sem aenv (rz_sub x (S size) (nat2fb A) ; inv_exp (rz_sub x (S size) (nat2fb A))) f).
  easy.
  rewrite H3. clear H3.
  rewrite inv_exp_correct_rev with (tenv := tenv); try easy.
  apply eupdate_same_1. easy.
  rewrite eq1.
  rewrite efresh_exp_sem_irrelevant. simpl. easy.
  apply efresh_rz_sub; try lia.
  apply fresh_inv_exp.
  apply efresh_rz_sub; try lia.
  apply phi_modes_exp.
  apply escope_rz_sub. easy.
  unfold nor_mode.
  rewrite efresh_exp_sem_irrelevant. easy.
  apply efresh_rz_sub; try lia.
  apply well_typed_right_mode_exp; try easy.
  apply qft_uniform_exp_trans; try easy.
  apply qft_gt_exp_trans; try easy.
Qed.

Lemma put_cu_get_r : forall c f b, nor_mode f c -> put_cu (f c) b = nval b (get_r (f c)).
Proof.
  intros.
  unfold put_cu, get_r.
  unfold nor_mode in H.
  destruct (f c). easy. lia. lia.
Qed.

Lemma qft_cu_r_same : forall aenv x c f, nor_mode f c -> fst c <> x -> 0 < aenv x ->
             get_r ((prog_sem aenv (qft_cu x c) f) c) = get_r (f c).
Proof.
  intros. simpl.
  unfold turn_qft.
  rewrite assign_r_out by easy.
  rewrite cnot_sem.
  rewrite eupdate_index_eq.
  unfold get_r,put_cu.
  unfold turn_rqft.
  rewrite assign_seq_out by easy.
  destruct (f c) eqn:eq1. easy. easy. easy.
  unfold nor_mode, turn_rqft.
  rewrite assign_seq_lt; lia.
  unfold nor_mode.
  unfold turn_rqft.
  rewrite assign_seq_out by easy. apply H.
Qed.

Lemma one_cu_adder_r_same : forall aenv x n c M f, fst c <> x ->
             get_r ((exp_sem aenv (one_cu_adder x n c M) f) c) = get_r (f c).
Proof.
  intros. simpl.
  destruct (get_cua (f c)).
  rewrite efresh_exp_sem_irrelevant. easy.
  apply efresh_rz_adder. easy. lia. easy.
Qed.

Lemma nor_mode_one_cu_adder : forall x n c M aenv f p, nor_mode f p -> fst p <> x ->
                nor_mode (exp_sem aenv (one_cu_adder x n c M) f) p.
Proof.
  intros.
  unfold nor_mode in *.
  Local Opaque rz_adder. simpl. Local Transparent rz_adder.
  destruct (get_cua (f c)).
  rewrite efresh_exp_sem_irrelevant. apply H.
  apply efresh_rz_adder. easy. lia. easy.
Qed.

Lemma nor_mode_qft_cu : forall x aenv f p, nor_mode f p -> fst p <> x -> 0 < aenv x ->
                nor_mode (prog_sem aenv (qft_cu x p) f) p.
Proof.
  intros.
  unfold nor_mode in *.
  simpl.
  unfold turn_qft.
  rewrite assign_r_out.
  rewrite cnot_sem. 
  rewrite eupdate_index_eq.
  unfold turn_rqft.
  rewrite assign_seq_out by easy.
  unfold put_cu.
  destruct (f p). 1-3:lia.
  unfold nor_mode, turn_rqft.
  rewrite assign_seq_lt ; try easy.
  unfold nor_mode, turn_rqft.
  rewrite assign_seq_out; try easy. easy.
Qed.

Lemma nor_mode_qft_acu : forall x aenv f p, nor_mode f p -> fst p <> x -> 0 < aenv x ->
                nor_mode (prog_sem aenv (qft_acu x p) f) p.
Proof.
  intros.
  unfold nor_mode in *.
  simpl.
  unfold turn_qft.
  rewrite assign_r_out.
  rewrite cnot_sem. 
  destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by iner_p.
  unfold turn_rqft.
  rewrite assign_seq_out by easy.
  rewrite put_cu_get_r. lia. easy.
  unfold nor_mode.
  rewrite eupdate_index_eq.
  unfold turn_rqft.
  rewrite assign_seq_lt; try easy.
  unfold nor_mode.
  destruct p.
  rewrite eupdate_index_neq by iner_p.
  unfold turn_rqft.
  rewrite assign_seq_out by easy. easy. easy.
Qed.


Lemma nor_mode_mod_adder : forall x n c aenv f A M, phi_modes f x n -> 
          nor_mode f c -> fst c <> x -> 0 < aenv x -> nor_mode (prog_sem aenv (mod_adder x n c A M) f) c.
Proof.
  intros.
  unfold mod_adder,mod_adder_half,clean_hbit.
  remember (rz_adder x n A; rz_sub x n M) as e1.
  Local Opaque qft_cu one_cu_adder rz_sub qft_acu rz_sub.
  simpl.
  Local Transparent qft_cu one_cu_adder rz_sub qft_acu rz_sub.
  unfold nor_mode.
  rewrite efresh_exp_sem_irrelevant.
  apply nor_mode_qft_acu; try easy.
  unfold nor_mode.
  rewrite efresh_exp_sem_irrelevant.
  apply nor_mode_one_cu_adder; try easy.
  apply nor_mode_qft_cu; try easy.
  subst.
  unfold nor_mode.
  rewrite efresh_exp_sem_irrelevant. easy.
  constructor.
  apply efresh_rz_adder; try easy.
  apply efresh_rz_sub; try easy.
  apply efresh_rz_sub; try easy.
  apply fresh_inv_exp.
  apply efresh_rz_sub; try easy.  
Qed.


Lemma phi_modes_qft_cu : forall x n c aenv f, phi_modes f x n -> 
          nor_mode f c -> fst c <> x -> 0 < aenv x -> phi_modes (prog_sem aenv (qft_cu x c) f) x n.
Proof. 
  intros.
  unfold phi_modes in *.
  intros. simpl.
  unfold turn_qft.
  unfold phi_mode in *.
  bdestruct (i <? aenv x).
  rewrite assign_r_lt by try lia.
  unfold up_qft.
  rewrite cnot_sem.
  destruct c.
  rewrite eupdate_index_neq by iner_p.
  unfold turn_rqft.
  rewrite assign_seq_lt ; easy.
  unfold nor_mode.
  unfold turn_rqft.
  rewrite assign_seq_lt. lia. lia.
  unfold nor_mode,turn_rqft.
  rewrite assign_seq_out. apply H0. easy.
  rewrite assign_r_ge.
  rewrite cnot_sem.
  destruct c.
  rewrite eupdate_index_neq by iner_p.
  unfold turn_rqft.
  rewrite assign_seq_ge by lia. apply H. easy.
  unfold nor_mode.
  unfold turn_rqft.
  rewrite assign_seq_lt. lia. lia.
  unfold nor_mode,turn_rqft.
  rewrite assign_seq_out. apply H0. easy. lia.
Qed.

Lemma phi_modes_qft_acu : forall x n c aenv f, phi_modes f x n -> 
          nor_mode f c -> fst c <> x -> 0 < aenv x -> phi_modes (prog_sem aenv (qft_acu x c) f) x n.
Proof. 
  intros.
  unfold phi_modes in *.
  intros. simpl.
  unfold turn_qft.
  unfold phi_mode in *.
  bdestruct (i <? aenv x).
  rewrite assign_r_lt by try lia.
  unfold up_qft.
  rewrite cnot_sem.
  bdestruct (i =? 0). subst.
  rewrite eupdate_index_eq.
  destruct c.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_eq.
  unfold turn_rqft.
  rewrite assign_seq_lt by lia.
  unfold exchange. lia.
  rewrite eupdate_index_neq by iner_p.
  destruct c.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_neq by iner_p.
  unfold turn_rqft.
  rewrite assign_seq_lt ; easy.
  unfold nor_mode.
  rewrite eupdate_index_eq.
  unfold turn_rqft.
  rewrite assign_seq_lt ; easy.
  unfold nor_mode.
  destruct c.
  rewrite eupdate_index_neq by iner_p.
  unfold turn_rqft.
  rewrite assign_seq_out ; easy.
  rewrite assign_r_ge by lia.
  rewrite cnot_sem.
  rewrite eupdate_index_neq by iner_p.
  destruct c.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_neq by iner_p.
  unfold turn_rqft.
  rewrite assign_seq_ge by lia. apply H. lia.
  unfold nor_mode.
  unfold turn_rqft.
  rewrite eupdate_index_eq.
  rewrite assign_seq_lt by lia.
  unfold exchange. lia.
  unfold nor_mode.
  unfold turn_rqft.
  destruct c.
  rewrite eupdate_index_neq by iner_p.
  rewrite assign_seq_out by lia.
  apply H0.
Qed.

Lemma exp_scope_inv_exp : forall e aenv x n, exp_scope aenv x n e -> exp_scope aenv x n (inv_exp e).
Proof.
  intros. induction H; simpl; try (constructor;easy).
Qed.

Lemma phi_modes_mod_adder : forall x n c aenv f A M, phi_modes f x n -> 
          nor_mode f c -> fst c <> x -> 0 < aenv x -> phi_modes (prog_sem aenv (mod_adder x n c A M) f) x n.
Proof.
  intros.
  unfold mod_adder,mod_adder_half,clean_hbit.
  remember (rz_adder x n A; rz_sub x n M) as e1.
  Local Opaque qft_cu one_cu_adder rz_sub qft_acu rz_sub.
  simpl.
  Local Transparent qft_cu one_cu_adder rz_sub qft_acu rz_sub.
  apply phi_modes_exp.
  apply exp_scope_inv_exp. apply escope_rz_sub.
  apply phi_modes_qft_acu; try easy.
  apply phi_modes_exp. apply escope_rz_sub.
  apply phi_modes_exp. constructor. apply escope_rz_adder.
  apply phi_modes_qft_cu; try easy.
  apply phi_modes_exp. subst. constructor.
  apply escope_rz_adder. apply escope_rz_sub.
  easy. subst.
  unfold nor_mode.
  rewrite efresh_exp_sem_irrelevant. easy.
  constructor.
  apply efresh_rz_adder; try easy.
  apply efresh_rz_sub; try easy.
  unfold nor_mode.
  rewrite efresh_exp_sem_irrelevant.
  apply nor_mode_one_cu_adder; try easy.
  apply nor_mode_qft_cu.
  unfold nor_mode.
  rewrite efresh_exp_sem_irrelevant. easy.
  subst. constructor.
  apply efresh_rz_adder; try easy.
  apply efresh_rz_sub; try easy.
  easy. easy.
  apply efresh_rz_sub; try easy.
Qed.


Lemma exp_neu_qft_cu : forall l x c, pexp_neu l (qft_cu x c) l.
Proof.
  intros.
  unfold qft_cu. econstructor. econstructor. constructor.
  constructor.
  Local Transparent CNOT.
  constructor.
  Local Opaque CNOT.
  constructor. constructor.
Qed.

Lemma exp_neu_qft_acu : forall l x c, pexp_neu l (qft_acu x c) l.
Proof.
  intros.
  unfold qft_cu. econstructor. econstructor. constructor.
  constructor. econstructor. econstructor. constructor.
  Local Transparent CNOT.
  constructor.
  Local Opaque CNOT.
  constructor. constructor. constructor.
Qed.

Lemma exp_neu_mod_adder_half : forall l x c size A M,
           pexp_neu l (mod_adder_half x size c A M) l.
Proof.
  intros. econstructor. econstructor.
  constructor. apply exp_neu_rz_adder_sub.
  apply exp_neu_qft_cu.
  unfold one_cu_adder. constructor.
  constructor.
  apply exp_neu_rz_adder'.
Qed.

Lemma exp_neu_clean_hbit : forall l x c size M, well_formed_ls l
           -> exp_neu_prop l -> pexp_neu l (clean_hbit x size c M) l.
Proof.
  intros. econstructor. econstructor.
  constructor.
  eapply exp_neu_rz_sub'.
  apply exp_neu_qft_acu.
  constructor.
  apply neu_inv_exp; try easy.
  apply exp_neu_rz_sub'.
Qed.

Lemma exp_neu_cnot : forall l x y, exp_neu l (CNOT x y) l.
Proof.
  intros.
  Local Transparent CNOT.
  constructor. constructor.
  Local Opaque CNOT.
Qed.

Lemma mod_adder_sem : forall size f x c A B M aenv l l' tenv tenv',
         phi_modes f x (S size) -> aenv x = S size -> nor_mode f c -> fst c <> x ->
         get_cua (f c) = false
        -> well_typed_pexp aenv l tenv (mod_adder x (S size) c (nat2fb A) (nat2fb M)) l' tenv'
        -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f
        -> 1 < M < 2^size -> A < M -> B < M ->
        fbrev (S size) (get_r_qft f x) = nat2fb B ->
                  well_formed_ls l -> exp_neu_prop l ->
      (get_r_qft (prog_sem aenv (mod_adder x (S size) c (nat2fb A) (nat2fb M)) f) x)
           = (fbrev (S size) (nat2fb (((B + A) mod M)))).
Proof.
  intros.
  Local Opaque mod_adder_half clean_hbit. simpl.
  inv H4.
  Local Transparent mod_adder_half clean_hbit.
  assert (exp_scope aenv x (S size)
        (rz_adder x (S size) (nat2fb A); rz_sub x (S size) (nat2fb M))).
  constructor. apply escope_rz_adder. apply escope_rz_sub.
  Check mod_adder_half_sem.
  specialize (mod_adder_half_sem size f x c A B M aenv l l'0 tenv env'
                 H H0 H1 H2 H3 H4 H18 H5 H6 H7 H8 H9 H10 H11 H12 H13) as eq1.
  unfold clean_hbit in H21. inv H21. inv H19. inv H20. unfold qft_acu in H24. inv H24. inv H22.
  Check clean_hbit_sem.
  rewrite clean_hbit_sem with (tenv := env'1)
        (tenv' := env'2) (B:=((B + A) mod M)) (l := l'2); try easy.
  rewrite get_r_qft_out by easy.
  rewrite eq1. easy.
  unfold mod_adder_half.
  remember (rz_adder x (S size) (nat2fb A); rz_sub x (S size) (nat2fb M)) as e1.
  Local Opaque qft_cu one_cu_adder.
  simpl.
  Local Transparent qft_cu one_cu_adder.
  apply phi_modes_exp.
  unfold one_cu_adder. constructor.
  apply escope_rz_adder.
  apply phi_modes_qft_cu ; try easy.
  apply phi_modes_exp. subst.
  constructor. apply escope_rz_adder.
  apply escope_rz_sub. easy.
  unfold nor_mode.
  rewrite efresh_exp_sem_irrelevant. apply H1.
  subst. constructor.
  apply efresh_rz_adder. easy. lia.
  apply efresh_rz_sub. easy. lia. lia.
  unfold nor_mode.
  unfold mod_adder_half.
  remember (rz_adder x (S size) (nat2fb A); rz_sub x (S size) (nat2fb M)) as e1.
  unfold one_cu_adder.
  Local Opaque qft_cu rz_adder.
  simpl.
  Local Transparent qft_cu rz_adder.
  destruct (get_cua (prog_sem aenv (qft_cu x c) (exp_sem aenv e1 f) c)).
  rewrite efresh_exp_sem_irrelevant.
  unfold qft_cu. simpl.
  unfold turn_qft.
  rewrite assign_r_out by iner_p.
  rewrite cnot_sem.
  rewrite eupdate_index_eq.
  unfold turn_rqft.
  rewrite assign_seq_out by easy.
  rewrite Heqe1.
  rewrite efresh_exp_sem_irrelevant.
  unfold nor_mode in H1. destruct (f c).
  unfold put_cu. 1-3:lia.
  constructor.
  apply efresh_rz_adder. easy. lia.
  apply efresh_rz_sub. easy. lia.
  unfold nor_mode.
  unfold turn_rqft. rewrite assign_seq_lt by lia. easy.
  unfold nor_mode.
  unfold turn_rqft. rewrite assign_seq_out by lia.
  rewrite efresh_exp_sem_irrelevant. apply H1.
  subst. constructor.
  apply efresh_rz_adder. easy. lia.
  apply efresh_rz_sub. easy. lia.
  apply efresh_rz_adder. easy. lia.
  unfold qft_cu. simpl.
  unfold turn_qft.
  rewrite assign_r_out by easy.
  rewrite cnot_sem.
  rewrite eupdate_index_eq.
  unfold turn_rqft. rewrite assign_seq_out by easy.
  rewrite efresh_exp_sem_irrelevant.
  unfold nor_mode in H1. unfold put_cu.
  destruct (f c). 1-3:lia.
  subst. constructor.
  apply efresh_rz_adder. easy. lia.
  apply efresh_rz_sub. easy. lia.
  unfold nor_mode.
  unfold turn_rqft.
  rewrite assign_seq_lt; lia.
  unfold nor_mode.
  unfold turn_rqft.
  rewrite assign_seq_out by easy.
  rewrite efresh_exp_sem_irrelevant. apply H1.
  subst. constructor.
  apply efresh_rz_adder. easy. lia.
  apply efresh_rz_sub. easy. lia.
  constructor. easy.
  apply exp_neu_rz_sub'. easy. 
  apply well_typed_right_mode_pexp with (tenv := tenv) (l := l) (l' := l'0); try easy.
  lia.
  assert ((B + A) mod M < M). 
  apply Nat.mod_upper_bound. lia. lia.
  apply qft_uniform_pexp_trans with (tenv := tenv) (l := l) (l' := l'0); try easy.
  apply qft_gt_pexp_trans with (tenv := tenv) (l := l) (l' := l'0); try easy.
  rewrite eq1.
  rewrite fbrev_twice_same. easy.
  inv H24. constructor; try easy.
  eapply exp_neu_well_formed_ls. apply H16.
  eapply typed_pexp_well_formed_ls.
  apply H18. easy.
  eapply exp_neu_t_prop. apply H16.
  eapply typed_pexp_well_formed_ls.
  apply H18. easy.
  eapply typed_pexp_neu_prop.
  apply H18. easy. easy.
Qed.


Lemma mod_adder_half_high : forall size f x c A B M aenv l l' tenv tenv',
         phi_modes f x (S size) -> aenv x = S size -> nor_mode f c -> fst c <> x ->
         get_cua (f c) = false ->
           exp_scope aenv x (S size) (rz_adder x (S size) (nat2fb A); rz_sub x (S size) (nat2fb M))
        -> well_typed_pexp aenv l tenv (mod_adder_half x (S size) c (nat2fb A) (nat2fb M)) l' tenv'
        -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f
        -> 1 < M < 2^size -> A < M -> B < M ->
        fbrev (S size) (get_r_qft f x) = nat2fb B ->
                  well_formed_ls l -> exp_neu_prop l ->
      get_cua ((prog_sem aenv (mod_adder_half x (S size) c (nat2fb A) (nat2fb M)) f) c) = (B + A <? M).
Proof.
  intros.
  unfold mod_adder_half,qft_cu.
  unfold qft_cu.
  assert (prog_sem aenv
     (((rz_adder x (S size) (nat2fb A); rz_sub x (S size) (nat2fb M));;
       ((RQFT x;; CNOT (x, 0) c);; QFT x));;
      one_cu_adder x (S size) c (nat2fb M)) f
      = (prog_sem aenv
        (Exp (rz_adder x (S size) (nat2fb A));; rz_compare_half x (S size) c M ;;
          QFT x ;; one_cu_adder x (S size) c (nat2fb M)) f)).
  simpl. easy.
  rewrite H15.
  Local Opaque rz_compare_half rz_adder.
  simpl.
  Local Transparent rz_compare_half rz_adder.
  inv H5. inv H20. inv H19. inv H21. inv H23. inv H26.
  assert (A < 2 ^ S size) by (simpl;lia).
  assert (B < 2 ^ S size) by (simpl;lia).
  Check rz_adder_full.
  specialize (rz_adder_full (S size) f x B A aenv env'0 H H20 H6 H5 H21 H12) as eq1.
  unfold turn_qft.
  rewrite assign_r_out by easy.
  assert (get_cua
       (prog_sem aenv (rz_compare_half x (S size) c M)
          (exp_sem aenv (rz_adder x (S size) (nat2fb A)) f) c) = (B + A <? M)).
  Check rz_compare_half_sem.
  inv H24. inv H30.
  rewrite rz_compare_half_sem with (A:=(B + A))
          (tenv := env'0) (tenv' := env'1) (l := l'1) (l' := l'3); try easy.
  apply phi_modes_exp. apply escope_rz_adder. easy.
  unfold nor_mode.
  rewrite efresh_exp_sem_irrelevant. apply H1.
  apply efresh_rz_adder. easy. lia.
  rewrite efresh_exp_sem_irrelevant. easy.
  apply efresh_rz_adder. easy. lia.
  inv H16. inv H17.
  unfold rz_compare_half. econstructor.
  econstructor. constructor. easy.
  apply exp_neu_rz_sub'.
  easy. apply H29. constructor.
  inv H34. easy. apply exp_neu_cnot. inv H34. easy.
  apply well_typed_right_mode_exp; try easy.
  simpl. lia. lia.
  rewrite eq1.
  rewrite fbrev_twice_same.
  rewrite Nat.mod_small by (simpl;lia). easy.
  rewrite H23.
  bdestruct (B + A <? M).
  rewrite efresh_exp_sem_irrelevant.
  rewrite assign_r_out by easy.
  rewrite H23. easy.
  apply efresh_rz_adder. easy. lia.
  rewrite assign_r_out by easy.
  rewrite H23. easy.
Qed.


Lemma mod_adder_typed : forall size f x c A B M aenv l l' tenv tenv',
         phi_modes f x (S size) -> aenv x = S size -> nor_mode f c -> fst c <> x ->
         get_cua (f c) = false
        -> well_typed_pexp aenv l tenv (mod_adder x (S size) c (nat2fb A) (nat2fb M)) l' tenv'
        -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f
        -> 1 < M < 2^size -> A < M -> B < M ->
        fbrev (S size) (get_r_qft f x) = nat2fb B ->
                  well_formed_ls l -> exp_neu_prop l ->
            (prog_sem aenv (mod_adder x (S size) c (nat2fb A) (nat2fb M)) f) c = f c.
Proof.
  intros.
  Local Opaque mod_adder_half clean_hbit. simpl.
  inv H4.
  Local Transparent mod_adder_half clean_hbit.
  inv H21. inv H17. inv H23. inv H17. inv H19.
  rewrite clean_hbit_sem with (B:= (((B + A) mod M)))
         (tenv:= env'1) (tenv':= env'3) (l := l'0); try easy.
  rewrite eupdate_index_eq.
  rewrite mod_adder_half_high with (B:=B) (tenv:=tenv) 
          (tenv' := env'1) (l := l) (l' := l'0); try easy.
  assert (forall b, put_cu (prog_sem aenv 
           (mod_adder_half x (S size) c (nat2fb A) (nat2fb M)) f c) b = put_cu (f c) b).
  intros. unfold mod_adder_half in *.
  remember ((rz_adder x (S size) (nat2fb A); rz_sub x (S size) (nat2fb M))) as e1.
  Local Opaque one_cu_adder qft_cu. simpl. Local Transparent one_cu_adder qft_cu.
  rewrite put_cu_get_r.
  rewrite one_cu_adder_r_same by easy.
  rewrite qft_cu_r_same ; try easy.
  rewrite efresh_exp_sem_irrelevant.
  unfold nor_mode in H1.
  destruct (f c). unfold get_r.
  unfold get_cua in H3. subst.
  unfold put_cu. easy. lia. lia.
  subst. constructor.
  apply efresh_rz_adder. easy. lia.
  apply efresh_rz_sub. easy. lia.
  unfold nor_mode.
  rewrite efresh_exp_sem_irrelevant. apply H1.
  subst. constructor.
  apply efresh_rz_adder. easy. lia.
  apply efresh_rz_sub. easy. lia. lia.
  Local Opaque one_cu_adder qft_cu. simpl. Local Transparent one_cu_adder qft_cu.
  apply nor_mode_one_cu_adder; try easy.
  apply nor_mode_qft_cu; try lia.
  unfold nor_mode. subst.
  rewrite efresh_exp_sem_irrelevant. apply H1.
  constructor.
  apply efresh_rz_adder. easy. lia.
  apply efresh_rz_sub. easy. lia.
  rewrite H4.
  bdestruct (B + A <? M).
  rewrite (Nat.mod_small (B+A)) by lia.
  assert ((B + A + 2 ^ S size - A) = B + 2^S size) by lia.
  rewrite H17.
  rewrite Nat.add_mod by (simpl;lia).
  rewrite Nat.mod_same by (simpl;lia). rewrite plus_0_r.
  rewrite Nat.mod_mod by (simpl;lia).
  rewrite Nat.mod_small by (simpl;lia).
  unfold fbrev. bdestruct (0 <? S size).
  simpl.
  assert ((size - 0 - 0) = size) by lia.
  rewrite H23.
  unfold nat2fb.
  rewrite N2fb_Ntestbit. rewrite Ntestbit_lt_pow2n. simpl.
  unfold put_cu. unfold get_cua in H3. unfold nor_mode in H1.
  destruct (f c). subst. easy. lia. lia.
  assert (N.of_nat B < N.of_nat (2^size))%N by lia. simpl in H26.
  rewrite Nofnat_pow in H26. simpl in H26. easy. lia.
  specialize (mod_sum_lt A B M H9 H10) as eq2.
  rewrite highbit_means_lt; try lia.
  rewrite plus_comm.
  bdestruct ((A + B) mod M <? A). 
  simpl. 
  unfold put_cu. unfold get_cua in H3. unfold nor_mode in H1.
  destruct (f c). subst. easy. lia. lia.
  rewrite plus_comm in H16.
  apply eq2 in H16. lia.
  assert ((B + A) mod M < M) by (apply Nat.mod_upper_bound;lia).
  simpl. lia.
  rewrite plus_comm.
  assert ((A + B) mod M < A). apply eq2. lia.
  lia.
  constructor.
  apply escope_rz_adder.
  apply escope_rz_sub.
  unfold mod_adder_half.
  remember (rz_adder x (S size) (nat2fb A); rz_sub x (S size) (nat2fb M)) as e1.
  Local Opaque qft_cu one_cu_adder.
  simpl.
  Local Transparent qft_cu one_cu_adder.
  apply phi_modes_exp.
  unfold one_cu_adder. constructor.
  apply escope_rz_adder.
  apply phi_modes_qft_cu ; try easy.
  apply phi_modes_exp. subst.
  constructor. apply escope_rz_adder.
  apply escope_rz_sub. easy.
  unfold nor_mode.
  rewrite efresh_exp_sem_irrelevant. apply H1.
  subst. constructor.
  apply efresh_rz_adder. easy. lia.
  apply efresh_rz_sub. easy. lia. lia.
  unfold nor_mode.
  unfold mod_adder_half.
  remember (rz_adder x (S size) (nat2fb A); rz_sub x (S size) (nat2fb M)) as e1.
  unfold one_cu_adder.
  Local Opaque qft_cu rz_adder.
  simpl.
  Local Transparent qft_cu rz_adder.
  destruct (get_cua (prog_sem aenv (qft_cu x c) (exp_sem aenv e1 f) c)).
  rewrite efresh_exp_sem_irrelevant.
  unfold qft_cu. simpl.
  unfold turn_qft.
  rewrite assign_r_out by iner_p.
  rewrite cnot_sem.
  rewrite eupdate_index_eq.
  unfold turn_rqft.
  rewrite assign_seq_out by easy.
  rewrite Heqe1.
  rewrite efresh_exp_sem_irrelevant.
  unfold nor_mode in H1. destruct (f c).
  unfold put_cu. 1-3:lia.
  constructor.
  apply efresh_rz_adder. easy. lia.
  apply efresh_rz_sub. easy. lia.
  unfold nor_mode.
  unfold turn_rqft. rewrite assign_seq_lt by lia. easy.
  unfold nor_mode.
  unfold turn_rqft. rewrite assign_seq_out by lia.
  rewrite efresh_exp_sem_irrelevant. apply H1.
  subst. constructor.
  apply efresh_rz_adder. easy. lia.
  apply efresh_rz_sub. easy. lia.
  apply efresh_rz_adder. easy. lia.
  unfold qft_cu. simpl.
  unfold turn_qft.
  rewrite assign_r_out by easy.
  rewrite cnot_sem.
  rewrite eupdate_index_eq.
  unfold turn_rqft. rewrite assign_seq_out by easy.
  rewrite efresh_exp_sem_irrelevant.
  unfold nor_mode in H1. unfold put_cu.
  destruct (f c). 1-3:lia.
  subst. constructor.
  apply efresh_rz_adder. easy. lia.
  apply efresh_rz_sub. easy. lia.
  unfold nor_mode.
  unfold turn_rqft.
  rewrite assign_seq_lt; lia.
  unfold nor_mode.
  unfold turn_rqft.
  rewrite assign_seq_out by easy.
  rewrite efresh_exp_sem_irrelevant. apply H1.
  subst. constructor.
  apply efresh_rz_adder. easy. lia.
  apply efresh_rz_sub. easy. lia.
  constructor. easy. apply exp_neu_rz_sub'. easy.
  apply well_typed_right_mode_pexp with (tenv := tenv) (l := l) (l' := l'0); try easy.
  lia.
  assert ((B + A) mod M < M). 
  apply Nat.mod_upper_bound. lia. lia.
  apply qft_uniform_pexp_trans with (tenv := tenv) (l := l) (l' := l'0); try easy.
  apply qft_gt_pexp_trans with (tenv := tenv) (l := l) (l' := l'0); try easy.
  rewrite mod_adder_half_sem with (B := B) 
           (tenv := tenv) (tenv' := env'1)  (l := l) (l' := l'0); try easy.
  rewrite fbrev_twice_same. easy.
  constructor. apply escope_rz_adder.
  apply escope_rz_sub.
  inv H20. constructor. easy. easy.
  eapply typed_pexp_well_formed_ls.
  apply H18. easy.
  eapply typed_pexp_neu_prop.
  apply H18. easy. easy.
Qed.

Lemma phi_nor_mode_rz_modmult' : forall n size y x c aenv f A M, phi_modes f y size -> 
          nor_mode f c -> fst c <> y -> 0 < aenv y ->
       nor_mode (prog_sem aenv (rz_modmult' y x n size c A M) f) c
       /\ phi_modes (prog_sem aenv (rz_modmult' y x n size c A M) f) y size.
Proof.
  induction n; intros.
  simpl. split. easy. easy.
 Local Opaque mod_adder.
 simpl.
 Local Transparent mod_adder.
 specialize (IHn size y x c aenv f A M H H0 H1 H2).
 destruct (get_cua
      (prog_sem aenv (rz_modmult' y x n size c A M) f (x, size - S n))).
 split. apply nor_mode_mod_adder; try easy.
 apply phi_modes_mod_adder; try easy.
 apply IHn; try easy.
Qed.

Lemma exp_fresh_rz_adder' : forall n m size x y M aenv, x <> y -> exp_fresh aenv (y,m) (rz_adder' x n size M).
Proof.
  induction n; intros; simpl.
  constructor. iner_p.
  constructor.
  specialize (IHn m size x y M aenv H). easy.
  destruct (M n). constructor. unfold or_not_r. left. iner_p.
  constructor. iner_p.
Qed.

Lemma exp_fresh_rz_adder'_ge : forall n m size x M aenv, 0 < n -> n <= size <= m -> exp_fresh aenv (x,m) (rz_adder' x n size M).
Proof.
  induction n; intros; simpl.
  constructor. iner_p.
  constructor.
  destruct n. simpl. constructor. iner_p.
  apply IHn. lia. lia.
  destruct (M n). constructor. unfold or_not_r. right. simpl. lia.
  constructor. iner_p.
Qed.

Lemma exp_fresh_rz_sub' : forall n m size x y M aenv, x <> y -> exp_fresh aenv (y,m) (rz_sub' x n size M).
Proof.
  induction n; intros; simpl.
  constructor. iner_p.
  constructor.
  specialize (IHn m size x y M aenv H). easy.
  destruct (M n). constructor. unfold or_not_r. left. iner_p.
  constructor. iner_p.
Qed.

Lemma exp_fresh_rz_sub'_ge : forall n m size x M aenv, 0 < n -> n <= size <= m -> exp_fresh aenv (x,m) (rz_sub' x n size M).
Proof.
  induction n; intros; simpl.
  constructor. iner_p.
  constructor.
  destruct n. simpl. constructor. iner_p.
  apply IHn. lia. lia.
  destruct (M n). constructor. unfold or_not_r. right. simpl. lia.
  constructor. iner_p.
Qed.

Lemma pexp_fresh_mod_adder : 
         forall m size x y c A M aenv, x <> y -> c <> (y,m) ->
          pexp_fresh aenv (y,m) (mod_adder x size c A M).
Proof.
  unfold mod_adder. intros.
  constructor. constructor.
  constructor. constructor. constructor.
  apply exp_fresh_rz_adder'. easy.
  apply exp_fresh_rz_sub'. easy.
  constructor. constructor. constructor. unfold or_not_eq. left. iner_p.
  Local Transparent CNOT.
  constructor. constructor. iner_p. constructor. destruct c. iner_p.
  Local Opaque CNOT.
  constructor. unfold or_not_eq. left. iner_p.
  constructor. constructor. destruct c. iner_p.
  apply exp_fresh_rz_adder'. easy.
  constructor. constructor.
  constructor. apply exp_fresh_rz_sub'. easy.
  constructor. constructor. constructor. unfold or_not_eq. left. iner_p.
  constructor. constructor. constructor. constructor. iner_p.
  Local Transparent CNOT.
  constructor. iner_p. constructor. destruct c. iner_p.
  Local Opaque CNOT.
  constructor. iner_p.
  constructor. unfold or_not_eq. left. iner_p.
  constructor. apply fresh_inv_exp.
  apply exp_fresh_rz_sub'. easy.
Qed.

Lemma pexp_fresh_mod_adder_ge : 
         forall m size x c A M aenv, fst c <> x -> aenv x = size -> 0 < size -> size <= m ->
          pexp_fresh aenv (x,m) (mod_adder x size c A M).
Proof.
  unfold mod_adder. intros.
  constructor. constructor.
  constructor. constructor. constructor.
  apply exp_fresh_rz_adder'_ge; try lia.
  apply exp_fresh_rz_sub'_ge; try lia.
  constructor. constructor. constructor. unfold or_not_eq. right. rewrite H0. simpl. lia.
  Local Transparent CNOT.
  constructor. constructor. iner_p. constructor. destruct c. iner_p.
  Local Opaque CNOT.
  constructor. unfold or_not_eq. right. rewrite H0. simpl. lia.
  constructor. constructor. destruct c. iner_p.
  apply exp_fresh_rz_adder'_ge; try lia.
  constructor. constructor.
  constructor.
  apply exp_fresh_rz_sub'_ge; try lia.
  constructor. constructor.
  constructor. unfold or_not_eq. right. rewrite H0. simpl. lia.
  constructor. constructor. constructor. constructor. iner_p.
  Local Transparent CNOT.
  constructor. iner_p. constructor. destruct c. iner_p.
  Local Opaque CNOT.
  constructor. iner_p.
  constructor. unfold or_not_eq. right. rewrite H0. simpl. lia.
  constructor. apply fresh_inv_exp.
  apply exp_fresh_rz_sub'_ge; try lia.
Qed.


Lemma rz_adder'_ge : forall n m size x M f aenv, 0 < n -> n <= size <= m -> 
         exp_sem aenv (rz_adder' x n size M) f (x,m) = f (x,m).
Proof.
  induction n; intros; simpl. easy.
  destruct (M n). simpl.
  destruct n.
  unfold sr_rotate. simpl.
  rewrite eupdate_index_neq by iner_p.
  rewrite sr_rotate'_ge;try easy. simpl. lia.
  unfold sr_rotate.
  rewrite sr_rotate'_ge;try easy.
  rewrite IHn; try lia. easy. simpl. lia. simpl.
  destruct n. simpl. easy.
  rewrite IHn; try lia. easy.
Qed.

Lemma rz_sub'_ge : forall n m size x M f aenv, 0 < n -> n <= size <= m -> 
         exp_sem aenv (rz_sub' x n size M) f (x,m) = f (x,m).
Proof.
  induction n; intros; simpl. easy.
  destruct (M n). simpl.
  destruct n.
  unfold srr_rotate. simpl.
  rewrite eupdate_index_neq by iner_p.
  rewrite srr_rotate'_ge;try easy. simpl. lia.
  unfold srr_rotate.
  rewrite srr_rotate'_ge;try easy.
  rewrite IHn; try lia. easy. simpl. lia. simpl.
  destruct n. simpl. easy.
  rewrite IHn; try lia. easy.
Qed.

Opaque mod_adder.

Lemma pexp_fresh_mod_mult: forall n m size x y c A M aenv, S n <= size -> m <= size - S n
             -> fst c <> x -> fst c <> y -> x <> y -> 
            pexp_fresh aenv (x,m) (rz_modmult' y x n size c A M).
Proof.
  induction n;intros.
  simpl. constructor. constructor. iner_p.
  simpl. constructor.
  apply IHn; try lia.
  constructor. iner_p.
  apply pexp_fresh_mod_adder. lia. destruct c. iner_p.
Qed.

Lemma pexp_fresh_mod_mult_real: forall n m size x y z c A M aenv, n <= size 
             -> c <> (z,m) -> z <> x -> z <> y -> 
            pexp_fresh aenv (z,m) (rz_modmult' y x n size c A M).
Proof.
  induction n;intros.
  simpl. constructor. constructor. iner_p.
  simpl. constructor.
  apply IHn; try lia. easy.
  constructor. iner_p.
  apply pexp_fresh_mod_adder. lia. easy.
Qed.


Lemma rz_modmult'_x_same: forall n m size x y c A M aenv f, n <= size ->
            fst c <> x -> fst c <> y -> x <> y -> 
             prog_sem aenv (rz_modmult' y x n size c A M) f (x,m) = f (x,m).
Proof.
  induction n;intros. simpl. easy.
  simpl. 
  destruct (get_cua (prog_sem aenv (rz_modmult' y x n size c A M) f (x, size - S n))).
  rewrite fresh_pexp_sem_irrelevant.
  rewrite IHn; try easy. lia.
  apply pexp_fresh_mod_adder; try easy. lia.
  destruct c. iner_p.
  rewrite IHn; try easy. lia.
Qed.

Lemma pexp_fresh_mod_mult_ge: forall n m size x y c A M aenv, 0 < n -> n <= size <= m -> aenv y = size
             -> fst c <> x -> fst c <> y -> x <> y -> 
            pexp_fresh aenv (y,m) (rz_modmult' y x n size c A M).
Proof.
  induction n;intros.
  simpl. constructor. constructor. iner_p.
  bdestruct (n =? 0). subst.
  simpl. constructor. constructor. constructor. iner_p.
  constructor. iner_p.
  apply pexp_fresh_mod_adder_ge; try easy.
  simpl. constructor.
  apply IHn; try lia.
  constructor. iner_p.
  apply pexp_fresh_mod_adder_ge; try easy. lia.
Qed.
 
Lemma rz_modmult'_typed_sem : forall n size y f x c A B M X aenv l l' tenv tenv', n <= S size ->
         nor_modes f x (S size) -> phi_modes f y (S size) -> aenv y = S size ->
          nor_mode f c -> fst c <> x -> fst c <> y -> x <> y -> get_cua (f c) = false
        -> well_typed_pexp aenv l tenv (rz_modmult' y x n (S size) c A M) l' tenv'
        -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f
        -> 1 < M < 2^size -> A < M -> B < M -> X < 2^(S size) 
         -> fbrev (S size) (get_r_qft f y) = nat2fb B ->
        fbrev (S size) (get_cus (S size) f x) = nat2fb X ->
                  well_formed_ls l -> exp_neu_prop l ->
            (prog_sem aenv (rz_modmult' y x n (S size) c A M) f c) = f c
       /\ (get_r_qft (prog_sem aenv (rz_modmult' y x n (S size) c A M) f) y)
           = (fbrev (S size) (nat2fb (((B + (bindecomp n X) * A) mod M)))).
Proof.
  induction n; intros. simpl. split. easy.
 rewrite plus_0_r.
 rewrite Nat.mod_small by lia.
 rewrite <- H16.
 rewrite fbrev_twice_same. easy.
  Local Opaque mod_adder.
  simpl.
  Local Transparent mod_adder.
  inv H8. inv H27.
 rewrite bindecomp_seq.
 rewrite mult_plus_distr_r.
 rewrite fresh_pexp_sem_irrelevant.
 assert ((get_cua (f (x, size - n))) = nat2fb X n).
 rewrite <- get_cus_cua with (n := (S size)) by lia.
 rewrite <- H17.
 unfold fbrev.
 bdestruct (n <? S size). simpl.
 assert ((size - 0 - n) = size - n) by lia. rewrite H20. easy. lia.
 destruct (get_cua (f (x, size - n))) eqn:eq1.
 rewrite mod_adder_sem with (B := (B + bindecomp n X * A) mod M)
      (l := l') (l' := l') (tenv := tenv') (tenv' := tenv'); try easy.
 rewrite mod_adder_typed with (B := (B + bindecomp n X * A) mod M)
      (l := l') (l' := l') (tenv := tenv') (tenv' := tenv'); try easy.
 rewrite <- H8. simpl.
 rewrite <- Nat.add_mod by lia.
 rewrite plus_0_r.
 rewrite plus_assoc.
 split.
 specialize (IHn size y f x c A B M X aenv l l' tenv tenv').
 assert (n <= S size) by lia.
 specialize (IHn H20 H0 H1 H2 H3 H4 H5
        H6 H7 H24 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19).
 destruct IHn. 
 rewrite H23. easy. easy.
 apply phi_nor_mode_rz_modmult'; try easy. lia.
 apply phi_nor_mode_rz_modmult'; try easy. lia.
 specialize (IHn size y f x c A B M X aenv l l' tenv tenv').
 assert (n <= S size) by lia.
 specialize (IHn H20 H0 H1 H2 H3 H4 H5
        H6 H7 H24 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19).
 destruct IHn. 
 rewrite H23. easy.
 apply well_typed_right_mode_pexp with (l := l) (l' := l') (tenv := tenv); try easy.
 apply qft_uniform_pexp_trans with (l := l) (l' := l') (tenv := tenv); try easy.
 apply qft_gt_pexp_trans with (l := l) (l' := l') (tenv := tenv); try easy.
 apply Nat.mod_upper_bound ; lia.
 apply Nat.mod_upper_bound ; lia.
 specialize (IHn size y f x c A B M X aenv l l' tenv tenv').
 assert (n <= S size) by lia.
 specialize (IHn H20 H0 H1 H2 H3 H4 H5
        H6 H7 H24 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19).
 destruct IHn. 
 rewrite H25.
 rewrite fbrev_twice_same. easy.
 eapply typed_pexp_well_formed_ls. apply H24. easy.
 eapply typed_pexp_neu_prop. apply H24. easy. easy.
 apply phi_nor_mode_rz_modmult'; try easy. lia.
 apply phi_nor_mode_rz_modmult'; try easy. lia.
 specialize (IHn size y f x c A B M X aenv l l' tenv tenv').
 assert (n <= S size) by lia.
 specialize (IHn H20 H0 H1 H2 H3 H4 H5
        H6 H7 H24 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19).
 destruct IHn. 
 rewrite H23. easy.
 apply well_typed_right_mode_pexp with (l := l) (l' := l') (tenv := tenv); try easy.
 apply qft_uniform_pexp_trans with (l := l) (l' := l') (tenv := tenv); try easy.
 apply qft_gt_pexp_trans with (l := l) (l' := l') (tenv := tenv); try easy.
 apply Nat.mod_upper_bound ; lia.
 apply Nat.mod_upper_bound ; lia.
 specialize (IHn size y f x c A B M X aenv l l' tenv tenv').
 assert (n <= S size) by lia.
 specialize (IHn H20 H0 H1 H2 H3 H4 H5
        H6 H7 H24 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19).
 destruct IHn. 
 rewrite H25.
 rewrite fbrev_twice_same. easy.
 eapply typed_pexp_well_formed_ls. apply H24. easy.
 eapply typed_pexp_neu_prop. apply H24. easy. easy.
 split.
 specialize (IHn size y f x c A B M X aenv l l' tenv tenv').
 assert (n <= S size) by lia.
 specialize (IHn H20 H0 H1 H2 H3 H4 H5
        H6 H7 H24 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19).
 destruct IHn. 
 rewrite H23. easy.
 specialize (IHn size y f x c A B M X aenv l l' tenv tenv').
 assert (n <= S size) by lia.
 specialize (IHn H20 H0 H1 H2 H3 H4 H5
        H6 H7 H24 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19).
 destruct IHn. 
 rewrite H25.
 rewrite <- H8. simpl.
 rewrite plus_0_r. easy.
 apply pexp_fresh_mod_mult; try lia.
Qed.

Opaque rz_modmult'.

Lemma nor_to_phi_modes: forall x size aenv f, aenv x >= size ->
        nor_modes f x size -> phi_modes (prog_sem aenv (QFT x) f) x size.
Proof.
  intros.
  unfold phi_modes, nor_modes in *.
  intros.
  simpl.
  unfold turn_qft.
  unfold phi_mode.
  specialize (H0 i H1). unfold nor_mode in H0.
  bdestruct (i <? aenv x).
  rewrite assign_r_lt by lia.
  unfold up_qft.
  destruct (f (x,i)); try easy. lia.
Qed.

Lemma phi_to_nor_modes: forall x size aenv f, aenv x >= size ->
        phi_modes f x size -> nor_modes (prog_sem aenv (RQFT x) f) x size.
Proof.
  intros.
  unfold phi_modes, nor_modes in *.
  intros.
  simpl.
  unfold turn_rqft.
  unfold nor_mode.
  specialize (H0 i H1). unfold nor_mode in H0.
  bdestruct (i <? aenv x).
  rewrite assign_seq_lt by lia. easy. lia.
Qed.

Lemma get_cus_qft_out : forall n x y f aenv,
          x <> y -> (get_cus n (prog_sem aenv (QFT y) f) x) = get_cus n f x.
Proof.
  intros.
  unfold get_cus.
  apply functional_extensionality; intro.
  bdestruct (x0 <? n).
  rewrite fresh_pexp_sem_irrelevant. easy.
  constructor. unfold or_not_eq. left. easy. easy.
Qed.

Lemma get_cus_assign_seq_aux : forall n i size x f g, i < n <= size ->
      get_cus size (assign_seq f x g n) x i = g i.
Proof.
  induction n; intros; unfold get_cus in *; simpl.
  lia.
  specialize (IHn i size x f g).
  bdestruct (i <? size).
  bdestruct (i =? n). subst.
  rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn. easy. lia.
  lia.
Qed.

Lemma get_cus_assign_seq : forall size x f g,
      (get_cus size (assign_seq f x g size) x) = cut_n g size.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold cut_n.
  bdestruct (x0 <? size).
  rewrite get_cus_assign_seq_aux.
  easy. lia.
  unfold get_cus.
  bdestruct (x0 <? size). lia. easy.
Qed.


Lemma rz_modmult_half_typed : forall size y f x c A B M X aenv l l' tenv tenv',
         nor_modes f x (S size) -> nor_modes f y (S size) -> aenv y = S size ->
          nor_mode f c -> fst c <> x -> fst c <> y -> x <> y -> get_cua (f c) = false
        -> well_typed_pexp aenv l tenv (rz_modmult_half y x (S size) c A M) l' tenv'
        -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f
        -> 1 < M < 2^size -> A < M -> B < M -> X < 2^(S size) 
         -> fbrev (S size) (get_cus (S size) f y) = nat2fb B ->
        fbrev (S size) (get_cus (S size) f x) = nat2fb X ->
                  well_formed_ls l -> exp_neu_prop l ->
            (prog_sem aenv (rz_modmult_half y x (S size) c A M) f c) = f c.
Proof.
  intros.
  assert (S size <= S size) by lia.
  unfold rz_modmult_half in *.
  assert (prog_sem aenv ((QFT y;; rz_modmult' y x (S size) (S size) c A M);; RQFT y) f
    = prog_sem aenv (RQFT y) 
         (prog_sem aenv (rz_modmult' y x (S size) (S size) c A M)
              (prog_sem aenv (QFT y) f))).
  simpl. easy.
  rewrite H20. clear H20.
  inv H7. inv H24. inv H27. inv H23.
  specialize (rz_modmult'_typed_sem (S size) size y (prog_sem aenv (QFT y) f)
          x c A B M X aenv l'1 l' env'0 env' H19) as eq1.
  assert (nor_modes (prog_sem aenv (QFT y) f) x (S size)).
  unfold nor_modes,nor_mode. intros.
  rewrite fresh_pexp_sem_irrelevant. apply H; easy.
  constructor. unfold or_not_eq. left. iner_p.
  assert (phi_modes (prog_sem aenv (QFT y) f) y (S size)).
  apply nor_to_phi_modes; try lia. easy.
  assert (nor_mode (prog_sem aenv (QFT y) f) c).
  unfold nor_mode.
  rewrite fresh_pexp_sem_irrelevant. apply H2; easy.
  constructor. unfold or_not_eq. left. iner_p.
  assert (get_cua (prog_sem aenv (QFT y) f c) = false).
  unfold get_cua.
  rewrite fresh_pexp_sem_irrelevant.
  destruct (f c); easy.
  constructor. unfold or_not_eq. left. iner_p.
  assert (right_mode_env aenv env'0 (prog_sem aenv (QFT y) f)).
  apply well_typed_right_mode_pexp with 
      (l := l'1) (l' := l'1) (tenv := tenv).
  constructor; easy. easy.
  assert (qft_uniform aenv env'0 (prog_sem aenv (QFT y) f)).
  apply qft_uniform_pexp_trans with 
      (l := l'1) (l' := l'1) (tenv := tenv). easy.
  constructor; easy. easy.
  assert (qft_gt aenv env'0 (prog_sem aenv (QFT y) f)).
  apply qft_gt_pexp_trans with 
      (l := l'1) (l' := l'1) (tenv := tenv). easy.
  constructor; easy. easy.
  assert (fbrev (S size) (get_r_qft (prog_sem aenv (QFT y) f) y) = nat2fb B).
  simpl.
  unfold turn_qft.
  unfold get_r_qft. rewrite assign_r_lt by lia.
  rewrite lshift_fun_0.
  unfold up_qft.
  unfold nor_modes,nor_mode in H0.
  assert (0 < S size) by lia.
  specialize (H0 0 H31).
  destruct (f (y, 0)); try easy.
  rewrite H1. rewrite H15. easy.
  assert (fbrev (S size) (get_cus (S size) (prog_sem aenv (QFT y) f) x) = nat2fb X).
  rewrite get_cus_qft_out. easy. easy.
  specialize (eq1 H7 H22 H1 H23 H3 H4 H5 H25 
            H28 H27 H29 H30 H11 H12 H13 H14 H31 H32 H17 H18).
  destruct eq1.
  remember ((prog_sem aenv (rz_modmult' y x 
         (S size) (S size) c A M) (prog_sem aenv (QFT y) f))) as g.
  simpl.
  unfold turn_rqft.
  rewrite assign_seq_out by lia.
  subst.
  rewrite H33. simpl.
  unfold turn_qft.
  rewrite assign_r_out by lia. easy.
Qed.

Lemma rz_modmult_half_sem : forall size y f x c A B M X aenv l l' tenv tenv',
         nor_modes f x (S size) -> nor_modes f y (S size) -> aenv y = S size ->
          nor_mode f c -> fst c <> x -> fst c <> y -> x <> y -> get_cua (f c) = false
        -> well_typed_pexp aenv l tenv (rz_modmult_half y x (S size) c A M) l' tenv'
        -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f
        -> 1 < M < 2^size -> A < M -> B < M -> X < 2^(S size) 
         -> fbrev (S size) (get_cus (S size) f y) = nat2fb B ->
        fbrev (S size) (get_cus (S size) f x) = nat2fb X ->
                  well_formed_ls l -> exp_neu_prop l ->
            get_cus (S size) (prog_sem aenv (rz_modmult_half y x (S size) c A M) f) y
                   = (fbrev (S size) (nat2fb (((B + X * A) mod M)))).
Proof.
  intros.
  assert (S size <= S size) by lia.
  unfold rz_modmult_half in *.
  assert (prog_sem aenv ((QFT y;; rz_modmult' y x (S size) (S size) c A M);; RQFT y) f
    = prog_sem aenv (RQFT y) 
         (prog_sem aenv (rz_modmult' y x (S size) (S size) c A M)
              (prog_sem aenv (QFT y) f))).
  simpl. easy.
  rewrite H20. clear H20.
  inv H7. inv H24. inv H27. inv H23.
  specialize (rz_modmult'_typed_sem (S size) size y (prog_sem aenv (QFT y) f)
          x c A B M X aenv l'1 l' env'0 env' H19) as eq1.
  assert (nor_modes (prog_sem aenv (QFT y) f) x (S size)).
  unfold nor_modes,nor_mode. intros.
  rewrite fresh_pexp_sem_irrelevant. apply H; easy.
  constructor. unfold or_not_eq. left. iner_p.
  assert (phi_modes (prog_sem aenv (QFT y) f) y (S size)).
  apply nor_to_phi_modes; try lia. easy.
  assert (nor_mode (prog_sem aenv (QFT y) f) c).
  unfold nor_mode.
  rewrite fresh_pexp_sem_irrelevant. apply H2; easy.
  constructor. unfold or_not_eq. left. iner_p.
  assert (get_cua (prog_sem aenv (QFT y) f c) = false).
  unfold get_cua.
  rewrite fresh_pexp_sem_irrelevant.
  destruct (f c); easy.
  constructor. unfold or_not_eq. left. iner_p.
  assert (right_mode_env aenv env'0 (prog_sem aenv (QFT y) f)).
  apply well_typed_right_mode_pexp with 
      (l := l'1) (l' := l'1) (tenv := tenv).
  constructor; easy. easy.
  assert (qft_uniform aenv env'0 (prog_sem aenv (QFT y) f)).
  apply qft_uniform_pexp_trans with 
      (l := l'1) (l' := l'1) (tenv := tenv). easy.
  constructor; easy. easy.
  assert (qft_gt aenv env'0 (prog_sem aenv (QFT y) f)).
  apply qft_gt_pexp_trans with 
      (l := l'1) (l' := l'1) (tenv := tenv). easy.
  constructor; easy. easy.
  assert (fbrev (S size) (get_r_qft (prog_sem aenv (QFT y) f) y) = nat2fb B).
  simpl.
  unfold turn_qft.
  unfold get_r_qft. rewrite assign_r_lt by lia.
  rewrite lshift_fun_0.
  unfold up_qft.
  unfold nor_modes,nor_mode in H0.
  assert (0 < S size) by lia.
  specialize (H0 0 H31).
  destruct (f (y, 0)); try easy.
  rewrite H1. rewrite H15. easy.
  assert (fbrev (S size) (get_cus (S size) (prog_sem aenv (QFT y) f) x) = nat2fb X).
  rewrite get_cus_qft_out. easy. easy.
  specialize (eq1 H7 H22 H1 H23 H3 H4 H5 H25 
            H28 H27 H29 H30 H11 H12 H13 H14 H31 H32 H17 H18).
  destruct eq1.
  remember ((prog_sem aenv (rz_modmult' y x 
         (S size) (S size) c A M) (prog_sem aenv (QFT y) f))) as g.
  simpl.
  unfold turn_rqft. rewrite H1.
  rewrite get_cus_assign_seq.
  rewrite H34.
  rewrite cut_n_fbrev_flip.
  rewrite cut_n_mod.
  rewrite bindecomp_spec.
  rewrite Nat.mod_small.
  rewrite (Nat.mod_small X) by lia. easy.
  assert ((B + X mod 2 ^ S size * A) mod M < M).
  apply Nat.mod_upper_bound. lia. simpl in *. lia.
Qed.

Lemma rz_modmult_half_x_same: forall size y c A M aenv f x m,
            fst c <> x -> fst c <> y -> x <> y -> 
             prog_sem aenv (rz_modmult_half y x size c A M) f (x,m) = f (x,m).
Proof.
  intros. unfold rz_modmult_half. simpl.
  unfold turn_rqft.
  rewrite assign_seq_out by iner_p.
  rewrite rz_modmult'_x_same; try easy.
  unfold turn_qft.
  rewrite assign_r_out by iner_p. easy.
Qed.

Lemma rz_modmult_half_r : forall i size y f x c A M aenv, i < size ->
         nor_modes f x (size) -> nor_modes f y (size) -> aenv y = size ->
          nor_mode f c -> fst c <> x -> fst c <> y -> x <> y ->
            get_r ((prog_sem aenv 
                 (rz_modmult_half y x (size) c A M) f) (y,i)) = get_r (f (y,i)).
Proof.
  intros.
  unfold rz_modmult_half in *.
  simpl.
  unfold turn_rqft.
  rewrite assign_seq_lt;try easy.
Admitted.

Lemma rz_modmult_half_x_cus: forall size y c A M aenv f x,
            fst c <> x -> fst c <> y -> x <> y -> 
          get_cus size (prog_sem aenv 
             (rz_modmult_half y x size c A M) f) x = get_cus size f x.
Proof.
  intros. unfold get_cus.
  apply functional_extensionality; intros.
  bdestruct (x0 <? size).
  rewrite rz_modmult_half_x_same; try easy. easy.
Qed.

Lemma rz_modmult_half_sem_1 : forall size y f x c A B M X aenv l l' tenv tenv',
         nor_modes f x (S size) -> nor_modes f y (S size) -> aenv y = S size ->
          nor_mode f c -> fst c <> x -> fst c <> y -> x <> y -> get_cua (f c) = false
        -> well_typed_pexp aenv l tenv (rz_modmult_half y x (S size) c A M) l' tenv'
        -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f
        -> 1 < M < 2^size -> A < M -> B < M -> X < 2^(S size) 
         -> fbrev (S size) (get_cus (S size) f y) = nat2fb B ->
        fbrev (S size) (get_cus (S size) f x) = nat2fb X ->
                  well_formed_ls l -> exp_neu_prop l ->
           (prog_sem aenv (rz_modmult_half y x (S size) c A M) f)
                   = put_cus f y (fbrev (S size) (nat2fb (((B + X * A) mod M)))) (S size).
Proof.
  intros.
  rewrite <- (rz_modmult_half_sem size y f x c A B M X aenv l l' tenv tenv'); try easy.
  apply functional_extensionality; intros.
  destruct x0.
  bdestruct (v =? y). subst.
  bdestruct (n <? S size). 
  rewrite put_cus_eq by lia.
  rewrite get_cus_cua by lia.
  assert (nor_modes (prog_sem aenv (rz_modmult_half y x (S size) c A M) f) y (S size)).
  unfold rz_modmult_half.
  simpl.
  unfold turn_rqft.
  unfold nor_modes.
  intros.
  unfold nor_mode.
  rewrite assign_seq_lt;try lia.
  unfold nor_modes,nor_mode in H1.
  specialize (H0 n H19) as eq1. unfold nor_mode in eq1.
  unfold put_cu.
  destruct (f (y,n)) eqn:eq2.
  assert (get_r (prog_sem aenv (rz_modmult_half y x (S size) c A M) f (y, n)) = r).
  rewrite rz_modmult_half_r; try easy. rewrite eq2. unfold get_r. easy.
  unfold nor_modes in H20.
  specialize (H20 n H19). unfold nor_mode in H20.
  destruct (prog_sem aenv (rz_modmult_half y x (S size) c A M) f (y, n)).
  unfold get_cua. unfold get_r in H21. subst. easy. 
  lia. lia. lia. lia.
  rewrite put_cus_neq_2; try lia.
  rewrite fresh_pexp_sem_irrelevant; try easy.
  unfold rz_modmult_half.
  constructor. constructor.
  constructor. unfold or_not_eq. right. rewrite H1. simpl. lia.
  apply pexp_fresh_mod_mult_ge; try lia.
  constructor. unfold or_not_eq. right. rewrite H1. simpl. lia.
  rewrite put_cus_neq; try lia.
  bdestruct (v =? x). subst.
  rewrite rz_modmult_half_x_same; try lia. easy.
  bdestruct (c ==? (v,n)). subst.
  rewrite rz_modmult_half_typed with (B := B) (X := X)
           (l:=l) (l':=l') (tenv:=tenv) (tenv':=tenv'); try easy.
  rewrite fresh_pexp_sem_irrelevant; try easy.
  unfold rz_modmult_half.
  constructor. constructor.
  constructor. unfold or_not_eq. left. simpl. easy.
  apply pexp_fresh_mod_mult_real; try lia. easy.
  constructor. unfold or_not_eq. left. simpl. easy.
Qed.

Opaque rz_modmult_half.

Lemma rz_modmult_full_sem : forall size y f x c A Ainv M X aenv l tenv ,
         nor_modes f x (S size) -> nor_modes f y (S size) -> aenv y = S size -> aenv x = S size ->
          nor_mode f c -> fst c <> x -> fst c <> y -> x <> y -> get_cua (f c) = false
        -> well_typed_pexp aenv l tenv (rz_modmult_full y x (S size) c A Ainv M) l tenv
        -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f
        -> 1 < M < 2^size -> A < M -> Ainv < M -> X < M -> A * Ainv mod M = 1
         -> fbrev (S size) (get_cus (S size) f y) = nat2fb 0 ->
            fbrev (S size) (get_cus (S size) f x) = nat2fb X ->
                  well_formed_ls l -> exp_neu_prop l ->
            (prog_sem aenv (rz_modmult_full y x (S size) c A Ainv M) f)
                   = put_cus (put_cus f y (fbrev (S size) (nat2fb (((X * A) mod M)))) (S size)) 
                                    x (fbrev (S size) (nat2fb 0)) (S size).
Proof.
  intros. simpl.
  inv H8.
  apply inv_pexp_reverse with (l := l) 
       (l' := l') (tenv := tenv) (tenv' := env'); try easy.
  assert (rz_modmult_half x y (S size) c Ainv M 
            = inv_pexp (inv_pexp (rz_modmult_half x y (S size) c Ainv M))).
  rewrite inv_pexp_involutive. easy.
  rewrite H8. clear H8.
  apply typed_inv_pexp.
  eapply typed_pexp_well_formed_ls. apply H25. easy.
  eapply typed_pexp_neu_prop. apply H25. easy. easy. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same. easy.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cus_same. easy. easy.
  apply right_mode_exp_put_cus_same. easy.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cus_same. easy. easy.
  unfold nor_modes in *. intros.
  nor_mode_simpl. apply H; lia.
  rewrite rz_modmult_half_sem_1 with (y := y) (x:= x) (l := l) (tenv:=tenv)
           (l':=l') (tenv':=env') (B:=0) (X := X); try easy.
  assert (well_typed_pexp 
           aenv l tenv (rz_modmult_half x y (S size) c Ainv M) l' env').
  assert (rz_modmult_half x y (S size) c Ainv M 
            = inv_pexp (inv_pexp (rz_modmult_half x y (S size) c Ainv M))).
  rewrite inv_pexp_involutive. easy.
  rewrite H8.
  apply typed_inv_pexp.
  eapply typed_pexp_well_formed_ls. apply H25. easy.
  eapply typed_pexp_neu_prop. apply H25. easy. easy. easy.
  rewrite plus_0_l.
  rewrite rz_modmult_half_sem_1 with (y := x) (x:= y) (l := l) (tenv:=tenv)
           (l':=l') (tenv':=env') (B:=0) (X := ((X * A) mod M)); try easy.
  rewrite put_cus_twice_eq.
  rewrite plus_0_l.
  rewrite Nat.mul_mod_idemp_l by lia.
  rewrite <- Nat.mul_assoc.
  rewrite (Nat.mul_mod X (A * Ainv)) by lia.
  rewrite H16.
  rewrite Nat.mul_1_r.
  rewrite Nat.mod_mod by lia.
  rewrite (Nat.mod_small X) by easy.
  apply put_cus_same.
  unfold nor_modes; intros.
  nor_mode_simpl. apply H. easy.
  rewrite get_cus_put_neq by lia.
  rewrite <- H18.
  rewrite fbrev_twice_same. easy.
  unfold nor_modes; intros.
  nor_mode_simpl. apply H0. easy.
  unfold nor_modes; intros.
  nor_mode_simpl. apply H. easy.
  destruct c.
  nor_mode_simpl. lia.
  destruct c.
  rewrite cus_get_neq by iner_p.
  rewrite cus_get_neq by iner_p. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same. easy.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cus_same. easy. easy.
  apply right_mode_exp_put_cus_same. easy.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cus_same. easy. easy.
  unfold nor_modes; intros.
  nor_mode_simpl. apply H. easy. lia.
  assert ((X * A) mod M < M).
  apply Nat.mod_upper_bound. lia. simpl. lia.
  rewrite put_cus_twice_neq by lia.
  rewrite get_cus_put_neq by lia.
  rewrite get_put_cus_cut_n by easy.
  rewrite cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  rewrite cut_n_mod.
  rewrite Nat.mod_small. easy. simpl. lia.
  rewrite get_cus_put_neq by lia.
  rewrite get_put_cus_cut_n by easy.
  rewrite cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  rewrite cut_n_mod.
  rewrite Nat.mod_small. easy. 
  assert ((X * A) mod M < M).
  apply Nat.mod_upper_bound. lia. simpl. lia.
  lia. simpl. lia.
Qed.



(** Functions for extraction & evaluation: **)
(* Implementing x * M multiplier. *)
Fixpoint nat_mult' (n:nat) (size:nat) (x:var) (ex:var) (M:nat->bool) :=
  match n with 
  | 0 => SKIP (x,0)
  | S m => one_cu_adder ex size (x,m) M; 
          nat_mult' m size x ex (cut_n (times_two_spec M) size)
  end.
Definition nat_mult (size:nat) (x:var) (re:var) (M:nat -> bool) := 
  Exp (Rev x; Rev re) ;; QFT re ;; nat_mult' size size x re M;; 
  RQFT re;; inv_pexp (Exp (Rev x; Rev re)).

Definition vars_for_rz_nat_m (size:nat) := gen_vars size (x_var::y_var::[]).

(* z = M * x *)
Definition nat_mult_out (size:nat) (M:nat -> bool) := nat_mult size x_var y_var M.

(* Implementing x * M multiplier for fixedP values. *)
Fixpoint flt_mult' (n:nat) (size:nat) (x:var) (ex:var) (M:nat->bool) :=
  match n with 
  | 0 => SKIP (x,0)
  | S m => one_cu_adder ex size (x,size-n) M; 
          flt_mult' m size x ex (cut_n (div_two_spec M) size)
  end.
Definition flt_mult (size:nat) (x re:var) (M:nat -> bool) := 
  Exp (Rev x; Rev re) ;; flt_mult' size size x re M;; inv_pexp (Exp (Rev x; Rev re)).

(* Implementing x * y multiplier for nats values. *)
(* y is in nor_mode, and y is in phi, [y][x] -> [y][x+y] *)
Fixpoint rz_full_adder_i (re:var) (y:var) (n:nat) (i:nat) :=
  match n with
  | 0 => (SKIP (re,0))
  | S m => (rz_full_adder_i re y m i; (CU (y,m) (SR (m+i) re)))
  end.
Definition one_cu_full_adder_i (c:posi) (re:var) (y:var) (n i : nat) := 
  CU c (rz_full_adder_i re y n i).

(* Here x and y are in nor_mode and re in phi_mode. 
  [x][y][phi(re)] ->[x][y][phi(x*y)], re is supposed to be zero *)
Fixpoint nat_full_mult' (n:nat) (size:nat) (x:var) (y:var) (re:var) :=
   match n with 0 => SKIP (re,0)
            | S m => nat_full_mult' m size x y re;
                 one_cu_full_adder_i (x,size - n) re y (size-m) m
   end.

(* Here x and y are in nor_mode and re in phi_mode. 
   [x][y][phi(re)] ->[x][y][phi(x*y mod 2^n)], re is supposed to be zero, 
   ex is in nor_mode. *)
Definition nat_full_mult (size:nat) (x y:var) (re:var) :=
  Exp (Rev re ; Rev x);; QFT re ;;
  Exp (nat_full_mult' size size x y re) ;;
  RQFT re ;; Exp (Rev re; Rev x).

Definition vars_for_rz_nat_full_m (size:nat) := 
  gen_vars size (x_var::y_var::z_var::[]).

Definition nat_full_mult_out (size:nat) := nat_full_mult size x_var y_var z_var.


(* Implementing x + y addition for fixedp values. *)
Fixpoint rz_full_adder (x:var) (n:nat) (y:var) :=
  match n with
  | 0 => (SKIP (x,0))
  | S m => ((CU (y,m) (SR m x)); rz_full_adder x m y)
  end.
Definition one_cu_full_adder (c:posi) (x:var) (n:nat) (y:var) := 
  CU c (rz_full_adder x n y).

Fixpoint flt_full_mult' (n:nat) (size:nat) (x:var) (y:var) (re:var) (ex:var) :=
  match n with 
  | 0 => SKIP (x,0)
  | S m => one_cu_full_adder (x,m) re size y ; SWAP (y,size - 1) (ex,m); Lshift y;
          flt_full_mult' m size x y re ex
   end.
Definition flt_full_mult_quar (size:nat) (x y:var) (re:var) (ex:var) := 
  flt_full_mult' size size x y re ex.

Fixpoint clean_high_flt (n:nat) (size:nat) (y:var) (ex:var) :=
  match n with 
  | 0 => SKIP (y,0)
  | S m => clean_high_flt m size y ex ;SWAP (y,size - 1) (ex,m); Lshift y
  end.

(* Here x and y are in nor_mode and re in phi_mode. 
   [x][y][phi(re)] ->[x][y][phi((x*2^n*y)/2^n)], re is supposed to be zero, 
   ex is in nor_mode. *)
Definition flt_full_mult (size:nat) (x y:var) (re:var) (ex:var) :=
  Exp (Rev re; Rev x; Rev y);; QFT re ;;
  Exp (flt_full_mult_quar size x y re ex ; inv_exp (clean_high_flt size size y ex)) ;;
  RQFT re ;;(Exp (Rev re; Rev x; Rev y)).

(*
Definition moddoubler01 n x M c1 c2 :=
                doubler1 x;  (comparator01 n x M c1 c2; CU c2 (subtractor01 n M x c1)).

Fixpoint modsummer' i n M x y c1 c2 s (fC : nat -> bool) :=
  match i with
  | 0 => if (fC 0) then (adder01 n x y c1) else (SKIP (x,0))
  | S i' =>  modsummer' i' n M x y c1 c2 s fC; moddoubler01 n x M c1 c2;
          (SWAP c2 (s,i));
        (if (fC i) then (modadder21 n y x M c1 c2) else (SKIP (x,i)))
*)

(* Implementing x < M comparator. *)
Definition rz_comparator (x:var) (n:nat) (c:posi) (M:nat) := 
  Exp (Rev x);; QFT x;; Exp (rz_sub x n (nat2fb M));; RQFT x ;; Exp (CNOT (x,0) c);; 
  inv_pexp (Exp (Rev x);; QFT x;; Exp (rz_sub x n (nat2fb M));; RQFT x).


(* Implementing x + y / X + M addition. *)
Definition rz_full_adder_form (x:var) (n:nat) (y:var) :=
  Exp (Rev x; Rev y);; QFT x ;; rz_full_adder x n y ;; 
  inv_pexp (Exp (Rev x; Rev y);; QFT x).

Definition rz_adder_form (x:var) (n:nat) (M:nat -> bool) :=
  Exp (Rev x);; QFT x;; rz_adder x n M ;; 
  inv_pexp (Exp (Rev x);; QFT x).

Definition vars_for_rz_adder (size:nat) := gen_vars size (x_var::[]).

Definition rz_adder_out (size:nat) (M:nat-> bool) := rz_adder_form x_var size M.

Definition vars_for_rz_full_add (size:nat) := gen_vars size (x_var::y_var::[]).

Definition rz_full_adder_out (size:nat) := rz_full_adder_form x_var size y_var.

(* Implementing x - y subtractor. *)
Fixpoint rz_full_sub (x:var) (n:nat) (y:var) :=
  match n with 
  | 0 => SKIP (x,0)
  | S m => ((CU (y,m) (SRR m x)); rz_full_sub x m y)
  end.

Definition rz_full_sub_form (x:var) (n:nat) (y:var) :=
  Exp (Rev x; Rev y);; QFT x ;; rz_full_sub x n y ;; 
  inv_pexp (Exp (Rev x; Rev y);; QFT x).

(* Implementing x - M subtractor. *)
Definition rz_sub_right (x:var) (n:nat) (M:nat -> bool) :=
  Exp (Rev x);; QFT x;; rz_sub x n M ;; inv_pexp (Exp (Rev x);; QFT x).

(* Implementing M - x subtractor. *)
Definition rz_sub_left (M:nat -> bool) (x:var) (n:nat) :=
  Exp (Rev x);; QFT x;; rz_sub x n M;; inv_pexp (Exp (Rev x);; QFT x);; negator0 n x.

(* Implementing x < y comparator. *)
Definition rz_full_comparator (x:var) (n:nat) (c:posi) (y:var) := 
    Exp (Rev x; Rev y);; QFT x;; QFT y;; Exp (rz_full_sub x n y);; RQFT x ;; Exp (CNOT (x,0) c);;
    inv_pexp (Exp (Rev x; Rev y);; QFT x;; QFT y;; Exp (rz_full_sub x n y);; RQFT x).

(* compare x < M *)
Definition rz_compare_half3 (x:var) (n:nat) (c:posi) (M:nat -> bool) := 
  Exp (rz_sub x n M) ;; RQFT x ;; Exp (CNOT (x,0) c).

(* compare x >= M *)
Definition rz_compare_half2 (x:var) (n:nat) (c:posi) (M:nat -> bool) := 
  Exp (rz_sub x n M) ;; RQFT x ;; Exp (X (x,0); CNOT (x,0) c ; X (x,0)).

(* if x >= M, then the effect of x states. at this point, high-bit of x is 0. 
    otherwise, clean up x, and move on. *)
Fixpoint rz_moder' i (n:nat) (x ex:var) c (M:nat -> bool) := 
     match i with 0 => Exp (SKIP (x,0))
           | S j => rz_compare_half3 x n c M ;; 
                     PCU c (inv_pexp (Exp (rz_sub x n M)));;
                     QFT x ;; X c;; Exp (SWAP c (ex,j));;
                       rz_moder' j n x ex c (cut_n (div_two_spec M) n)
     end.

(* x % M circuit. *)
Definition rz_moder (n:nat) (x re ex:var) c (M:nat) := 
    let i := findnum M n in 
        Exp (Rev x; Rev re);; QFT x;;
          rz_moder' (S i) n x ex c (nat2fb (2^i * M))
            ;; (Exp (copyto x re n));; inv_pexp (rz_moder' (S i) n x ex c (nat2fb (2^i * M)));;
        inv_pexp (Exp (Rev x; Rev re);; QFT x).

Definition vars_for_rz_moder' (size:nat) := 
  gen_vars size (x_var::(y_var::(z_var::([])))).

Definition vars_for_rz_moder (size:nat) :=
  fun x => if x =? s_var then ((S size) * 3,1,id_nat,id_nat) 
        else vars_for_rz_moder' (S size) x.

Definition avs_for_rz_moder (size:nat) := fun x => (x/ (S size), x mod (S size)).

Definition rz_moder_out (size:nat) := 
   rz_moder size x_var y_var z_var (s_var,0).

(* x / M  circuit. *)
Definition rz_div (n:nat) (x re ex:var) c (M:nat) := 
    let i := findnum M n in 
        Exp (Rev x);; QFT x;;
         rz_moder' (S i) n x ex c (nat2fb (2^i * M)) ;;
           Exp (copyto ex re n);; inv_pexp (rz_moder' (S i) n x ex c (nat2fb (2^i * M)));;
        inv_pexp (Exp (Rev x);; QFT x).

Definition vars_for_rz_div' (size:nat) := 
  gen_vars size (x_var::(y_var::(z_var::([])))).

Definition vars_for_rz_div (size:nat) :=
  fun x => if x =? s_var then ((S size) * 3,1,id_nat,id_nat) 
        else vars_for_rz_div' (S size) x.

Definition avs_for_rz_div (size:nat) := fun x => (x/ (S size), x mod (S size)).

Definition rz_div_out (size:nat) := 
   rz_div size x_var y_var z_var (s_var,0).


(* x = (x % M, x / M)  circuit. *)
Definition rz_div_mod (n:nat) (x ex:var) c (M:nat) := 
    let i := findnum M n in 
        Exp (Rev x);; QFT x;;
            rz_moder' (S i) n x ex c (nat2fb (2^i * M));;
        inv_pexp (Exp (Rev x);; QFT x).

Definition vars_for_rz_div_mod' (size:nat) := 
  gen_vars size (x_var::(y_var::(([])))).

Definition vars_for_rz_div_mod (size:nat) :=
  fun x => if x =? z_var then ((S size) * 2,1,id_nat,id_nat) 
        else vars_for_rz_div_mod' (S size) x.

Definition avs_for_rz_div_mod (size:nat) := fun x => (x/ (S size), x mod (S size)).

Definition rz_div_mod_out (size:nat) := 
   rz_div_mod size x_var y_var (z_var,0).




