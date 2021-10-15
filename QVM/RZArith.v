Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import MathSpec.
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
   (rz_sub x n (nat2fb M)) ; RQFT x ; (CNOT (x,0) c).

Definition rz_compare (x:var) (n:nat) (c:posi) (M:nat) := 
 rz_compare_half x n c M ; (inv_exp ( (rz_sub x n (nat2fb M)) ; RQFT x)).

Definition qft_cu (x:var) (c:posi) := 
  RQFT x ;  (CNOT (x,0) c) ; QFT x.

Definition qft_acu (x:var) (c:posi) := 
  RQFT x ;  (X (x,0); CNOT (x,0) c; X (x,0)) ; QFT x.

Definition one_cu_adder (x:var) (n:nat) (c:posi) (M:nat -> bool) := CU c (rz_adder x n M).

Definition mod_adder_half (x:var) (n:nat) (c:posi) (A:nat -> bool) (M:nat -> bool) :=
   (rz_adder x n A; (rz_sub x n M)) ; qft_cu x c ;  (one_cu_adder x n c M).

Definition clean_hbit (x:var) (n:nat) (c:posi) (M:nat -> bool) := 
   (rz_sub x n M) ; qft_acu x c ; ( inv_exp (rz_sub x n M)).

Definition mod_adder (x:var) (n:nat) (c:posi) (A:nat -> bool) (M:nat -> bool) :=
  mod_adder_half x n c A M ; clean_hbit x n c A.

(* modular multiplier: takes [x][0] -> [x][ax%N] where a and N are constant. *)
Fixpoint rz_modmult' (y:var) (x:var) (n:nat) (size:nat) (c:posi) (A:nat) (M:nat) :=
   match n with
   | 0 =>  (SKIP (y,0))
   | S m => rz_modmult' y x m size c A M;
           CU (x,size - n) (mod_adder y size c (nat2fb ((2^m * A) mod M)) (nat2fb M))
   end.

Definition rz_modmult_half y x size c A M := 
   QFT y ; rz_modmult' y x size size c A M ; RQFT y.

Definition rz_modmult_full (y:var) (x:var) (n:nat) (c:posi) (A:nat) (Ainv :nat) (N:nat) :=
  rz_modmult_half y x n c A N ; inv_exp (rz_modmult_half x y n c Ainv N).

Definition vars_for_rz' (size:nat) := gen_vars size (x_var::(y_var::[])).

Definition vars_for_rz (size:nat) := 
       fun x => if x =? z_var then (size * 2,1,id_nat,id_nat) else vars_for_rz' size x.

Definition real_rz_modmult_rev (M C Cinv size:nat) :=
    rz_modmult_full y_var x_var size (z_var,0) C Cinv M.

Definition trans_rz_modmult_rev (M C Cinv size:nat) :=
        trans_exp (vars_for_rz size) (2*size+1) (real_rz_modmult_rev M C Cinv size) (avs_for_arith size).

(*An alternative implementation for comparison on efficiency. *)
Definition one_cu_sub (x:var) (n:nat) (c:posi) (M:nat -> bool) := CU c (rz_sub x n M).

Definition rz_modadder_alt (c1:posi) (x:var) (n:nat) (c:posi) (A:nat -> bool) (M:nat -> bool) :=
   (one_cu_adder x n c1 A; (rz_sub x n M)) ; qft_cu x c ;  (one_cu_adder x n c M; one_cu_sub x n c1 A)
      ; qft_acu x c; ( (one_cu_adder x n c1 A)).

Fixpoint rz_modmult_alt' (y:var) (x:var) (n:nat) (size:nat) (c:posi) (A:nat) (M:nat) :=
   match n with
   | 0 => (SKIP (y,0))
   | S m => rz_modmult_alt' y x m size c A M;
            rz_modadder_alt (x,size-n) y size c (nat2fb ((2^m * A) mod M)) (nat2fb M)
   end.

Definition rz_modmult_half_alt y x size c A M := 
   QFT y ; rz_modmult_alt' y x size size c A M ; RQFT y.

Definition rz_modmult_full_alt (y:var) (x:var) (n:nat) (c:posi) (A:nat) (Ainv :nat) (N:nat) :=
  rz_modmult_half_alt y x n c A N ; inv_exp (rz_modmult_half_alt x y n c Ainv N).

Definition real_rz_modmult_rev_alt (M C Cinv size:nat) :=
    rz_modmult_full_alt y_var x_var size (z_var,0) C Cinv M.

Definition trans_rz_modmult_rev_alt (M C Cinv size:nat) :=
        trans_exp (vars_for_rz size) (2*size+1) (real_rz_modmult_rev_alt M C Cinv size) (avs_for_arith size).


(*********** Proofs ***********)
Lemma rz_adder_well_typed : forall n x size M aenv tenv, n <= size -> size = aenv x -> 
           Env.MapsTo x (Phi (aenv x)) tenv -> well_typed_pexp aenv tenv (rz_adder' x n size M) tenv.
Proof.
 induction n; intros; simpl.
 constructor. constructor.
 apply pe_seq with (env' := tenv).
 apply IHn; try easy. lia.
 destruct (M n).
 constructor.
 apply sr_phi with (n := aenv x). easy.
 subst. lia.
 constructor. constructor.
Qed.

Lemma rz_adder_phi_modes : forall n x size M f aenv tenv, n <= size -> size = aenv x ->
           Env.MapsTo x (Phi (aenv x)) tenv -> right_mode_env aenv tenv f -> 
             phi_modes (exp_sem aenv (rz_adder' x n size M) f) x size.
Proof.
  induction n; intros.
  simpl in *. rewrite H0. apply type_phi_modes with (env := tenv); easy.
  simpl.
  destruct (M n).
  apply sr_phi_modes.
  apply IHn with (tenv := tenv); try easy. lia.
  simpl.
  apply IHn with (tenv := tenv); try easy. lia.
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

Lemma rz_adder_sem : forall n size f x A M aenv tenv, n <= size -> size = aenv x ->
                  Env.MapsTo x (Phi (aenv x)) tenv -> right_mode_env aenv tenv f ->
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
  specialize (rz_adder_phi_modes n x size (nat2fb M) f aenv tenv H6 H0 H1 H2) as eq3.
  unfold phi_modes in eq3. assert (0 < size) by lia. specialize (eq3 0 H7).
  unfold phi_mode in eq3.
  specialize (rz_adder_gt n size aenv (nat2fb M) f x) as X1.
  assert (n <= size) by lia.
  specialize (X1 H8).
  assert ((forall i : nat, i >= size -> get_r_qft f x i = false)).
  intros.
  specialize (nat2fb_bound size A H4 i H9) as X2.
  rewrite <- H5 in X2.
  unfold fbrev in X2. bdestruct (i <? size). lia.
  easy. specialize (X1 H9).
  unfold get_r_qft in X1.
  destruct (exp_sem aenv (rz_adder' x n size (nat2fb M)) f (@pair var nat x O)) eqn:eq2.
   lia. lia.
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

Lemma rz_adder_full : forall size f x A M aenv tenv, size = aenv x ->
                  Env.MapsTo x (Phi (aenv x)) tenv -> right_mode_env aenv tenv f ->
                  M < 2^size -> A < 2^size ->
                  fbrev size (get_r_qft f x) = nat2fb A ->
                  (get_r_qft (exp_sem aenv (rz_adder x size (nat2fb M)) f) x)
                    = (fbrev size (nat2fb ((A + M) mod 2^size))).
Proof.
  intros. unfold rz_adder. rewrite rz_adder_sem with (A:=A) (tenv := tenv); try easy.
  rewrite bindecomp_spec.
  rewrite (Nat.mod_small M) by easy. easy.
Qed.

Lemma rz_sub_well_typed : forall n x size M aenv tenv, n <= size -> size = aenv x -> 
           Env.MapsTo x (Phi (aenv x)) tenv -> well_typed_pexp aenv tenv (rz_sub' x n size M) tenv.
Proof.
 induction n; intros; simpl.
 constructor. constructor.
 apply pe_seq with (env' := tenv).
 apply IHn; try easy. lia.
 destruct (M n).
 constructor.
 apply srr_phi with (n := aenv x). easy.
 subst. lia.
 constructor. constructor.
Qed.

Lemma rz_sub_phi_modes : forall n x size M f aenv tenv, n <= size -> size = aenv x ->
           Env.MapsTo x (Phi (aenv x)) tenv -> right_mode_env aenv tenv f -> 
             phi_modes (exp_sem aenv (rz_sub' x n size M) f) x size.
Proof.
  induction n; intros.
  simpl in *. rewrite H0. apply type_phi_modes with (env := tenv); easy.
  simpl.
  destruct (M n).
  apply srr_phi_modes.
  apply IHn with (tenv := tenv); try easy. lia.
  simpl.
  apply IHn with (tenv := tenv); try easy. lia.
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

Lemma rz_sub_sem : forall n size f x A M aenv tenv, n <= size -> size = aenv x ->
                  Env.MapsTo x (Phi (aenv x)) tenv -> right_mode_env aenv tenv f ->
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
  specialize (rz_sub_phi_modes n x size (nat2fb M) f aenv tenv H6 H0 H1 H2) as eq3.
  unfold phi_modes in eq3. assert (0 < size) by lia. specialize (eq3 0 H7).
  unfold phi_mode in eq3.
  specialize (rz_sub_gt n size aenv (nat2fb M) f x) as X1.
  assert (n <= size) by lia.
  specialize (X1 H8).
  assert ((forall i : nat, i >= size -> get_r_qft f x i = false)).
  intros.
  specialize (nat2fb_bound size A H4 i H9) as X2.
  rewrite <- H5 in X2.
  unfold fbrev in X2. bdestruct (i <? size). lia.
  easy. specialize (X1 H9).
  unfold get_r_qft in X1.
  destruct (exp_sem aenv (rz_sub' x n size (nat2fb M)) f (@pair var nat x O)) eqn:eq2. lia. lia.
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

Lemma rz_sub_full : forall size f x A M aenv tenv, size = aenv x ->
                  Env.MapsTo x (Phi (aenv x)) tenv -> right_mode_env aenv tenv f ->
                  M < 2^size -> A < 2^size ->
                  fbrev size (get_r_qft f x) = nat2fb A ->
                  (get_r_qft (exp_sem aenv (rz_sub x size (nat2fb M)) f) x)
                    = (fbrev size (nat2fb ((A + 2^size - M) mod 2^size))).
Proof.
  intros. unfold rz_sub. rewrite rz_sub_sem with (A:=A) (tenv := tenv); try easy.
  rewrite bindecomp_spec.
  rewrite (Nat.mod_small M) by easy. easy.
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

Lemma rz_compare_half_well_typed : forall x c size M aenv tenv, 
           x <> fst c -> size = aenv x -> 
           Env.MapsTo (fst c) Nor tenv -> Env.MapsTo x (Phi (aenv x)) tenv ->
           well_typed_pexp aenv tenv (rz_compare_half x size c M) (Env.add x Nor tenv).
Proof.
 intros. unfold rz_compare_half.
 apply pe_seq with (env' := (Env.add x Nor tenv)).
 apply pe_seq with (env' := tenv).
 apply rz_sub_well_typed; try easy.
 apply rqft_phi. easy. easy.
 apply cnot_wt_nor. iner_p.
 simpl. apply Env.add_1. easy.
 simpl. apply Env.add_2. easy. easy.
Qed.


Lemma rz_compare_half_sem : forall size f c x A M aenv tenv,
            aenv x = S size -> fst c <> x -> Env.MapsTo x (Phi (aenv x)) tenv -> 
            Env.MapsTo (fst c) Nor tenv -> get_cua (f c) = false ->
            right_mode_env aenv tenv f -> snd c < aenv (fst c)
            -> M < 2^size -> A < 2^S size -> A < 2*M ->
            fbrev (S size) (get_r_qft f x) = nat2fb A ->
                  get_cua ((exp_sem aenv (rz_compare_half x (S size) c M) f) c) = (A <? M).
Proof.
  intros. unfold rz_compare_half.
  assert (well_typed_pexp aenv tenv (rz_sub x (S size) (nat2fb M)) tenv) as X1.
  apply rz_sub_well_typed; try easy.
  assert (well_typed_pexp aenv tenv (RQFT x) (Env.add x Nor tenv)) as X2.
  apply rqft_phi; try easy.
  assert (well_typed_pexp aenv (Env.add x Nor tenv) (CNOT (@pair var nat x O) c) (Env.add x Nor tenv)) as X3.
  apply cnot_wt_nor. destruct c. iner_p.
  simpl. apply Env.add_1. easy.
  apply Env.add_2. iner_p. easy.
  assert (nor_mode f c) as X4.
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  remember (rz_sub x (S size) (nat2fb M)) as e1. simpl.
  rewrite Heqe1 in *. clear Heqe1.
  unfold turn_rqft.
  rewrite rz_sub_full with (A:=A) (tenv:= tenv); try easy.
  unfold rz_compare_half in X1. 
  rewrite cnot_sem.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  rewrite assign_seq_lt by lia.
  rewrite assign_seq_out by iner_p.
  rewrite efresh_exp_sem_irrelevant with (p := c).
  rewrite H3.
  unfold get_cua. bt_simpl.
  unfold fbrev. bdestruct (0 <? S size). simpl.
  assert ((size - 0 - 0) = size) by lia. rewrite H11.
  rewrite <- highbit_means_lt with (size := size); try easy.
  unfold fbrev.
  bdestruct (0 <? S size). simpl.
  rewrite H11. easy. lia. lia.
  apply efresh_rz_sub; try easy.
  unfold nor_mode.
  rewrite assign_seq_out by iner_p.
  rewrite efresh_exp_sem_irrelevant with (p := c).
  apply X4.
  apply efresh_rz_sub; try easy.
  unfold nor_mode.
  rewrite assign_seq_lt by lia. lia.
  unfold nor_mode.
  rewrite assign_seq_out by iner_p.
  rewrite efresh_exp_sem_irrelevant with (p := c).
  apply X4.
  apply efresh_rz_sub; try easy.
  simpl. lia.
Qed.

Lemma rz_compare_sem : forall size f c x A M aenv tenv,
            aenv x = S size -> fst c <> x -> Env.MapsTo x (Phi (aenv x)) tenv -> 
            Env.MapsTo (fst c) Nor tenv -> get_cua (f c) = false -> snd c < aenv (fst c)
            -> M < 2^size -> A < 2^S size -> A < 2*M -> get_cua (f c) = false 
            -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f
             -> fbrev (S size) (get_r_qft f x) = nat2fb A ->
                     exp_sem aenv (rz_compare x (S size) c M) f = f[c|-> put_cu (f c) (A <? M)].
Proof.
  intros. unfold rz_compare. unfold rz_compare_half in *. 
  assert (well_typed_pexp aenv tenv (rz_sub x (S size) (nat2fb M)) tenv) as X1.
  apply rz_sub_well_typed; try easy.
  assert (well_typed_pexp aenv tenv (RQFT x) (Env.add x Nor tenv)) as X2.
  apply rqft_phi; try easy.
  assert (well_typed_pexp aenv (Env.add x Nor tenv) (CNOT (@pair var nat x O) c) (Env.add x Nor tenv)) as X3.
  apply cnot_wt_nor. destruct c. iner_p.
  simpl. apply Env.add_1. easy.
  apply Env.add_2. iner_p. easy.
  assert (nor_mode f c) as X4.
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  remember (rz_sub x (S size) (nat2fb M); RQFT x) as e1. 
  remember (exp_sem aenv e1 f) as g.
  simpl.
  rewrite <- Heqg.
  rewrite cnot_sem.
  rewrite inv_pexp_reverse_1 with (tenv:= tenv) (tenv' := (Env.add x Nor tenv)) (f:=f); try easy.
  rewrite Heqg.
  rewrite Heqe1 in *.
  remember (rz_sub x (S size) (nat2fb M)) as e2. simpl in *.
  unfold turn_rqft. rewrite Heqe2 in *.
  rewrite rz_sub_full with (A:=A) (tenv:= tenv); try easy.
  rewrite assign_seq_lt by lia.
  rewrite assign_seq_out by iner_p.
  rewrite efresh_exp_sem_irrelevant with (p := c).
  rewrite H3.
  unfold get_cua. bt_simpl.
  unfold fbrev. bdestruct (0 <? S size). simpl.
  assert ((size - 0 - 0) = size) by lia. rewrite H14.
  assert ((nat2fb ((A + (2 ^ size + (2 ^ size + 0)) - M)
                mod (2 ^ size + (2 ^ size + 0))) size) = (A <? M)).
  unfold nat2fb.
  rewrite N2fb_Ntestbit.
  bdestruct (A <? M).
  apply Ntestbit_in_pow2n_pow2Sn.
  assert ((2 ^ size + (2 ^ size + 0)) = 2^ S size). simpl. easy.
  rewrite H16.
  split.
  assert (2^size <= (A + 2 ^ S size - M) mod 2 ^ S size).
  assert ((A + 2 ^ S size - M) = 2^S size - (M - A)) by lia.
  rewrite H17.
  assert ((2 ^ S size - (M - A)) < 2 ^ S size) by lia.
  rewrite Nat.mod_small by lia.
  assert (M - A < 2^size) by lia. lia.
  assert (N.of_nat(2 ^ size) <= N.of_nat ((A + 2 ^ S size - M) mod 2 ^ S size))%N by lia.
  simpl in *. rewrite Nofnat_pow in H18. simpl in H18. lia.
  assert ((A + 2 ^ S size - M) mod 2 ^ S size < 2 ^ S size).
  apply Nat.mod_upper_bound. lia.
  assert (N.of_nat ((A + 2 ^ S size - M) mod 2 ^ S size) < N.of_nat (2 ^ S size))%N by lia.
  rewrite Nofnat_pow in H18. 
  assert (N.of_nat (S size) = N.succ (N.of_nat size)) by lia.
  rewrite H19 in H18. simpl in *. lia.
  apply Ntestbit_lt_pow2n.
  assert ((2 ^ size + (2 ^ size + 0)) = 2^ S size). simpl. easy.
  rewrite H16. clear H16.
  assert ((A + 2 ^ S size - M) mod 2 ^ S size < 2 ^ size).
  assert ((A + 2 ^ S size - M) = 2 ^ S size + (A - M)) by lia.
  rewrite H16. clear H16.
  assert (2^ size <> 0).
  apply Nat.pow_nonzero. lia.
  rewrite Nat.add_mod by (simpl;lia).
  rewrite Nat.mod_same by (simpl;lia).
  rewrite plus_0_l.
  rewrite Nat.mod_mod by (simpl;lia).
  rewrite Nat.mod_small by (simpl;lia).
  simpl. lia.
  assert (N.of_nat ((A + 2 ^ S size - M) mod 2 ^ S size) < N.of_nat (2 ^ size))%N by lia.
  rewrite Nofnat_pow in H17. 
  simpl in *. lia. rewrite H15. easy. lia.
  apply efresh_rz_sub; try easy. simpl. lia.
  subst. 
  apply pe_seq with (env' := tenv).
  easy. easy.
  subst. 
  constructor. 
  apply efresh_rz_sub; try easy.
  constructor. unfold or_not_eq. left. easy.
  subst. simpl. unfold turn_rqft.
  unfold nor_mode. simpl.
  rewrite assign_seq_lt. lia. rewrite H. lia.
  subst. 
  unfold nor_mode.
  rewrite efresh_exp_sem_irrelevant with (p := c).
  apply X4.
  constructor. 
  apply efresh_rz_sub; try easy.
  constructor. unfold or_not_eq. left. easy.
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

Lemma escope_inv : forall e y n aenv,
         exp_scope aenv y n e -> exp_scope aenv y n (inv_exp e).
Proof.
  induction e;intros; simpl.
  constructor. constructor. constructor.
  inv H. apply IHe. easy. 
  1-5:constructor.
  inv H. constructor. easy.
  apply rshift_scope_nhit. easy.
  inv H. constructor. easy.
  apply lshift_scope_nhit. easy.
  inv H. constructor. easy.
  apply rev_scope_nhit. easy.
  inv H. inv H. inv H.
  inv H. constructor.
  apply IHe2. easy. apply IHe1. easy.
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
  inv H. inv H. inv H.
  inv H.
  specialize (IHe1 aenv f x size H5 H0).
  specialize (IHe2 aenv (exp_sem aenv e1 f) x size H6 IHe1). easy.
Qed.

Lemma adder_sub_seq : forall size f x B A M aenv tenv,
            size = aenv x -> Env.MapsTo x (Phi (aenv x)) tenv -> right_mode_env aenv tenv f -> 
                  1 < M < 2^size -> A < 2^size -> B < 2^size ->
                  fbrev size (get_r_qft f x) = nat2fb B ->
                  (get_r_qft (exp_sem aenv (rz_adder x size (nat2fb A); (rz_sub x size (nat2fb M))) f) x)
                    = (fbrev size (nat2fb (((B + A) + 2^size - M) mod 2^size))).
Proof.
  intros.
  specialize (rz_adder_full size f x B A aenv tenv H H0 H1 H3 H4 H5) as eq1.
  simpl.
  assert (fbrev size (get_r_qft (exp_sem aenv (rz_adder x size (nat2fb A)) f) x) 
               = (nat2fb ((B + A) mod 2 ^ size))).
  rewrite eq1. rewrite fbrev_twice_same. easy.
  rewrite rz_sub_full with (A:= ((B + A) mod 2 ^ size)) (tenv:=tenv); try easy.
  assert (2 ^ size - M = (2 ^ size - M) mod 2^size).
  rewrite Nat.mod_small by lia. easy.
  assert (((B + A) mod 2 ^ size + 2 ^ size - M) =
              ((B + A) mod 2 ^ size + (2 ^ size - M))) by lia.
  rewrite H8. rewrite H7.
  rewrite <- Nat.add_mod by lia.
  assert ((B + A + (2 ^ size - M)) = ((B + A + 2 ^ size - M))) by lia.
  rewrite H9. easy.
  apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
  apply rz_adder_well_typed; try easy.
  apply Nat.mod_upper_bound. lia.
Qed.

Lemma qft_cu_sem : forall tenv aenv f x c size,
            aenv x = S size -> fst c <> x -> Env.MapsTo x (Phi (aenv x)) tenv -> 
            Env.MapsTo (fst c) Nor tenv -> snd c < aenv (fst c) ->
             right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
          exp_sem aenv (qft_cu x c) f = f[c |-> put_cu (f c) ((get_r_qft f x 0) ⊕ get_cua (f c))].
Proof.
  intros.
  unfold qft_cu.
  remember (RQFT x) as e.
  assert (QFT x = inv_exp e). rewrite Heqe. simpl. easy.
  rewrite H7. simpl.
  rewrite cnot_sem.
  rewrite efresh_exp_sem_out.
  assert ((exp_sem aenv (inv_exp e) (exp_sem aenv e f))
          = exp_sem aenv (e ; inv_exp e) f). simpl. easy.
  rewrite H8.
  rewrite inv_exp_correct_rev with (tenv := tenv) (tenv' := Env.add x Nor tenv); try easy.
  apply eupdate_same_1. easy.
  rewrite Heqe. simpl.
  unfold turn_rqft,turn_qft.
  rewrite assign_seq_out; try iner_p.
  rewrite assign_seq_lt; try lia.
  assert (get_cua (nval (get_r_qft f x 0) (get_r (f (@pair var nat x O)))) = (get_r_qft f x 0)).
  unfold get_cua. easy.
  rewrite H9. easy.
  rewrite Heqe.
  apply rqft_phi. easy.
  easy.
  rewrite Heqe. simpl.
  constructor. unfold or_not_eq. left. easy.
  rewrite Heqe. simpl.
  unfold turn_rqft.
  unfold nor_mode.
  rewrite assign_seq_lt; try lia.
  rewrite Heqe. simpl.
  unfold nor_mode,turn_rqft.
  assert (nor_mode f c).
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  rewrite assign_seq_out; easy.
Qed.

Lemma qft_acu_sem : forall tenv aenv f x c size,
            aenv x = S size -> fst c <> x -> Env.MapsTo x (Phi (aenv x)) tenv -> 
            Env.MapsTo (fst c) Nor tenv -> snd c < aenv (fst c) ->
             right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
           exp_sem aenv (qft_acu x c) f = f[c |-> put_cu (f c) ((¬ (get_r_qft f x 0)) ⊕ get_cua (f c))].
Proof.
  intros.
  unfold qft_acu.
  remember (RQFT x) as e.
  assert (QFT x = inv_exp e). rewrite Heqe. simpl. easy.
  rewrite H7. simpl.
  rewrite cnot_sem.
  destruct c.
  rewrite eupdate_index_eq.
  rewrite eupdate_twice_neq by iner_p.
  rewrite eupdate_twice_eq.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by iner_p.
  assert (((exp_sem aenv e f) [(@pair var nat x O)
    |-> exchange (exchange (exp_sem aenv e f (@pair var nat x O)))]) = (exp_sem aenv e f)).
  rewrite eupdate_same. easy.
  unfold exchange.
  destruct (exp_sem aenv e f (@pair var nat x O)) eqn:eq1.
  assert ((¬ (¬ b)) = b) by btauto. rewrite H8. 1-3:easy.
  rewrite H8.
  rewrite efresh_exp_sem_out.
  assert ((exp_sem aenv (inv_exp e) (exp_sem aenv e f))
          = exp_sem aenv (e ; inv_exp e) f). simpl. easy.
  rewrite H9.
  rewrite inv_exp_correct_rev with (tenv := tenv) (tenv' := Env.add x Nor tenv); try easy.
  apply eupdate_same_1. easy.
  rewrite Heqe. simpl.
  unfold turn_rqft,turn_qft.
  rewrite assign_seq_out; try iner_p.
  rewrite assign_seq_lt; try lia.
  unfold exchange. unfold get_cua. easy.
  rewrite Heqe. simpl. constructor. easy. easy.
  subst. simpl. constructor.
  unfold or_not_eq. left. easy.
  unfold nor_mode. rewrite eupdate_index_eq.
  rewrite Heqe. simpl.
  unfold turn_rqft.
  rewrite assign_seq_lt; try lia. unfold exchange. lia.
  rewrite Heqe.
  simpl.
  unfold nor_mode,turn_rqft.
  rewrite eupdate_index_neq.
  assert (nor_mode f c).
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  rewrite assign_seq_out; easy. destruct c. iner_p. 
Qed.

Lemma mod_adder_half_sem : forall size f x c A B M aenv tenv,
            aenv x = S size -> fst c <> x -> Env.MapsTo x (Phi (aenv x)) tenv -> 
            Env.MapsTo (fst c) Nor tenv  -> get_cua (f c) = false -> snd c < aenv (fst c)
            -> 1 < M < 2^size -> A < M -> B < M -> fbrev (S size) (get_r_qft f x) = nat2fb B
            -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
      (get_r_qft (exp_sem aenv (mod_adder_half x (S size) c (nat2fb A) (nat2fb M)) f) x)
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
  rewrite adder_sub_seq with (B := B) (tenv:=tenv) ; try easy.
  1-3:simpl;lia.
  Check qft_cu_sem.
  rewrite qft_cu_sem with (tenv := tenv) (size := size); try easy.
  assert ((g c) = f c). subst.
  rewrite efresh_exp_sem_irrelevant. easy.
  constructor. apply efresh_rz_adder; easy.
  apply efresh_rz_sub;easy.
  rewrite H13.
  rewrite H3. bt_simpl. rewrite H12.
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
  rewrite rz_adder_full with (A:= ((B + A + 2 ^ S size - M) mod 2 ^ S size)) (tenv:= tenv); try easy.
  assert (2^S size <> 0).
  apply Nat.pow_nonzero; lia.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_mod by lia.
  rewrite <- Nat.add_mod by lia.
  assert (M < 2^S size) by (simpl;lia).
  assert (B + A + 2 ^ S size - M + M = B + A + 2^S size) by lia.
  rewrite H17.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small by lia.
  rewrite Nat.mod_small by lia. easy.
  subst. 
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply pe_seq with (env' := tenv).
  apply rz_adder_well_typed; try easy.
  apply rz_sub_well_typed; try easy. easy.
  simpl. lia.
  apply Nat.mod_upper_bound.
  apply Nat.pow_nonzero ; lia.
  rewrite H12.
  rewrite fbrev_twice_same. easy.
  rewrite get_r_qft_out by easy.
  rewrite H12.
  assert ((B + A + 2 ^ S size - M) = (B + A - M) + 2^S size) by lia.
  rewrite H15.
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
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  subst.
  apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
  apply pe_seq with (env' := tenv).
  apply rz_adder_well_typed; try easy.
  apply rz_sub_well_typed; try easy.
  subst.
  apply qft_uniform_exp_trans with (tenv := tenv); try easy.
  apply pe_seq with (env' := tenv).
  apply rz_adder_well_typed; try easy.
  apply rz_sub_well_typed; try easy.
  subst.
  apply qft_gt_exp_trans with (tenv := tenv); try easy.
  apply pe_seq with (env' := tenv).
  apply rz_adder_well_typed; try easy.
  apply rz_sub_well_typed; try easy.
Qed.

Lemma clean_hbit_sem: forall size f x c B A aenv tenv, 
            aenv x = S size -> fst c <> x -> Env.MapsTo x (Phi (aenv x)) tenv -> 
            Env.MapsTo (fst c) Nor tenv -> snd c < aenv (fst c)
            -> A < 2^ size -> B < 2^size -> fbrev (S size) (get_r_qft f x) = nat2fb B
            -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
        exp_sem aenv (clean_hbit x (S size) c (nat2fb A)) f =
                f[c |-> put_cu (f c) ((¬ (fbrev (S size)
                           (nat2fb ((B + 2^S size - A) mod 2^S size)) 0)) ⊕ get_cua (f c))].
Proof.
  intros.
  Local Opaque rz_sub qft_acu. simpl.
  Local Transparent rz_sub qft_acu.
  assert (A < 2^ S size) by (simpl;lia).
  assert (B < 2^ S size) by (simpl;lia).
  assert (S size = aenv x) as X1 by lia.
  specialize (rz_sub_full (S size) f x B A aenv tenv X1 H1 H7 H10 H11 H6) as eq1.
  rewrite qft_acu_sem with (tenv := tenv) (size := size); try easy.
  rewrite efresh_exp_sem_out.
  assert ((exp_sem aenv (inv_exp (rz_sub x (S size) (nat2fb A)))
   (exp_sem aenv (rz_sub x (S size) (nat2fb A)) f))
   = exp_sem aenv (rz_sub x (S size) (nat2fb A) ; inv_exp (rz_sub x (S size) (nat2fb A))) f).
  easy.
  rewrite H12. clear H12.
  rewrite inv_exp_correct_rev with (tenv := tenv) (tenv' := tenv); try easy.
  apply eupdate_same_1. easy.
  rewrite eq1.
  rewrite efresh_exp_sem_irrelevant. simpl. easy.
  apply efresh_rz_sub; try lia. easy.
  apply rz_sub_well_typed; try easy.
  apply fresh_inv_exp.
  apply efresh_rz_sub; try lia. easy.
  apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
  apply rz_sub_well_typed; try easy.
  apply qft_uniform_exp_trans with (tenv := tenv); try easy.
  apply rz_sub_well_typed; try easy.
  apply qft_gt_exp_trans with (tenv := tenv); try easy.
  apply rz_sub_well_typed; try easy.
Qed.

Lemma qft_cu_r_same : forall aenv x c f, nor_mode f c -> fst c <> x -> 0 < aenv x ->
             get_r ((exp_sem aenv (qft_cu x c) f) c) = get_r (f c).
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
                nor_mode (exp_sem aenv (qft_cu x p) f) p.
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
                nor_mode (exp_sem aenv (qft_acu x p) f) p.
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
          nor_mode f c -> fst c <> x -> 0 < aenv x -> nor_mode (exp_sem aenv (mod_adder x n c A M) f) c.
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
          nor_mode f c -> fst c <> x -> 0 < aenv x -> phi_modes (exp_sem aenv (qft_cu x c) f) x n.
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
          nor_mode f c -> fst c <> x -> 0 < aenv x -> phi_modes (exp_sem aenv (qft_acu x c) f) x n.
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
          nor_mode f c -> fst c <> x -> 0 < aenv x -> phi_modes (exp_sem aenv (mod_adder x n c A M) f) x n.
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


Lemma exp_neu_rz_adder : forall n x y size M, n <= size -> exp_neu_l y [] (rz_adder' x n size M) [].
Proof.
 induction n;intros;simpl. constructor.
 apply seq_neul with (l' := []).
 apply IHn. lia.
 destruct (M n). constructor. constructor.
Qed.

Lemma mod_adder_half_well_typed : forall x c size A M aenv tenv,
            aenv x = size -> fst c <> x -> Env.MapsTo x (Phi (aenv x)) tenv -> Env.MapsTo (fst c) Nor tenv
          -> well_typed_pexp aenv tenv (mod_adder_half x size c A M) tenv.
Proof.
 intros. unfold mod_adder_half.
 apply pe_seq with (env' := tenv).
 apply pe_seq with (env' := tenv).
 apply pe_seq with (env' := tenv).
 apply rz_adder_well_typed; try easy.
 apply rz_sub_well_typed; try easy.
 unfold qft_cu.
 apply pe_seq with (env' := Env.add x Nor tenv).
 apply pe_seq with (env' := Env.add x Nor tenv).
 apply rqft_phi. easy.
 easy.
 apply cnot_wt_nor; try easy. destruct c. iner_p.
 simpl. apply Env.add_1. easy.
 simpl. apply Env.add_2. iner_p. easy.
 apply qft_nor. apply Env.add_1. easy.
 apply EnvFacts.Equal_mapsto_iff.
 intros. split. intros.
 bdestruct (k =? x). subst.
 apply mapsto_always_same with (v2 := e) in H1. subst.
 apply Env.add_1. easy. easy.
 apply Env.add_2. lia. apply Env.add_2. lia. easy.
 intros.
 bdestruct (k =? x). subst. 
 apply mapsto_add1 in H3. subst. easy.
 apply Env.add_3 in H3. apply Env.add_3 in H3. easy. lia. lia.
 unfold one_cu_adder.
 apply pcu_nor; try easy.
 apply efresh_rz_adder; try easy.
 simpl.
 unfold exp_neu. intros.
 apply exp_neu_rz_adder. easy.
 apply rz_adder_well_typed; try easy.
Qed.

Lemma mod_adder_well_typed : forall x c size A M aenv tenv,
            aenv x = size -> fst c <> x -> Env.MapsTo x (Phi (aenv x)) tenv -> Env.MapsTo (fst c) Nor tenv
          -> well_typed_pexp aenv tenv (mod_adder x size c A M) tenv.
Proof.
 intros. unfold mod_adder,mod_adder_half,clean_hbit.
 apply pe_seq with (env' := tenv).
 apply pe_seq with (env' := tenv).
 apply pe_seq with (env' := tenv).
 apply pe_seq with (env' := tenv).
 apply rz_adder_well_typed; try easy.
 apply rz_sub_well_typed; try easy.
 unfold qft_cu.
 apply pe_seq with (env' := Env.add x Nor tenv).
 apply pe_seq with (env' := Env.add x Nor tenv).
 apply rqft_phi. easy.
 easy.
 apply cnot_wt_nor; try easy. destruct c. iner_p.
 simpl. apply Env.add_1. easy.
 simpl. apply Env.add_2. iner_p. easy.
 apply qft_nor. apply Env.add_1. easy.
 apply EnvFacts.Equal_mapsto_iff.
 intros. split. intros.
 bdestruct (k =? x). subst.
 apply mapsto_always_same with (v2 := e) in H1. subst.
 apply Env.add_1. easy. easy.
 apply Env.add_2. lia. apply Env.add_2. lia. easy.
 intros.
 bdestruct (k =? x). subst. 
 apply mapsto_add1 in H3. subst. easy.
 apply Env.add_3 in H3. apply Env.add_3 in H3. easy. lia. lia.
 unfold one_cu_adder.
 apply pcu_nor; try easy.
 apply efresh_rz_adder; try easy.
 simpl.
 unfold exp_neu. intros.
 apply exp_neu_rz_adder. easy.
 apply rz_adder_well_typed; try easy.
 apply pe_seq with (env' := tenv).
 apply pe_seq with (env' := tenv).
 apply rz_sub_well_typed; try easy.
 unfold qft_acu.
 apply pe_seq with (env' := Env.add x Nor tenv).
 apply pe_seq with (env' := Env.add x Nor tenv).
 apply rqft_phi. easy. easy.
 apply pe_seq with (env' := Env.add x Nor tenv).
 apply pe_seq with (env' := Env.add x Nor tenv).
 constructor. constructor. simpl. apply Env.add_1. easy.
 apply cnot_wt_nor. destruct c. iner_p.
 simpl. apply Env.add_1. easy.
 apply Env.add_2. iner_p. easy.
 constructor. constructor. simpl. apply Env.add_1. easy.
 apply qft_nor. apply Env.add_1. easy.
 apply EnvFacts.Equal_mapsto_iff.
 intros. split. intros.
 bdestruct (k =? x). subst.
 apply mapsto_always_same with (v2 := e) in H1. subst.
 apply Env.add_1. easy. easy.
 apply Env.add_2. lia. apply Env.add_2. lia. easy.
 intros.
 bdestruct (k =? x). subst. 
 apply mapsto_add1 in H3. subst. easy.
 apply Env.add_3 in H3. apply Env.add_3 in H3. easy. lia. lia.
 apply typed_inv_pexp.
 apply rz_sub_well_typed; try easy.
Qed.

Lemma mod_adder_sem : forall size f x c A B M aenv tenv,
            aenv x = S size -> fst c <> x -> Env.MapsTo x (Phi (aenv x)) tenv -> 
            Env.MapsTo (fst c) Nor tenv  -> get_cua (f c) = false -> snd c < aenv (fst c)
            -> 1 < M < 2^size -> A < M -> B < M -> fbrev (S size) (get_r_qft f x) = nat2fb B
            -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
      (get_r_qft (exp_sem aenv (mod_adder x (S size) c (nat2fb A) (nat2fb M)) f) x)
           = (fbrev (S size) (nat2fb (((B + A) mod M)))).
Proof.
  intros.
  Local Opaque mod_adder_half clean_hbit. simpl.
  Local Transparent mod_adder_half clean_hbit.
  assert (exp_scope aenv x (S size)
        (rz_adder x (S size) (nat2fb A); rz_sub x (S size) (nat2fb M))).
  constructor. apply escope_rz_adder. apply escope_rz_sub.
  Check mod_adder_half_sem.
  specialize (mod_adder_half_sem size f x c A B M aenv tenv
              H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11) as eq1.
  Check clean_hbit_sem.
  rewrite clean_hbit_sem with (tenv := tenv) (B:=((B + A) mod M)); try easy.
  rewrite get_r_qft_out by easy.
  rewrite eq1. easy. lia.
  assert ((B + A) mod M < M). 
  apply Nat.mod_upper_bound. lia. lia.
  rewrite eq1.
  rewrite fbrev_twice_same. easy.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply mod_adder_half_well_typed; try easy. easy.
  apply qft_uniform_exp_trans with (tenv := tenv). easy.
  apply mod_adder_half_well_typed; try easy. easy.
  apply qft_gt_exp_trans with (tenv := tenv). easy.
  apply mod_adder_half_well_typed; try easy. easy.
Qed.

Lemma mod_adder_half_high : forall size f x c A B M aenv tenv,
            aenv x = S size -> fst c <> x -> Env.MapsTo x (Phi (aenv x)) tenv -> 
            Env.MapsTo (fst c) Nor tenv  -> get_cua (f c) = false -> snd c < aenv (fst c)
            -> 1 < M < 2^size -> A < M -> B < M -> fbrev (S size) (get_r_qft f x) = nat2fb B
            -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
      get_cua ((exp_sem aenv (mod_adder_half x (S size) c (nat2fb A) (nat2fb M)) f) c) = (B + A <? M).
Proof.
  intros.
  unfold mod_adder_half,qft_cu.
  assert (exp_sem aenv
     (((rz_adder x (S size) (nat2fb A); rz_sub x (S size) (nat2fb M));
       ((RQFT x; CNOT (@pair var nat x O) c); QFT x));
      one_cu_adder x (S size) c (nat2fb M)) f
      = (exp_sem aenv
        ( (rz_adder x (S size) (nat2fb A)); rz_compare_half x (S size) c M ;
          QFT x ; one_cu_adder x (S size) c (nat2fb M)) f)).
  simpl. easy.
  rewrite H12.
  Local Opaque rz_compare_half rz_adder.
  simpl.
  Local Transparent rz_compare_half rz_adder.
  assert (A < 2 ^ S size) by (simpl;lia).
  assert (B < 2 ^ S size) by (simpl;lia).
  Check rz_adder_full.
  assert (S size = aenv x) as X1 by easy.
  specialize (rz_adder_full (S size) f x B A aenv tenv X1 H1 H9 H13 H14 H8) as eq1.
  unfold turn_qft.
  rewrite assign_r_out by easy.
  assert (get_cua
       (exp_sem aenv (rz_compare_half x (S size) c M)
          (exp_sem aenv (rz_adder x (S size) (nat2fb A)) f) c) = (B + A <? M)).
  Check rz_compare_half_sem.
  rewrite rz_compare_half_sem with (A:=(B + A)) (tenv := tenv); try easy.
  rewrite efresh_exp_sem_irrelevant. easy.
  apply efresh_rz_adder. easy. lia.
  apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
  apply rz_adder_well_typed; try easy.
  simpl. lia. lia.
  rewrite eq1.
  rewrite fbrev_twice_same.
  rewrite Nat.mod_small by (simpl;lia). easy.
  rewrite H15.
  bdestruct (B + A <? M).
  rewrite efresh_exp_sem_irrelevant.
  rewrite assign_r_out by easy.
  rewrite H15. easy.
  apply efresh_rz_adder. easy. lia.
  rewrite assign_r_out by easy.
  rewrite H15. easy.
Qed.


Lemma mod_adder_typed : forall size f x c A B M aenv tenv,
            aenv x = S size -> fst c <> x -> Env.MapsTo x (Phi (aenv x)) tenv -> 
            Env.MapsTo (fst c) Nor tenv  -> get_cua (f c) = false -> snd c < aenv (fst c)
            -> 1 < M < 2^size -> A < M -> B < M -> fbrev (S size) (get_r_qft f x) = nat2fb B
            -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
            (exp_sem aenv (mod_adder x (S size) c (nat2fb A) (nat2fb M)) f) c = f c.
Proof.
  intros.
  Local Opaque mod_adder_half clean_hbit. simpl.
  Local Transparent mod_adder_half clean_hbit.
  assert (nor_mode f c) as X1.
  apply type_nor_mode with (aenv := aenv) (env := tenv); easy.
  rewrite clean_hbit_sem with (B:= (((B + A) mod M))) (tenv := tenv); try easy.
  rewrite eupdate_index_eq.
  rewrite mod_adder_half_high with (B:=B) (tenv:=tenv) ; try easy.
  assert (forall b, put_cu (exp_sem aenv 
           (mod_adder_half x (S size) c (nat2fb A) (nat2fb M)) f c) b = put_cu (f c) b).
  intros. unfold mod_adder_half in *.
  remember ((rz_adder x (S size) (nat2fb A); rz_sub x (S size) (nat2fb M))) as e1.
  Local Opaque one_cu_adder qft_cu. simpl. Local Transparent one_cu_adder qft_cu.
  rewrite put_cu_get_r.
  rewrite one_cu_adder_r_same by easy.
  rewrite qft_cu_r_same ; try easy.
  rewrite efresh_exp_sem_irrelevant.
  unfold nor_mode in X1.
  destruct (f c). unfold get_r.
  unfold get_cua in H3. subst.
  unfold put_cu. easy. lia. lia.
  subst. constructor.
  apply efresh_rz_adder. easy. lia.
  apply efresh_rz_sub. easy. lia.
  unfold nor_mode.
  rewrite efresh_exp_sem_irrelevant. apply X1.
  subst. constructor.
  apply efresh_rz_adder. easy. lia.
  apply efresh_rz_sub. easy. lia. lia.
  Local Opaque one_cu_adder qft_cu. simpl. Local Transparent one_cu_adder qft_cu.
  apply nor_mode_one_cu_adder; try easy.
  apply nor_mode_qft_cu; try lia.
  unfold nor_mode. subst.
  rewrite efresh_exp_sem_irrelevant. apply X1.
  constructor.
  apply efresh_rz_adder. easy. lia.
  apply efresh_rz_sub. easy. lia. easy.
  rewrite H12.
  bdestruct (B + A <? M).
  rewrite (Nat.mod_small (B+A)) by lia.
  assert ((B + A + 2 ^ S size - A) = B + 2^S size) by lia.
  rewrite H14.
  rewrite Nat.add_mod by (simpl;lia).
  rewrite Nat.mod_same by (simpl;lia). rewrite plus_0_r.
  rewrite Nat.mod_mod by (simpl;lia).
  rewrite Nat.mod_small by (simpl;lia).
  unfold fbrev. bdestruct (0 <? S size).
  simpl.
  assert ((size - 0 - 0) = size) by lia.
  rewrite H16.
  unfold nat2fb.
  rewrite N2fb_Ntestbit. rewrite Ntestbit_lt_pow2n. simpl.
  unfold put_cu. unfold get_cua in H3. unfold nor_mode in X1.
  destruct (f c). subst. easy. lia. lia.
  assert (N.of_nat B < N.of_nat (2^size))%N by lia. simpl in H17.
  rewrite Nofnat_pow in H17. simpl in H17. easy. lia.
  specialize (mod_sum_lt A B M H6 H7) as eq2.
  rewrite highbit_means_lt; try lia.
  rewrite plus_comm.
  bdestruct ((A + B) mod M <? A). 
  simpl. 
  unfold put_cu. unfold get_cua in H3. unfold nor_mode in X1.
  destruct (f c). subst. easy. lia. lia.
  rewrite plus_comm in H13.
  apply eq2 in H13. lia.
  assert ((B + A) mod M < M) by (apply Nat.mod_upper_bound;lia).
  simpl. lia.
  rewrite plus_comm.
  assert ((A + B) mod M < A). apply eq2. lia.
  lia. lia.
  assert ((B + A) mod M < M) by (apply Nat.mod_upper_bound;lia).
  simpl. lia.
  rewrite mod_adder_half_sem with (B := B) (tenv := tenv); try easy.
  rewrite fbrev_twice_same. easy.
  apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
  apply mod_adder_half_well_typed; try easy.
  apply qft_uniform_exp_trans with (tenv := tenv); try easy.
  apply mod_adder_half_well_typed; try easy.
  apply qft_gt_exp_trans with (tenv := tenv); try easy.
  apply mod_adder_half_well_typed; try easy.
Qed.

Lemma phi_nor_mode_rz_modmult' : forall n size y x c aenv f A M, phi_modes f y size -> 
          nor_mode f c -> fst c <> y -> 0 < aenv y ->
       nor_mode (exp_sem aenv (rz_modmult' y x n size c A M) f) c
       /\ phi_modes (exp_sem aenv (rz_modmult' y x n size c A M) f) y size.
Proof.
  induction n; intros.
  simpl. split. easy. easy.
 Local Opaque mod_adder.
 simpl.
 Local Transparent mod_adder.
 specialize (IHn size y x c aenv f A M H H0 H1 H2).
 destruct (get_cua
      (exp_sem aenv (rz_modmult' y x n size c A M) f (x, size - S n))).
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
          exp_fresh aenv (y,m) (mod_adder x size c A M).
Proof.
  unfold mod_adder. intros.
  constructor. constructor.
  constructor. constructor.
  apply exp_fresh_rz_adder'. easy.
  apply exp_fresh_rz_sub'. easy.
  constructor. constructor. constructor. unfold or_not_eq. left. iner_p.
  Local Transparent CNOT.
  constructor. iner_p. constructor. destruct c. iner_p.
  Local Opaque CNOT.
  constructor. unfold or_not_eq. left. iner_p.
  constructor. destruct c. iner_p.
  apply exp_fresh_rz_adder'. easy.
  constructor. constructor.
  apply exp_fresh_rz_sub'. easy.
  constructor. constructor. constructor. unfold or_not_eq. left. iner_p.
  constructor. constructor. constructor. iner_p.
  Local Transparent CNOT.
  constructor. iner_p. constructor. destruct c. iner_p.
  Local Opaque CNOT.
  constructor. iner_p.
  constructor. unfold or_not_eq. left. iner_p.
  apply fresh_inv_exp.
  apply exp_fresh_rz_sub'. easy.
Qed.

Lemma pexp_fresh_mod_adder_ge : 
         forall m size x c A M aenv, fst c <> x -> aenv x = size -> 0 < size -> size <= m ->
          exp_fresh aenv (x,m) (mod_adder x size c A M).
Proof.
  unfold mod_adder. intros.
  constructor. constructor.
  constructor. constructor.
  apply exp_fresh_rz_adder'_ge; try lia.
  apply exp_fresh_rz_sub'_ge; try lia.
  constructor. constructor. constructor. unfold or_not_eq. right. rewrite H0. simpl. lia.
  Local Transparent CNOT.
  constructor. iner_p. constructor. destruct c. iner_p.
  Local Opaque CNOT.
  constructor. unfold or_not_eq. right. rewrite H0. simpl. lia.
  constructor. destruct c. iner_p.
  apply exp_fresh_rz_adder'_ge; try lia.
  constructor. constructor.
  apply exp_fresh_rz_sub'_ge; try lia.
  constructor. constructor.
  constructor. unfold or_not_eq. right. rewrite H0. simpl. lia.
  constructor. constructor. constructor. iner_p.
  Local Transparent CNOT.
  constructor. iner_p. constructor. destruct c. iner_p.
  Local Opaque CNOT.
  constructor. iner_p.
  constructor. unfold or_not_eq. right. rewrite H0. simpl. lia.
  apply fresh_inv_exp.
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
            exp_fresh aenv (x,m) (rz_modmult' y x n size c A M).
Proof.
  induction n;intros.
  simpl. constructor. iner_p.
  simpl. constructor.
  apply IHn; try lia.
  constructor. iner_p.
  apply pexp_fresh_mod_adder. lia. destruct c. iner_p.
Qed.

Lemma pexp_fresh_mod_mult_real: forall n m size x y z c A M aenv, n <= size 
             -> c <> (z,m) -> z <> x -> z <> y -> 
            exp_fresh aenv (z,m) (rz_modmult' y x n size c A M).
Proof.
  induction n;intros.
  simpl. constructor. iner_p.
  simpl. constructor.
  apply IHn; try lia. easy.
  constructor. iner_p.
  apply pexp_fresh_mod_adder. lia. easy.
Qed.


Lemma rz_modmult'_x_same: forall n m size x y c A M aenv f, n <= size ->
            fst c <> x -> fst c <> y -> x <> y -> 
             exp_sem aenv (rz_modmult' y x n size c A M) f (x,m) = f (x,m).
Proof.
  induction n;intros. simpl. easy.
  simpl. 
  destruct (get_cua (exp_sem aenv (rz_modmult' y x n size c A M) f (x, size - S n))).
  rewrite efresh_exp_sem_irrelevant.
  rewrite IHn; try easy. lia.
  apply pexp_fresh_mod_adder; try easy. lia.
  destruct c. iner_p.
  rewrite IHn; try easy. lia.
Qed.

Lemma pexp_fresh_mod_mult_ge: forall n m size x y c A M aenv, 0 < n -> n <= size <= m -> aenv y = size
             -> fst c <> x -> fst c <> y -> x <> y -> 
            exp_fresh aenv (y,m) (rz_modmult' y x n size c A M).
Proof.
  induction n;intros.
  simpl. constructor. iner_p.
  bdestruct (n =? 0). subst.
  simpl. constructor. constructor. iner_p.
  constructor. iner_p.
  apply pexp_fresh_mod_adder_ge; try easy.
  simpl. constructor.
  apply IHn; try lia.
  constructor. iner_p.
  apply pexp_fresh_mod_adder_ge; try easy. lia.
Qed.

Lemma exp_neu_rz_sub : forall n x y size M, n <= size -> exp_neu_l y [] (rz_sub' x n size M) [].
Proof.
 induction n;intros;simpl. constructor.
 apply seq_neul with (l' := []).
 apply IHn. lia.
 destruct (M n). constructor. constructor.
Qed.

Lemma rz_modmult'_well_typed : forall n size x y c A M aenv tenv, n <= size ->
          aenv y = size -> fst c <> x -> fst c <> y -> x <> y -> Env.MapsTo y (Phi (aenv y)) tenv
               -> Env.MapsTo x Nor tenv -> Env.MapsTo (fst c) Nor tenv
          -> well_typed_pexp aenv tenv (rz_modmult' y x n size c A M) tenv.
Proof.
 induction n; intros;simpl.
 constructor. constructor.
 apply pe_seq with (env' := tenv).
 apply IHn; try easy. lia.
 apply pcu_nor; try easy.
 apply pexp_fresh_mod_adder; try easy. lia. destruct c. iner_p.
 unfold exp_neu. intros.
 Local Transparent mod_adder mod_adder_half CNOT.
 unfold mod_adder,mod_adder_half.
 apply seq_neul with (l' := []).
 apply seq_neul with (l' := []).
 apply seq_neul with (l' := []).
 apply seq_neul with (l' := []).
 apply exp_neu_rz_adder; try easy.
 apply exp_neu_rz_sub; try easy.
 apply seq_neul with (l' := []).
 apply seq_neul with (l' := []).
 constructor. apply cu_neul. constructor.
 constructor. constructor.
 apply exp_neu_rz_adder; try easy.
 apply seq_neul with (l' := []).
 apply seq_neul with (l' := []).
 apply exp_neu_rz_sub; try easy.
 apply seq_neul with (l' := []).
 apply seq_neul with (l' := []).
 constructor.
 apply seq_neul with (l' := []).
 apply seq_neul with (l' := []).
 constructor.  constructor.  constructor.
 constructor. constructor.
 apply neu_l_inv_exp.
 unfold exp_neu_prop. intros.
 simpl in *.  lia.
 apply exp_neu_rz_sub; try easy.
 Local Opaque mod_adder mod_adder_half CNOT.
 apply mod_adder_well_typed; try easy.
Qed.
 
Lemma rz_modmult'_typed_sem : forall n size y f x c A B M X aenv tenv, n <= S size ->
          aenv y = S size -> fst c <> x -> fst c <> y -> x <> y -> 
          Env.MapsTo y (Phi (aenv y)) tenv -> Env.MapsTo x Nor tenv -> Env.MapsTo (fst c) Nor tenv ->
          get_cua (f c) = false -> snd c < aenv (fst c)
        -> 1 < M < 2^size -> A < M -> B < M -> X < 2^(S size) 
         -> fbrev (S size) (get_r_qft f y) = nat2fb B ->
        fbrev (S size) (get_cus (S size) f x) = nat2fb X
        -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
            (exp_sem aenv (rz_modmult' y x n (S size) c A M) f c) = f c
       /\ (get_r_qft (exp_sem aenv (rz_modmult' y x n (S size) c A M) f) y)
           = (fbrev (S size) (nat2fb (((B + (bindecomp n X) * A) mod M)))).
Proof.
  induction n; intros. simpl. split. easy.
 rewrite plus_0_r.
 rewrite Nat.mod_small by lia.
 rewrite <- H13.
 rewrite fbrev_twice_same. easy.
  Local Opaque mod_adder.
  simpl.
  Local Transparent mod_adder.
 rewrite bindecomp_seq.
 rewrite mult_plus_distr_r.
 rewrite efresh_exp_sem_irrelevant.
 assert ((get_cua (f (@pair var nat x (size - n)))) = nat2fb X n).
 rewrite <- get_cus_cua with (n := (S size)) by lia.
 rewrite <- H14.
 unfold fbrev.
 bdestruct (n <? S size). simpl.
 assert ((size - 0 - n) = size - n) by lia. rewrite H19. easy. lia.
 destruct (get_cua (f (@pair var nat x (size - n)))) eqn:eq1.
 rewrite mod_adder_sem with (B := (B + bindecomp n X * A) mod M) (tenv := tenv); try easy.
 rewrite mod_adder_typed with (B := (B + bindecomp n X * A) mod M) (tenv := tenv); try easy.
 rewrite <- H18. simpl.
 rewrite <- Nat.add_mod by lia.
 rewrite plus_0_r.
 rewrite plus_assoc.
 split.
 specialize (IHn size y f x c A B M X aenv tenv).
 assert (n <= S size) by lia.
 specialize (IHn H19 H0 H1 H2 H3 H4
        H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17).
 destruct IHn. 
 rewrite H20. easy. easy. 
 specialize (IHn size y f x c A B M X aenv tenv).
 assert (n <= S size) by lia.
 specialize (IHn H19 H0 H1 H2 H3 H4
        H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17).
 destruct IHn. 
 rewrite H20. easy.
 apply Nat.mod_upper_bound ; lia.
 apply Nat.mod_upper_bound ; lia.
 specialize (IHn size y f x c A B M X aenv tenv).
 assert (n <= S size) by lia.
 specialize (IHn H19 H0 H1 H2 H3 H4
        H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17).
 destruct IHn. 
 rewrite H21.
 rewrite fbrev_twice_same. easy.
 apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
 apply rz_modmult'_well_typed; try easy. lia.
 apply qft_uniform_exp_trans with (tenv := tenv); try easy.
 apply rz_modmult'_well_typed; try easy. lia.
 apply qft_gt_exp_trans with (tenv := tenv); try easy.
 apply rz_modmult'_well_typed; try easy. lia.
 specialize (IHn size y f x c A B M X aenv tenv).
 assert (n <= S size) by lia.
 specialize (IHn H19 H0 H1 H2 H3 H4
        H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17).
 destruct IHn. 
 rewrite H20. easy.
 apply Nat.mod_upper_bound ; lia.
 apply Nat.mod_upper_bound ; lia.
 specialize (IHn size y f x c A B M X aenv tenv).
 assert (n <= S size) by lia.
 specialize (IHn H19 H0 H1 H2 H3 H4
        H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17).
 destruct IHn. 
 rewrite H21.
 rewrite fbrev_twice_same. easy.
 apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
 apply rz_modmult'_well_typed; try easy. lia.
 apply qft_uniform_exp_trans with (tenv := tenv); try easy.
 apply rz_modmult'_well_typed; try easy. lia.
 apply qft_gt_exp_trans with (tenv := tenv); try easy.
 apply rz_modmult'_well_typed; try easy. lia.
 specialize (IHn size y f x c A B M X aenv tenv).
 assert (n <= S size) by lia.
 specialize (IHn H19 H0 H1 H2 H3 H4
        H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17).
 destruct IHn.
 split. 
 rewrite H20. easy.
 rewrite H21.
 rewrite <- H18. simpl.
 rewrite plus_0_r. easy.
 apply pexp_fresh_mod_mult; try lia. easy. easy.
Qed.

Opaque rz_modmult'.

Lemma rz_modmult_half_typed : forall size y f x c A B M X aenv tenv,
          aenv x = S size -> aenv y = S size -> fst c <> x -> fst c <> y -> x <> y -> 
          Env.MapsTo y Nor tenv -> Env.MapsTo x Nor tenv -> Env.MapsTo (fst c) Nor tenv ->
          get_cua (f c) = false -> snd c < aenv (fst c)
        -> 1 < M < 2^size -> A < M -> B < M -> X < 2^(S size) 
         -> fbrev (S size) (get_cus (S size) f y) = nat2fb B ->
        fbrev (S size) (get_cus (S size) f x) = nat2fb X
        -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
            (exp_sem aenv (rz_modmult_half y x (S size) c A M) f c) = f c.
Proof.
  intros.
  assert (S size <= S size) by lia.
  unfold rz_modmult_half in *.
  assert (exp_sem aenv ((QFT y; rz_modmult' y x (S size) (S size) c A M); RQFT y) f
    = exp_sem aenv (RQFT y) 
         (exp_sem aenv (rz_modmult' y x (S size) (S size) c A M)
              (exp_sem aenv (QFT y) f))).
  simpl. easy.
  rewrite H19. clear H19.
  specialize (rz_modmult'_typed_sem (S size) size y (exp_sem aenv (QFT y) f)
          x c A B M X aenv (Env.add y (Phi (aenv y)) tenv) H18 H0 H1 H2 H3) as eq1.
  assert (Env.MapsTo y (Phi (aenv y)) (Env.add y (Phi (aenv y)) tenv)).
  apply Env.add_1. easy.
  assert (Env.MapsTo x Nor (Env.add y (Phi (aenv y)) tenv)).
  apply Env.add_2. lia. easy.
  assert (Env.MapsTo (fst c) Nor (Env.add y (Phi (aenv y)) tenv)).
  apply Env.add_2. lia. easy.
  assert (get_cua (exp_sem aenv (QFT y) f c) = false).
  unfold get_cua.
  rewrite efresh_exp_sem_irrelevant.
  assert (nor_mode f c).
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  unfold nor_mode in H22.
  destruct (f c); easy. constructor. unfold or_not_eq. left. easy.
  rewrite efresh_exp_sem_irrelevant.
  assert (nor_modes f y (S size)).
  rewrite <- H0.
  apply type_nor_modes with (env := tenv); try easy.
  assert (fbrev (S size) (get_r_qft (exp_sem aenv (QFT y) f) y) = nat2fb B).
  simpl.
  unfold turn_qft.
  unfold get_r_qft. rewrite assign_r_lt by lia.
  rewrite lshift_fun_0.
  unfold up_qft.
  unfold nor_modes,nor_mode in H23.
  assert (0 < S size) by lia.
  specialize (H23 0 H24).
  destruct (f (@pair var nat y O)); try easy.
  rewrite H0. easy.
  assert (fbrev (S size) (get_cus (S size) (exp_sem aenv (QFT y) f) x) = nat2fb X).
  rewrite get_cus_qft_out. easy. easy.
  assert (right_mode_env aenv (Env.add y (Phi (aenv y)) tenv)
        (exp_sem aenv (QFT y) f) ).
  apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
  apply qft_nor. easy. easy.
  assert (qft_uniform aenv (Env.add y (Phi (aenv y)) tenv) (exp_sem aenv (QFT y) f)).
  apply qft_uniform_exp_trans with (tenv := tenv); try easy.
  apply qft_nor. easy. easy.
  assert (qft_gt aenv (Env.add y (Phi (aenv y)) tenv) (exp_sem aenv (QFT y) f)).
  apply qft_gt_exp_trans with (tenv := tenv); try easy.
  apply qft_nor. easy. easy.
  specialize (eq1 H19 H20 H21 H22 H8 H9 H10 H11 H12 H24 H25 H26 H27 H28).
  destruct eq1.
  rewrite H29.
  rewrite efresh_exp_sem_irrelevant. easy.
  constructor. unfold or_not_eq. left. easy.
  constructor. unfold or_not_eq. left. easy.
Qed.

Lemma rz_modmult_half_sem : forall size y f x c A B M X aenv tenv,
          aenv x = S size -> aenv y = S size -> fst c <> x -> fst c <> y -> x <> y -> 
          Env.MapsTo y Nor tenv -> Env.MapsTo x Nor tenv -> Env.MapsTo (fst c) Nor tenv ->
          get_cua (f c) = false -> snd c < aenv (fst c)
        -> 1 < M < 2^size -> A < M -> B < M -> X < 2^(S size) 
         -> fbrev (S size) (get_cus (S size) f y) = nat2fb B ->
        fbrev (S size) (get_cus (S size) f x) = nat2fb X
        -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
            get_cus (S size) (exp_sem aenv (rz_modmult_half y x (S size) c A M) f) y
                   = (fbrev (S size) (nat2fb (((B + X * A) mod M)))).
Proof.
  intros.
  assert (S size <= S size) by lia.
  unfold rz_modmult_half in *.
  assert (exp_sem aenv ((QFT y; rz_modmult' y x (S size) (S size) c A M); RQFT y) f
    = exp_sem aenv (RQFT y) 
         (exp_sem aenv (rz_modmult' y x (S size) (S size) c A M)
              (exp_sem aenv (QFT y) f))).
  simpl. easy.
  rewrite H19. clear H19.
  specialize (rz_modmult'_typed_sem (S size) size y (exp_sem aenv (QFT y) f)
          x c A B M X aenv (Env.add y (Phi (aenv y)) tenv) H18 H0 H1 H2 H3) as eq1.
  assert (Env.MapsTo y (Phi (aenv y)) (Env.add y (Phi (aenv y)) tenv)).
  apply Env.add_1. easy.
  assert (Env.MapsTo x Nor (Env.add y (Phi (aenv y)) tenv)).
  apply Env.add_2. lia. easy.
  assert (Env.MapsTo (fst c) Nor (Env.add y (Phi (aenv y)) tenv)).
  apply Env.add_2. lia. easy.
  assert (get_cua (exp_sem aenv (QFT y) f c) = false).
  unfold get_cua.
  rewrite efresh_exp_sem_irrelevant.
  assert (nor_mode f c).
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  unfold nor_mode in H22.
  destruct (f c); easy. constructor. unfold or_not_eq. left. easy.
  assert (nor_modes f y (S size)).
  rewrite <- H0.
  apply type_nor_modes with (env := tenv); try easy.
  assert (fbrev (S size) (get_r_qft (exp_sem aenv (QFT y) f) y) = nat2fb B).
  simpl.
  unfold turn_qft.
  unfold get_r_qft. rewrite assign_r_lt by lia.
  rewrite lshift_fun_0.
  unfold up_qft.
  unfold nor_modes,nor_mode in H23.
  assert (0 < S size) by lia.
  specialize (H23 0 H24).
  destruct (f (@pair var nat y O)); try easy.
  rewrite H0. easy.
  assert (fbrev (S size) (get_cus (S size) (exp_sem aenv (QFT y) f) x) = nat2fb X).
  rewrite get_cus_qft_out. easy. easy.
  assert (right_mode_env aenv (Env.add y (Phi (aenv y)) tenv)
        (exp_sem aenv (QFT y) f) ).
  apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
  apply qft_nor. easy. easy.
  assert (qft_uniform aenv (Env.add y (Phi (aenv y)) tenv) (exp_sem aenv (QFT y) f)).
  apply qft_uniform_exp_trans with (tenv := tenv); try easy.
  apply qft_nor. easy. easy.
  assert (qft_gt aenv (Env.add y (Phi (aenv y)) tenv) (exp_sem aenv (QFT y) f)).
  apply qft_gt_exp_trans with (tenv := tenv); try easy.
  apply qft_nor. easy. easy.
  specialize (eq1 H19 H20 H21 H22 H8 H9 H10 H11 H12 H24 H25 H26 H27 H28).
  destruct eq1.
  remember ((exp_sem aenv (rz_modmult' y x 
         (S size) (S size) c A M) (exp_sem aenv (QFT y) f))) as g.
  simpl.
  unfold turn_rqft. rewrite H0.
  rewrite get_cus_assign_seq.
  rewrite H30.
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
             exp_sem aenv (rz_modmult_half y x size c A M) f (x,m) = f (x,m).
Proof.
  intros. unfold rz_modmult_half. simpl.
  unfold turn_rqft.
  rewrite assign_seq_out by iner_p.
  rewrite rz_modmult'_x_same; try easy.
  unfold turn_qft.
  rewrite assign_r_out by iner_p. easy.
Qed.

Lemma rz_adder_r : forall n size i x M aenv tenv f, n <= size -> i < size -> aenv x = size
       -> Env.MapsTo x (Phi (aenv x)) tenv -> right_mode_env aenv tenv f ->
      get_r (exp_sem aenv (rz_adder' x n size M) f (x,i)) = get_r (f (x,i)).
Proof.
 induction n; intros; simpl.
 easy.
 assert (phi_modes (exp_sem aenv (rz_adder' x n size M) f) x size).
 apply rz_adder_phi_modes with (tenv := tenv); try easy.
 lia.
 destruct (M n). simpl.
 rewrite <- (IHn size i x M aenv tenv f); try easy.
 unfold get_r.
 unfold sr_rotate.
 bdestruct (i <? (S (size - S n))).
 rewrite sr_rotate'_lt_1; try lia.
 unfold phi_modes in H4.
 apply H4 in H0. unfold phi_mode in H0.
 unfold times_rotate.
 destruct (exp_sem aenv (rz_adder' x n size M) f (@pair var nat x i)) eqn:eq1. easy. easy.
 assert ( (@pair Env.key nat x i)  =  (@pair var nat x i)) by easy.
 rewrite H6 in *. rewrite eq1. easy.
 rewrite sr_rotate'_ge. 
 apply H4 in H0. unfold phi_mode in H0.
 unfold times_rotate.
 destruct (exp_sem aenv (rz_adder' x n size M) f (@pair var nat x i)) eqn:eq1. easy. easy.
 assert ( (@pair Env.key nat x i)  =  (@pair var nat x i)) by easy.
 rewrite H6 in *. rewrite eq1. easy. simpl. lia. lia.
 simpl.
 rewrite IHn with (tenv := tenv); try easy.
 lia.
Qed.

Lemma rz_sub_r : forall n size i x M aenv tenv f, n <= size -> i < size -> aenv x = size
       -> Env.MapsTo x (Phi (aenv x)) tenv -> right_mode_env aenv tenv f ->
      get_r (exp_sem aenv (rz_sub' x n size M) f (x,i)) = get_r (f (x,i)).
Proof.
 induction n; intros; simpl.
 easy.
 assert (phi_modes (exp_sem aenv (rz_sub' x n size M) f) x size).
 apply rz_sub_phi_modes with (tenv := tenv); try easy.
 lia.
 destruct (M n). simpl.
 rewrite <- (IHn size i x M aenv tenv f); try easy.
 unfold get_r.
 unfold srr_rotate.
 bdestruct (i <? (S (size - S n))).
 rewrite srr_rotate'_lt_1; try lia.
 unfold phi_modes in H4.
 apply H4 in H0. unfold phi_mode in H0.
 unfold times_r_rotate.
 destruct (exp_sem aenv (rz_sub' x n size M) f (@pair var nat x i)) eqn:eq1. easy. easy.
 assert ( (@pair Env.key nat x i)  =  (@pair var nat x i)) by easy.
 rewrite H6 in *. rewrite eq1. easy.
 rewrite srr_rotate'_ge. 
 apply H4 in H0. unfold phi_mode in H0.
 unfold times_rotate.
 destruct (exp_sem aenv (rz_sub' x n size M) f (@pair var nat x i)) eqn:eq1. easy. easy.
 assert ( (@pair Env.key nat x i)  =  (@pair var nat x i)) by easy.
 rewrite H6 in *. rewrite eq1. easy. simpl. lia. lia.
 simpl.
 rewrite IHn with (tenv := tenv); try easy.
 lia.
Qed.

Lemma rz_sub_inv_r : forall n size i x M aenv tenv f, n <= size -> i < size -> aenv x = size
       -> Env.MapsTo x (Phi (aenv x)) tenv -> right_mode_env aenv tenv f ->
      get_r (exp_sem aenv (inv_exp (rz_sub' x n size M)) f (x,i)) = get_r (f (x,i)).
Proof.
 induction n; intros; simpl.
 easy.
 assert (phi_modes (exp_sem aenv (inv_exp (rz_sub' x n size M)) f) x size).
 apply phi_modes_exp.
 apply exp_scope_inv_exp. apply escope_rz_sub.
 assert (phi_modes f x size).
 rewrite <- H1.
 apply type_phi_modes with (env := tenv).
 easy. easy. easy.
 destruct (M n). simpl.
 rewrite IHn with (tenv := tenv); try easy.
 unfold get_r.
 unfold sr_rotate.
 bdestruct (i <? (S (size - S n))).
 rewrite sr_rotate'_lt_1; try lia.
 unfold times_rotate.
 assert (phi_modes f x size).
 rewrite <- H1.
 apply type_phi_modes with (env := tenv). easy. easy.
 unfold phi_modes in H6. apply H6 in H0. unfold phi_mode in H0.
 destruct (f (@pair var nat x i)) eqn:eq1. easy. easy.
 assert ( (@pair Env.key nat x i)  =  (@pair var nat x i)) by easy.
 rewrite H7 in *. rewrite eq1. easy.
 rewrite sr_rotate'_ge. easy. simpl. lia. lia. 
 assert (right_mode_env aenv tenv (exp_sem aenv (SR (size - S n) x) f)).
 apply well_typed_right_mode_pexp with (tenv := tenv).
 constructor. apply sr_phi with (n := aenv x). easy. lia. easy.
 simpl in H5. easy.
 simpl. rewrite IHn with (tenv := tenv); try easy. lia.
Qed.

Lemma one_cu_adder_r : forall size i x c M aenv tenv f, i < size -> aenv x = size
      -> snd c < aenv (fst c)-> Env.MapsTo x (Phi (aenv x)) tenv 
      -> Env.MapsTo (fst c) Nor tenv -> right_mode_env aenv tenv f ->
      get_r (exp_sem aenv (one_cu_adder x size c M) f (x,i)) = get_r (f (x,i)).
Proof.
 intros. simpl.
 assert (nor_mode f c).
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 destruct (f c) eqn:eq1.
 unfold get_cua. destruct b.
 apply rz_adder_r with (tenv := tenv); try easy. easy.
 easy. easy.
Qed.

Lemma rqft_r : forall i size x aenv tenv f, i < size -> aenv x = size -> 
          Env.MapsTo x (Phi (aenv x)) tenv -> right_mode_env aenv tenv f ->
          get_r (exp_sem aenv (RQFT x) f (x,i)) = get_r (f (x,i)).
Proof.
  intros; simpl.
  unfold turn_rqft.
  rewrite assign_seq_lt; try lia.
  assert (phi_modes f x size).
  rewrite <- H0.
  apply type_phi_modes with (env := tenv); try easy.
  unfold phi_modes in H3.
  apply H3 in H. unfold phi_mode in H.
  destruct (f (@pair var nat x i)) eqn:eq1. easy. easy.
  unfold get_r.
  assert ( (@pair Env.key nat x i)  =  (@pair var nat x i)) by easy. 
  rewrite H4 in *. rewrite eq1. easy.
Qed.

Lemma qft_r : forall i size x aenv tenv f, i < size -> aenv x = size -> 
          Env.MapsTo x Nor tenv -> right_mode_env aenv tenv f ->
          get_r (exp_sem aenv (QFT x) f (x,i)) = get_r (f (x,i)).
Proof.
  intros; simpl.
  unfold turn_qft.
  rewrite assign_r_lt; try lia. unfold up_qft.
  assert (nor_modes f x size).
  rewrite <- H0.
  apply type_nor_modes with (env := tenv); try easy.
  unfold nor_modes in H3.
  apply H3 in H. unfold nor_mode in H.
  destruct (f (@pair var nat x i)) eqn:eq1. 
  unfold get_r.
  assert ( (@pair Env.key nat x i)  =  (@pair var nat x i)) by easy. 
  rewrite H4 in *. rewrite eq1. easy. easy. easy.
Qed.

Lemma cnot_r : forall p1 p2 p3 aenv tenv f, p1 <> p2 -> p2 <> p3 -> snd p1 < aenv (fst p1) ->
          Env.MapsTo (fst p1) Nor tenv -> right_mode_env aenv tenv f ->
          get_r (exp_sem aenv (CNOT p1 p2) f p3) = get_r (f p3).
Proof.
  Local Transparent CNOT.
  intros; simpl.
  Local Opaque CNOT.
  assert (nor_mode f p1).
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  unfold nor_mode in H4.
  destruct (f p1).
  unfold get_cua.
  destruct b.
  rewrite eupdate_index_neq. easy. easy. easy. easy. easy.
Qed.

Lemma x_r : forall p1 p3 aenv tenv f, snd p1 < aenv (fst p1) ->
          Env.MapsTo (fst p1) Nor tenv -> right_mode_env aenv tenv f ->
          get_r (exp_sem aenv (X p1) f p3) = get_r (f p3).
Proof.
  intros; simpl.
  bdestruct (p1 ==? p3). subst.
  rewrite eupdate_index_eq.
  unfold exchange.
  unfold get_r.
  assert (nor_mode f p3).
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  unfold nor_mode in H2.
  destruct (f p3). easy. easy. easy.
  rewrite eupdate_index_neq. easy. easy.
Qed.

Lemma qft_cu_r : forall i size x c aenv tenv f, i < size -> aenv x = size ->
      fst c <> x -> snd c < aenv (fst c)-> Env.MapsTo x (Phi (aenv x)) tenv 
      -> Env.MapsTo (fst c) Nor tenv -> right_mode_env aenv tenv f ->
      get_r (exp_sem aenv (qft_cu x c) f (x,i)) = get_r (f (x,i)).
Proof.
  intros.
  unfold qft_cu.
  assert ((exp_sem aenv ((RQFT x; CNOT (@pair var nat x 0) c); QFT x) f)
    = exp_sem aenv (QFT x) 
       (exp_sem aenv (CNOT (@pair var nat x 0) c) (exp_sem aenv (RQFT x) f))).
  simpl. easy.
  rewrite H6.
  rewrite qft_r with (size := size) (tenv := Env.add x Nor tenv); try easy.
  rewrite cnot_r with (tenv := Env.add x Nor tenv); try easy.
  rewrite rqft_r with (size := size) (tenv := tenv); try easy.
  destruct c. iner_p.
  destruct c. iner_p. simpl. lia.
  simpl. apply Env.add_1. easy.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply rqft_phi. easy. easy. easy.
  apply Env.add_1. easy.
  apply well_typed_right_mode_pexp with (tenv := (Env.add x Nor tenv)).
  apply cnot_wt_nor. destruct c. iner_p.
  simpl. apply Env.add_1. easy.
  apply Env.add_2. iner_p. easy.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply rqft_phi. easy. easy. easy.
Qed.

Lemma qft_acu_r : forall i size x c aenv tenv f, i < size -> aenv x = size ->
      fst c <> x -> snd c < aenv (fst c)-> Env.MapsTo x (Phi (aenv x)) tenv 
      -> Env.MapsTo (fst c) Nor tenv -> right_mode_env aenv tenv f ->
      get_r (exp_sem aenv (qft_acu x c) f (x,i)) = get_r (f (x,i)).
Proof.
  intros.
  unfold qft_acu.
  assert ((exp_sem aenv ((RQFT x; ((X (@pair var nat x 0); CNOT (@pair var nat x 0) c); X (@pair var nat x 0))); QFT x) f)
    = exp_sem aenv (QFT x) (exp_sem aenv (X (@pair var nat x 0))
       (exp_sem aenv (CNOT (@pair var nat x 0) c)
             (exp_sem aenv (X (@pair var nat x 0)) (exp_sem aenv (RQFT x) f))))).
  simpl. easy.
  rewrite H6.
  rewrite qft_r with (size := size) (tenv := Env.add x Nor tenv); try easy.
  rewrite x_r with (tenv := Env.add x Nor tenv); try easy.
  rewrite cnot_r with (tenv := Env.add x Nor tenv); try easy.
  rewrite x_r with (tenv := Env.add x Nor tenv); try easy.
  rewrite rqft_r with (size := size) (tenv := tenv); try easy.
  simpl. lia. simpl. apply Env.add_1. easy.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply rqft_phi. easy. easy. easy. destruct c. iner_p.
  destruct c. iner_p.
  simpl. lia. simpl. apply Env.add_1. easy.
  apply well_typed_right_mode_pexp with (tenv := (Env.add x Nor tenv)).
  constructor. constructor. simpl. apply Env.add_1. easy.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply rqft_phi. easy. easy. easy.
  simpl. lia. simpl. apply Env.add_1. easy.
  apply well_typed_right_mode_pexp with (tenv := (Env.add x Nor tenv)).
  apply cnot_wt_nor. destruct c. iner_p.
  simpl. apply Env.add_1. easy.
  apply Env.add_2. iner_p. easy.
  apply well_typed_right_mode_pexp with (tenv := (Env.add x Nor tenv)).
  constructor. constructor.
  simpl. apply Env.add_1. easy.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply rqft_phi. easy. easy. easy.
  apply Env.add_1. easy.
  apply well_typed_right_mode_pexp with (tenv := (Env.add x Nor tenv)).
  constructor. constructor.
  simpl. apply Env.add_1. easy.
  apply well_typed_right_mode_pexp with (tenv := (Env.add x Nor tenv)).
  apply cnot_wt_nor. destruct c. iner_p.
  simpl. apply Env.add_1. easy.
  apply Env.add_2. iner_p. easy.
  apply well_typed_right_mode_pexp with (tenv := (Env.add x Nor tenv)).
  constructor. constructor.
  simpl. apply Env.add_1. easy.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply rqft_phi. easy. easy. easy.
Qed.


Lemma mod_adder_half_r : forall size i x c A M aenv tenv f, i < size
      -> aenv x = size -> snd c < aenv (fst c) ->
        fst c <> x -> Env.MapsTo x (Phi (aenv x)) tenv
       -> Env.MapsTo (fst c) Nor tenv -> right_mode_env aenv tenv f ->
      get_r (exp_sem aenv (mod_adder_half x size c A M) f (x,i)) = get_r (f (x,i)).
Proof.
 intros.
 Local Transparent mod_adder_half. unfold mod_adder_half.
 Local Opaque rz_adder rz_sub qft_cu one_cu_adder.
 simpl. rewrite one_cu_adder_r with (tenv := tenv) ; try easy.
 rewrite qft_cu_r with (size := size) (tenv := tenv); try easy.
 Local Transparent rz_sub rz_adder qft_cu.
 unfold rz_sub.
 rewrite rz_sub_r with (tenv := tenv); try easy.
 unfold rz_adder.
 rewrite rz_adder_r with (tenv := tenv); try easy.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply rz_adder_well_typed; try easy. easy.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply rz_sub_well_typed; try easy.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply rz_adder_well_typed; try easy. easy.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply pe_seq with (env' := Env.add x Nor tenv).
  apply pe_seq with (env' := Env.add x Nor tenv).
  apply rqft_phi; try easy.
  apply cnot_wt_nor. destruct c. iner_p. simpl. apply Env.add_1. easy.
  apply Env.add_2. iner_p. easy.
  apply qft_nor. apply Env.add_1. easy.
 apply EnvFacts.Equal_mapsto_iff.
 intros. split. intros.
 bdestruct (k =? x). subst.
 apply mapsto_always_same with (v2 := e) in H3. subst.
 apply Env.add_1. easy. easy.
 apply Env.add_2. lia. apply Env.add_2. lia. easy.
 intros.
 bdestruct (k =? x). subst. 
 apply mapsto_add1 in H6. subst. easy.
 apply Env.add_3 in H6. apply Env.add_3 in H6. easy. lia. lia.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply rz_sub_well_typed; try easy.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply rz_adder_well_typed; try easy. easy.
 Local Opaque rz_sub rz_adder qft_cu mod_adder_half one_cu_adder.
Qed.

Lemma clean_hbit_r : forall size i x c M aenv tenv f, i < size
      -> aenv x = size -> snd c < aenv (fst c) ->
        fst c <> x -> Env.MapsTo x (Phi (aenv x)) tenv
       -> Env.MapsTo (fst c) Nor tenv -> right_mode_env aenv tenv f ->
      get_r (exp_sem aenv (clean_hbit x size c M) f (x,i)) = get_r (f (x,i)).
Proof.
  intros. unfold clean_hbit.
  assert ( exp_sem aenv ((rz_sub x size M; qft_acu x c); inv_exp (rz_sub x size M)) f
    = exp_sem aenv (inv_exp (rz_sub x size M)) (exp_sem aenv (qft_acu x c)
            (exp_sem aenv ((rz_sub x size M)) f))).
  simpl. easy.
  rewrite H6. clear H6.
  Local Transparent rz_sub. 
  unfold rz_sub.
  rewrite rz_sub_inv_r with (tenv := tenv); try easy.
  rewrite qft_acu_r with (size := size) (tenv := tenv); try easy.
  rewrite rz_sub_r with (tenv := tenv); try easy.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply rz_sub_well_typed; try easy. easy.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  unfold qft_acu.
 apply pe_seq with (env' := Env.add x Nor tenv).
 apply pe_seq with (env' := Env.add x Nor tenv).
 apply rqft_phi. easy. easy.
 apply pe_seq with (env' := Env.add x Nor tenv).
 apply pe_seq with (env' := Env.add x Nor tenv).
 constructor. constructor. simpl. apply Env.add_1. easy.
 apply cnot_wt_nor. destruct c. iner_p.
 simpl. apply Env.add_1. easy.
 apply Env.add_2. iner_p. easy.
 constructor. constructor. simpl. apply Env.add_1. easy.
 apply qft_nor. apply Env.add_1. easy.
 apply EnvFacts.Equal_mapsto_iff.
 intros. split. intros.
 bdestruct (k =? x). subst.
 apply mapsto_always_same with (v2 := e) in H3. subst.
 apply Env.add_1. easy. easy.
 apply Env.add_2. lia. apply Env.add_2. lia. easy.
 intros.
 bdestruct (k =? x). subst. 
 apply mapsto_add1 in H6. subst. easy.
 apply Env.add_3 in H6. apply Env.add_3 in H6. easy. lia. lia.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply rz_sub_well_typed; try easy. easy.
  Local Opaque rz_sub.
Qed.

Lemma rz_modmult'_r: forall n size i  y x c A M aenv tenv f, n <= size -> i < size
      -> aenv x = size -> aenv y = size -> snd c < aenv (fst c) ->
        fst c <> x -> y <> x -> fst c <> y -> Env.MapsTo y (Phi (aenv y)) tenv
       -> Env.MapsTo x Nor tenv -> Env.MapsTo (fst c) Nor tenv -> right_mode_env aenv tenv f ->
      get_r (exp_sem aenv (rz_modmult' y x n size c A M) f (y,i)) = get_r (f (y,i)).
Proof.
  Local Transparent rz_modmult'.
  Local Opaque mod_adder_half clean_hbit.
  induction n; intros. simpl. easy.
  simpl.
  destruct (get_cua
       (exp_sem aenv (rz_modmult' y x n size c A M) f
          (@pair var nat x (size - S n)))) eqn:eq1.
  simpl.
  rewrite clean_hbit_r with (tenv := tenv); try easy.
  rewrite mod_adder_half_r with (tenv := tenv); try easy.
  rewrite IHn with (tenv := tenv); try easy.
  lia.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply rz_modmult'_well_typed; try easy. lia. lia. easy.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply mod_adder_half_well_typed; try easy.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply rz_modmult'_well_typed; try easy. lia. lia. easy.
  rewrite IHn with (tenv := tenv); try easy.
  lia.
  Local Opaque rz_modmult'.
Qed.

Lemma rz_modmult_half_r : forall i size y x c A M aenv tenv f, i < size
      -> aenv x = size -> aenv y = size -> snd c < aenv (fst c) ->
        fst c <> x -> y <> x -> fst c <> y -> Env.MapsTo y Nor tenv
       -> Env.MapsTo x Nor tenv -> Env.MapsTo (fst c) Nor tenv -> right_mode_env aenv tenv f ->
            get_r ((exp_sem aenv 
                 (rz_modmult_half y x (size) c A M) f) (y,i)) = get_r (f (y,i)).
Proof.
  intros.
  unfold rz_modmult_half in *.
  assert ((exp_sem aenv ((QFT y; rz_modmult' y x size size c A M); RQFT y) f)
      = exp_sem aenv (RQFT y) (exp_sem aenv (rz_modmult' y x size size c A M) (exp_sem aenv (QFT y) f))).
  simpl. easy.
  rewrite H10. clear H10.
  rewrite rqft_r with (size := size) (tenv := Env.add y (Phi (aenv y)) tenv); try easy.
  rewrite rz_modmult'_r with (tenv := Env.add y  (Phi (aenv y)) tenv); try easy.
  rewrite qft_r with (size := size) (tenv := tenv); try easy.
  apply Env.add_1. easy.
  apply Env.add_2. easy. easy.
  apply Env.add_2. iner_p. easy.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply qft_nor. easy. easy. easy.
  apply Env.add_1. easy.
  apply well_typed_right_mode_pexp with (tenv := (Env.add y (Phi (aenv y)) tenv)).
  apply rz_modmult'_well_typed; try easy. lia.
  apply Env.add_1. easy.
  apply Env.add_2. easy. easy.
  apply Env.add_2. iner_p. easy.
  apply well_typed_right_mode_pexp with (tenv := tenv).
  apply qft_nor. easy. easy. easy.
Qed.

Lemma rz_modmult_half_x_cus: forall size y c A M aenv f x,
            fst c <> x -> fst c <> y -> x <> y -> 
          get_cus size (exp_sem aenv 
             (rz_modmult_half y x size c A M) f) x = get_cus size f x.
Proof.
  intros. unfold get_cus.
  apply functional_extensionality; intros.
  bdestruct (x0 <? size).
  rewrite rz_modmult_half_x_same; try easy. easy.
Qed.

Lemma rz_modmult_half_sem_1 : forall size y f x c A B M X aenv tenv,
          aenv x = S size -> aenv y = S size -> fst c <> x -> fst c <> y -> x <> y -> 
          Env.MapsTo y Nor tenv -> Env.MapsTo x Nor tenv -> Env.MapsTo (fst c) Nor tenv ->
          get_cua (f c) = false -> snd c < aenv (fst c)
        -> 1 < M < 2^size -> A < M -> B < M -> X < 2^(S size) 
         -> fbrev (S size) (get_cus (S size) f y) = nat2fb B ->
        fbrev (S size) (get_cus (S size) f x) = nat2fb X
        -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
           (exp_sem aenv (rz_modmult_half y x (S size) c A M) f)
                   = put_cus f y (fbrev (S size) (nat2fb (((B + X * A) mod M)))) (S size).
Proof.
  intros.
  rewrite <- (rz_modmult_half_sem size y f x c A B M X aenv tenv); try easy.
  apply functional_extensionality; intros.
  destruct x0.
  bdestruct (v =? y). subst.
  bdestruct (n <? S size). 
  rewrite put_cus_eq by lia.
  rewrite get_cus_cua by lia.
  assert (nor_modes f y (S size)) as X1.
  rewrite <- H0.
  apply type_nor_modes with (env := tenv); try easy.
  assert (nor_modes f x (S size)) as X2.
  rewrite <- H.
  apply type_nor_modes with (env := tenv); try easy.
  assert (nor_modes (exp_sem aenv (rz_modmult_half y x (S size) c A M) f) y (S size)).
  unfold rz_modmult_half.
  simpl.
  unfold turn_rqft.
  unfold nor_modes.
  intros.
  unfold nor_mode.
  rewrite assign_seq_lt;try lia.
  unfold nor_modes,nor_mode in H1.
  specialize (X1 n H18) as eq1. unfold nor_mode in eq1.
  unfold put_cu.
  destruct (f (@pair var nat y n)) eqn:eq2.
  assert (get_r (exp_sem aenv (rz_modmult_half y x (S size) c A M) f (@pair var nat y n)) = r).
  rewrite rz_modmult_half_r with (tenv := tenv); try easy.
  assert ( (@pair Env.key nat y n)  =  (@pair var nat y n)) by easy.
  rewrite H20 in *.
  rewrite eq2. unfold get_r. easy. lia.
  unfold nor_modes in H19. apply H19 in H18. unfold nor_mode in H18.
  destruct (exp_sem aenv (rz_modmult_half y x (S size) c A M) f (@pair var nat y n)).
  unfold get_cua. unfold get_r in H20. subst. easy. lia. lia. lia. lia.
  rewrite put_cus_neq_2; try lia.
  rewrite efresh_exp_sem_irrelevant; try easy.
  unfold rz_modmult_half.
  constructor. constructor.
  constructor. unfold or_not_eq. right. rewrite H0. simpl. lia.
  apply pexp_fresh_mod_mult_ge; try lia. easy. easy.
  constructor. unfold or_not_eq. right. rewrite H0. simpl. lia.
  rewrite put_cus_neq; try lia.
  bdestruct (v =? x). subst.
  rewrite rz_modmult_half_x_same; try lia. easy. easy. easy.
  bdestruct (c ==? (v,n)). subst.
  rewrite rz_modmult_half_typed with (B := B) (X := X) (tenv:=tenv); try easy.
  rewrite efresh_exp_sem_irrelevant; try easy.
  unfold rz_modmult_half.
  constructor. constructor.
  constructor. unfold or_not_eq. left. simpl. easy.
  apply pexp_fresh_mod_mult_real; try lia. easy.
  constructor. unfold or_not_eq. left. simpl. easy.
Qed.

Opaque rz_modmult_half.

Lemma rz_modmult_full_sem : forall size y f x c A Ainv M X aenv tenv ,
          aenv x = S size -> aenv y = S size -> fst c <> x -> fst c <> y -> x <> y -> 
          Env.MapsTo y Nor tenv -> Env.MapsTo x Nor tenv -> Env.MapsTo (fst c) Nor tenv ->
          get_cua (f c) = false -> snd c < aenv (fst c)
        -> 1 < M < 2^size -> A < M -> Ainv < M -> X < M -> A * Ainv mod M = 1
         -> fbrev (S size) (get_cus (S size) f y) = nat2fb 0 ->
            fbrev (S size) (get_cus (S size) f x) = nat2fb X
        -> right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
            (exp_sem aenv (rz_modmult_full y x (S size) c A Ainv M) f)
                   = put_cus (put_cus f y (fbrev (S size) (nat2fb (((X * A) mod M)))) (S size)) 
                                    x (fbrev (S size) (nat2fb 0)) (S size).
Proof.
  intros. simpl.
  assert (nor_modes f y (S size)) as X1.
  rewrite <- H0. apply type_nor_modes with (env := tenv). easy. easy.
  assert (nor_modes f x (S size)) as X2.
  rewrite <- H. apply type_nor_modes with (env := tenv). easy. easy.
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv); try easy.
  Local Transparent rz_modmult_half.
  unfold rz_modmult_half.
  apply pe_seq with (env' := Env.add x (Phi (aenv x)) tenv). 
  apply pe_seq with (env' := Env.add x (Phi (aenv x)) tenv). 
  apply qft_nor. easy. easy.
  apply rz_modmult'_well_typed; try easy. lia.
  apply Env.add_1. easy.
  apply Env.add_2. lia. easy.
  apply Env.add_2. iner_p. easy.
  apply rqft_phi.
  apply Env.add_1. easy.
 apply EnvFacts.Equal_mapsto_iff.
 intros. split. intros.
 bdestruct (k =? x). subst.
 apply mapsto_always_same with (v2 := e) in H5. subst.
 apply Env.add_1. easy. easy.
 apply Env.add_2. lia. apply Env.add_2. lia. easy.
 intros.
 bdestruct (k =? x). subst. 
 apply mapsto_add1 in H19. subst. easy.
 apply Env.add_3 in H19. apply Env.add_3 in H19. easy. lia. lia.
  Local Opaque rz_modmult_half.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same. easy.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cus_same. easy. easy.
  apply right_mode_exp_put_cus_same. easy.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cus_same. easy.
  easy.
  unfold nor_modes in *. intros.
  nor_mode_simpl. apply X2; lia.
  rewrite rz_modmult_half_sem_1 with (y := y) (x:= x) (tenv:=tenv) (B:=0) (X := X); try easy.
  rewrite rz_modmult_half_sem_1 with (y := x) (x:= y) (tenv:=tenv) (B:=0) (X := ((X * A) mod M)).
  rewrite put_cus_twice_eq.
  rewrite plus_0_l.
  rewrite plus_0_l.
  rewrite Nat.mul_mod_idemp_l by lia.
  rewrite <- Nat.mul_assoc.
  rewrite (Nat.mul_mod X (A * Ainv)) by lia.
  rewrite H13.
  rewrite Nat.mul_1_r.
  rewrite Nat.mod_mod by lia.
  rewrite (Nat.mod_small X) by easy.
  apply put_cus_same.
  unfold nor_modes; intros.
  nor_mode_simpl. apply X2. easy.
  rewrite get_cus_put_neq by lia.
  rewrite <- H15.
  rewrite fbrev_twice_same. easy.
  1-4:easy. lia. 1-3:easy.
  destruct c.
  rewrite cus_get_neq by iner_p.
  rewrite cus_get_neq by iner_p. easy. 1-3:easy. lia.
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
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same. easy.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cus_same. easy. easy.
  apply right_mode_exp_put_cus_same. easy.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cus_same. easy. easy.
  unfold nor_modes; intros.
  nor_mode_simpl. apply X2. easy. lia. simpl. lia.
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
   (Rev x; Rev re) ; QFT re ; nat_mult' size size x re M;
  RQFT re; inv_exp ( (Rev x; Rev re)).

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
   (Rev x; Rev re) ; flt_mult' size size x re M; inv_exp ( (Rev x; Rev re)).

(* Implementing x * y multiplier for nats values. *)
(* y is in nor_mode, and y is in phi, [y][x] -> [y][x+y] *)
Fixpoint rz_full_adder_i (size:nat) (re:var) (y:var) (n:nat) (i:nat) :=
  match n with
  | 0 => (SKIP (re,0))
  | S m => (rz_full_adder_i size re y m i; (CU (y,m) (SR (size - n - i) re)))
  end.
Definition one_cu_full_adder_i (c:posi) (re:var) (y:var) (size n i : nat) := 
  CU c (rz_full_adder_i size re y n i).

(* Here x and y are in nor_mode and re in phi_mode. 
  [x][y][phi(re)] ->[x][y][phi(x*y)], re is supposed to be zero *)
Fixpoint nat_full_mult' (n:nat) (size:nat) (x:var) (y:var) (re:var) :=
   match n with 0 => SKIP (re,0)
            | S m => nat_full_mult' m size x y re;
                 one_cu_full_adder_i (x,size - n) re y size (size-m) m
   end.

(* Here x and y are in nor_mode and re in phi_mode. 
   [x][y][phi(re)] ->[x][y][phi(x*y mod 2^n)], re is supposed to be zero, 
   ex is in nor_mode. *)
Definition nat_full_mult (size:nat) (x y:var) (re:var) :=
   (Rev re ; Rev x); QFT re ;
   (nat_full_mult' size size x y re) ;
  RQFT re ;  (Rev re; Rev x).

Definition vars_for_rz_nat_full_m (size:nat) := 
  gen_vars size (x_var::y_var::z_var::[]).

Definition nat_full_mult_out (size:nat) := nat_full_mult size x_var y_var z_var.


(* Implementing x + y addition for fixedp values. *)
Fixpoint rz_full_adder' (x:var) (n:nat) (size:nat) (y:var) :=
  match n with
  | 0 => (SKIP (x,0))
  | S m => ((CU (y,m) (SR (size - n) x)); rz_full_adder' x m size y)
  end.
Definition rz_full_adder (x:var) (n:nat) (y:var) := rz_full_adder' x n n y.

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
   (Rev re; Rev x; Rev y); QFT re ;
   (flt_full_mult_quar size x y re ex ; inv_exp (clean_high_flt size size y ex)) ;
  RQFT re ;( (Rev re; Rev x; Rev y)).

(* Implementing x < M comparator. *)
Definition rz_comparator (x:var) (n:nat) (c:posi) (M:nat) := 
   (Rev x); QFT x;  (rz_sub x n (nat2fb M)); RQFT x ; (CNOT (x,0) c);
  inv_exp ( (Rev x); QFT x; (rz_sub x n (nat2fb M)); RQFT x).


(* Implementing x + y / X + M addition. *)
Lemma xfactor_well_typed : forall x aenv tenv,
      Env.MapsTo x Nor tenv -> well_typed_pexp aenv tenv (Rev x; QFT x) (Env.add x (Phi (aenv x)) tenv).
Proof.
 intros.
  apply pe_seq with (env' := tenv).
  constructor. constructor; try easy.
  constructor. easy. easy.
Qed.

Lemma xfactor_sem : forall x aenv tenv f n, 0 < n -> aenv x = n -> Env.MapsTo x Nor tenv ->
        right_mode_env aenv tenv f -> get_r_qft (exp_sem aenv (Rev x; QFT x) f) x = fbrev n (get_cus n f x).
Proof.
 intros.
 simpl.
 assert (nor_modes f x n).
 rewrite <- H0.
 apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
 unfold get_r_qft,turn_qft. rewrite H0.
 rewrite assign_r_same_0 with (size := n); try easy.
 unfold get_cus,reverse,fbrev.
 apply functional_extensionality; intros.
 bdestruct (x0 <? n).
 unfold nor_modes in *. simpl.
 bdestruct (x =? x).
 bdestruct (x0 <? n). simpl.
 specialize (H3 (n - 1 - x0)).
 assert (n - 1 - x0 < n) by lia.
 apply H3 in H7. unfold nor_mode in *.
 destruct (f (x, n - 1 - x0)) eqn:eq1.
 assert ((@pair var nat x (Init.Nat.sub (Init.Nat.sub n (S O)) x0)) =
    (@pair Env.key nat x (Init.Nat.sub (Init.Nat.sub n (S O)) x0))) by easy.
 rewrite H8 in *. rewrite eq1 in *.
 bdestruct (n - 1 - x0 <? n). easy. lia.
 assert ((@pair var nat x (Init.Nat.sub (Init.Nat.sub n (S O)) x0)) =
    (@pair Env.key nat x (Init.Nat.sub (Init.Nat.sub n (S O)) x0))) by easy.
 rewrite H8 in *. rewrite eq1 in *. easy.
 assert ((@pair var nat x (Init.Nat.sub (Init.Nat.sub n (S O)) x0)) =
    (@pair Env.key nat x (Init.Nat.sub (Init.Nat.sub n (S O)) x0))) by easy.
 rewrite H8 in *. rewrite eq1 in *.
 easy. lia. lia. easy.
 replace (reverse f x n) with (exp_sem aenv (Rev x) f).
 assert (right_mode_env aenv tenv ((exp_sem aenv (Rev x) f))).
 apply well_typed_right_mode_exp; try easy.
 constructor. easy.
 rewrite <- H0.
 apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
 simpl. rewrite H0. easy.
Qed.

Lemma xfactor_r : forall x aenv tenv f i n, 0 < n -> aenv x = n -> i < n -> Env.MapsTo x Nor tenv ->
        right_mode_env aenv tenv f -> get_r (exp_sem aenv (Rev x; QFT x) f (x,i)) = get_r (f (x,n-1-i)).
Proof.
 intros.
 simpl.
 assert (nor_modes f x n).
 rewrite <- H0.
 apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
 unfold get_r_qft,turn_qft.
 rewrite assign_r_angle_same.
 unfold reverse. simpl in *.
 rewrite H0.
 bdestruct (x =? x). bdestruct (i <? n). simpl. easy. lia. lia. rewrite H0. lia.
 assert (right_mode_env aenv tenv (exp_sem aenv (Rev x) f)).
 apply well_typed_right_mode_exp. constructor; try easy.
 easy.
 assert (nor_modes (exp_sem aenv (Rev x) f) x (aenv x)).
 apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
 simpl in *. easy.
Qed.

Definition rz_full_adder_form (x:var) (n:nat) (y:var) :=
   (Rev x; QFT x) ; rz_full_adder x n y ; 
  inv_exp (Rev x; QFT x).

Lemma rz_full_adder_sem : forall n size f x y A M aenv tenv, 
           n <= size -> x <> y -> size = aenv x -> size = aenv y ->
           Env.MapsTo x (Phi (aenv x)) tenv -> Env.MapsTo y Nor tenv -> right_mode_env aenv tenv f ->
           qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
           M < 2^size -> A < 2^size ->
           fbrev size (get_r_qft f x) = nat2fb A ->
           (get_cus size f y) = nat2fb M ->
           (get_r_qft (exp_sem aenv (rz_full_adder' x n size y) f) x)
              = (fbrev size (nat2fb ((A + (bindecomp n M)) mod 2^size))).
Proof.
  induction n;intros;simpl.
  unfold bindecomp. simpl.
  rewrite plus_0_r.
  rewrite Nat.mod_small by lia.
  rewrite <- H10.
  rewrite fbrev_twice_same. easy.
  destruct (get_cua (f (y, n))) eqn:eq1.
  assert ((@pair Env.key nat y n) = (@pair var nat y n)) by easy.
  rewrite H12 in *. clear H12. rewrite eq1 in *.
  unfold sr_rotate.
  assert ((get_cus size (sr_rotate' f x (S (size - S n)) (S (size - S n))) y) = get_cus size f y).
  unfold get_cus.
  apply functional_extensionality; intros.
  bdestruct (x0 <? size).
  rewrite sr_rotate'_irrelevant. easy. simpl. lia. easy.
  assert (right_mode_env aenv tenv (exp_sem aenv (SR (size - S n) x) f)).
  apply well_typed_right_mode_exp; try easy.
  apply sr_phi with (n := aenv x); try easy. rewrite <- H1. lia.
  rewrite bindecomp_seq.
  assert (fbrev size (get_r_qft (sr_rotate' f x (S (size - S n)) (S (size - S n))) x) 
           = nat2fb ((A + Nat.b2n (nat2fb M n) * 2 ^ n) mod  2 ^ size)).
  rewrite sr_rotate_get_r by lia.
  unfold get_phi_r.
  assert (phi_modes f x (aenv x)).
  apply type_phi_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H1 in H14. unfold phi_modes in H14.
  specialize (H14 0). assert (0 < size) by lia. apply H14 in H15.
  unfold phi_mode in H15.
  unfold times_rotate,rotate.
  destruct (f (x,0)) eqn: eq2.
  assert ((@pair var nat x O) = (@pair Env.key nat x O)) by easy. rewrite H16 in *.
  rewrite eq2 in *. easy.
  assert ((@pair var nat x O) = (@pair Env.key nat x O)) by easy. rewrite H16 in *.
  rewrite eq2 in *. easy.
  assert ((@pair var nat x O) = (@pair Env.key nat x O)) by easy. rewrite H16 in *.
  rewrite eq2 in *.
  unfold qft_uniform in *.
  specialize (H6 x H3 0).
  assert (0 < aenv x) by lia.
  apply H6 in H17. 
  rewrite lshift_fun_0 in *.
  unfold get_snd_r in H17. rewrite eq2 in *.
  rewrite (add_to_sem size); (try easy; try lia).
  rewrite cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  rewrite H17. rewrite H10.
  rewrite sumfb_correct_carry0.
  rewrite cut_n_mod.
  assert ((size - S (size - S n)) = n) by lia. rewrite H18.
  rewrite <- H11.
  rewrite get_cus_cua. rewrite eq1. simpl.
  rewrite plus_0_r. easy. lia.
  intros. rewrite H17.
  assert ((get_r_qft f x) = fbrev size (nat2fb A)).
  rewrite <- H10.
  rewrite fbrev_twice_same. easy.
  rewrite H19.
  unfold fbrev.
  bdestruct (i <? size). lia.
  rewrite nat2fb_bound with (n := size) by lia. easy.
  assert (n <= size) by lia.
  simpl in H13. unfold sr_rotate in H13.
  specialize (IHn size (sr_rotate' f x (S (size - S n)) (S (size - S n))) x y 
      ((A + Nat.b2n (nat2fb M n) * 2 ^ n) mod 2 ^ size) M aenv tenv H15 H0 H1 H2
      H3 H4 H13 ).
  rewrite IHn ; try easy.
  rewrite Nat.add_mod_idemp_l by lia.
  assert ((A + Nat.b2n (nat2fb M n) * 2 ^ n + bindecomp n M) = 
        (A + (bindecomp n M + Nat.b2n (nat2fb M n) * 2 ^ n))) by lia.
  rewrite H16. easy.
  replace ((sr_rotate' f x (S (size - S n)) (S (size - S n))))
    with (exp_sem aenv (SR (size - S n) x) f) by easy.
  apply qft_uniform_exp_trans with (tenv := tenv); try easy.
  constructor.
  apply sr_phi with (n := aenv x); try easy. rewrite <- H1. lia.
  replace ((sr_rotate' f x (S (size - S n)) (S (size - S n))))
    with (exp_sem aenv (SR (size - S n) x) f) by easy.
  apply qft_gt_exp_trans with (tenv := tenv); try easy.
  constructor.
  apply sr_phi with (n := aenv x); try easy. rewrite <- H1. lia.
  apply Nat.mod_upper_bound. lia.
  rewrite H12. easy.
  assert ((@pair Env.key nat y n) = (@pair var nat y n)) by easy.
  rewrite H12 in *. clear H12. rewrite eq1 in *.
  rewrite IHn with (A := A) (M := M) (tenv := tenv); try easy.
  rewrite bindecomp_seq. 
  rewrite <- H11. rewrite get_cus_cua. rewrite eq1. simpl.
  rewrite plus_0_r. easy. lia. lia.
Qed.

Lemma rz_full_adder_y_same : forall n i size f x y aenv tenv, 
           n <= size -> x <> y -> size = aenv x -> size = aenv y ->
           Env.MapsTo x (Phi (aenv x)) tenv -> Env.MapsTo y Nor tenv -> 
           (exp_sem aenv (rz_full_adder' x n size y) f) (y,i) = f (y,i).
Proof.
  induction n;intros;simpl. easy.
  destruct (get_cua (f (y, n))) eqn:eq1.
  assert ((@pair Env.key nat y n) = (@pair var nat y n)) by easy.
  rewrite H5 in *. clear H5. rewrite eq1 in *.
  rewrite IHn with (tenv := tenv); try easy.
  unfold sr_rotate. rewrite sr_rotate'_irrelevant; iner_p. easy. lia.
  assert ((@pair Env.key nat y n) = (@pair var nat y n)) by easy.
  rewrite H5 in *. clear H5. rewrite eq1 in *.
  rewrite IHn with (tenv := tenv); try easy. lia.
Qed.


Lemma efresh_rz_full_adder: forall n c x y size aenv, fst c <> x -> fst c <> y 
                 -> n <= size -> exp_fresh aenv c (rz_full_adder' x n size y).
Proof.
  induction n;intros; simpl.
  constructor. destruct c. iner_p.
  constructor.
  constructor. destruct c. iner_p.
  constructor. unfold or_not_r. left. easy.
  apply IHn. easy. easy. lia.
Qed.

Lemma exp_fresh_rz_full_adder'_ge : forall n m size x M aenv, 
     0 < n -> n <= size <= m -> exp_fresh aenv (x,m) (rz_full_adder' x n size M).
Proof.
  induction n; intros; simpl.
  constructor. iner_p.
  constructor.
  constructor. iner_p. constructor.  unfold or_not_r. right. simpl. lia.
  destruct n. simpl. constructor. iner_p.
  apply IHn. lia. lia.
Qed.

Lemma rz_full_adder_well_typed : forall n x y size aenv tenv, x <> y -> n <= size -> size = aenv x -> size = aenv y ->
           Env.MapsTo x (Phi (aenv x)) tenv -> Env.MapsTo y Nor tenv
           -> well_typed_pexp aenv tenv (rz_full_adder' x n size y) tenv.
Proof.
 induction n; intros; simpl.
 constructor. constructor.
 apply pe_seq with (env' := tenv).
  apply pcu_nor; try easy. simpl.
 constructor. unfold or_not_r. left. simpl. lia.
 constructor. constructor. apply sr_phi with (n := aenv x). easy. rewrite <- H1. lia.
 apply IHn; try easy. lia.
Qed.

Lemma rz_full_adder_phi_modes : forall n x size y f aenv tenv, n <= size -> size = aenv x ->
          size = aenv y ->  Env.MapsTo x (Phi (aenv x)) tenv -> Env.MapsTo y Nor tenv 
          -> right_mode_env aenv tenv f -> 
             phi_modes (exp_sem aenv (rz_full_adder' x n size y) f) x size.
Proof.
  induction n; intros.
  simpl in *. rewrite H0. apply type_phi_modes with (env := tenv); easy.
  simpl.
  destruct (get_cua (f (y, n))) eqn:eq1.
  assert ((@pair Env.key nat y n) = (@pair var nat y n)) by easy.
  rewrite H5 in *. clear H5. rewrite eq1 in *.
  apply IHn with (tenv := tenv); try easy. lia.
  replace  (sr_rotate f x (size - S n)) with (exp_sem aenv (SR (size - S n) x) f) by easy.
  apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
  constructor. apply sr_phi with (n := aenv x). easy. rewrite <- H0. lia.
  assert ((@pair Env.key nat y n) = (@pair var nat y n)) by easy.
  rewrite H5 in *. clear H5. rewrite eq1 in *.
  apply IHn with (tenv := tenv); try easy. lia.
Qed. 


Lemma rz_full_adder_r : forall n size i x y aenv tenv f, n <= size -> i < size -> aenv x = size
       -> aenv y = size -> Env.MapsTo x (Phi (aenv x)) tenv -> Env.MapsTo y Nor tenv -> right_mode_env aenv tenv f ->
      get_r (exp_sem aenv (rz_full_adder' x n size y) f (x,i)) = get_r (f (x,i)).
Proof.
 induction n; intros; simpl.
 easy.
  destruct (get_cua (f (y, n))) eqn:eq1.
  assert ((@pair Env.key nat y n) = (@pair var nat y n)) by easy.
  rewrite H6 in *. clear H6. rewrite eq1 in *.
 rewrite (IHn size i x y aenv tenv (sr_rotate f x (size - S n))); try easy.
 assert (phi_mode f (x,i)).
 apply type_phi_mode with (aenv := aenv) (env := tenv); try easy. simpl. lia.
 unfold get_r.
 unfold phi_mode in H6.
 unfold sr_rotate.
 bdestruct (i <? (S (size - S n))).
 rewrite sr_rotate'_lt_1; try lia.
 unfold times_rotate.
 destruct (f (x,i)) eqn:eq2.
  assert ((@pair Env.key nat x i) = (@pair var nat x i)) by easy.
  rewrite H8 in *. clear H8. rewrite eq2 in *. lia. easy.
  assert ((@pair Env.key nat x i) = (@pair var nat x i)) by easy.
  rewrite H8 in *. clear H8. rewrite eq2 in *. easy.
 rewrite sr_rotate'_ge.
 easy. simpl. lia. lia.
  replace  (sr_rotate f x (size - S n)) with (exp_sem aenv (SR (size - S n) x) f) by easy.
  apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
  constructor. apply sr_phi with (n := aenv x). easy. rewrite <- H1. lia.
   assert ((@pair Env.key nat y n) = (@pair var nat y n)) by easy.
  rewrite H6 in *. clear H6. rewrite eq1 in *.
 rewrite (IHn size i x y aenv tenv f); try easy. lia.
Qed.


Lemma rz_full_adder_form_correct :
  forall n f x y aenv tenv ,
    0 < n ->  x <> y -> aenv x = n -> aenv y = n ->
    Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv ->
    right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    exp_sem aenv (rz_full_adder_form x n y) f =
        (put_cus f x (sumfb false (get_cus n f y) (get_cus n f x)) n).
Proof.
  intros.
   unfold rz_full_adder_form in *. 
   rewrite exp_sem_seq.
   rewrite exp_sem_seq.
   specialize (xfactor_well_typed x aenv tenv H3) as eq1.
   remember (exp_sem aenv (Rev x; QFT x) f) as g.
   assert (right_mode_env aenv (Env.add x (Phi (aenv x)) tenv) g).
   subst.
   apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
   assert (qft_uniform aenv (Env.add x (Phi (aenv x)) tenv) g).
   subst.
   apply qft_uniform_exp_trans with (tenv := tenv); try easy.
   assert (qft_gt aenv (Env.add x (Phi (aenv x)) tenv) g).
   subst.
   apply qft_gt_exp_trans with (tenv := tenv); try easy.
   assert (get_r_qft g x = fbrev n ((get_cus n f x))).
   rewrite Heqg.
   apply xfactor_sem with (tenv := tenv); try easy.
   assert (forall z, z <> x -> (forall i, g (z,i) = f (z,i))).
   intros. rewrite Heqg.
   rewrite efresh_exp_sem_irrelevant; try easy.
   constructor. constructor. unfold or_not_eq. left. easy.
   constructor. unfold or_not_eq. left. easy.
   assert (nor_modes f x n).
   rewrite <- H1.
   apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
   assert (fbrev n (get_r_qft g x) = get_cus n f x).
   rewrite H11. rewrite fbrev_twice_same. easy.
   clear H11.
   assert (exists A, (get_cus n f x) = nat2fb A).
   rewrite <- put_get_cus_eq with (f := f) (x := x) (n := n); try easy.
   rewrite get_put_cus_cut_n; try easy.
   apply f_num_0. destruct H11 as [A eq2]. rewrite eq2 in H14.
   assert (eq3 := eq2).
   rewrite <- put_get_cus_eq with (f := f) (x := x) (n := n) in eq2; try easy.
   rewrite get_put_cus_cut_n in eq2; try easy.
   apply f_num_small in eq3.
   assert (nor_modes f y n).
   rewrite <- H2.
   apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
   assert (exists M, (get_cus n f y) = nat2fb M).
   rewrite <- put_get_cus_eq with (f := f) (x := y) (n := n); try easy.
   rewrite get_put_cus_cut_n; try easy.
   apply f_num_0. destruct H15 as [M eq4]. 
   assert (eq5 := eq4).
   rewrite <- put_get_cus_eq with (f := f) (x := y) (n := n) in eq5; try easy.
   rewrite get_put_cus_cut_n in eq5; try easy.
   apply f_num_small in eq5.
  unfold rz_full_adder in *.
  assert (Env.MapsTo x (Phi (aenv x)) (Env.add x (Phi (aenv x)) tenv)).
  apply Env.add_1. easy.
  assert (Env.MapsTo y Nor (Env.add x (Phi (aenv x)) tenv)).
  apply Env.add_2. lia. easy.
  assert (n <= n) by lia.
  symmetry in H1. symmetry in H2.
  assert (get_cus n f y = get_cus n g y).
  apply functional_extensionality; intros.
  rewrite Heqg.
  simpl. unfold turn_qft.
  bdestruct (x0 <? n).
  rewrite get_cus_cua.
  rewrite get_cus_cua.
  rewrite assign_r_out.
  unfold reverse.
  simpl. bdestruct (y =? x). lia. simpl. easy. iner_p. lia. lia.
  unfold get_cus. bdestruct (x0 <? n). lia. easy.
  rewrite H18 in eq4.
  specialize (rz_full_adder_sem n n g x y A M aenv (Env.add x (Phi (aenv x)) tenv)
        H17 H0 H1 H2 H15 H16 H8 H9 H10 eq5 eq3 H14 eq4) as eq6.
   remember (exp_sem aenv (rz_full_adder' x n n y) g) as gf.
   assert (right_mode_env aenv (Env.add x (Phi (aenv x)) tenv) gf).
   subst.
   apply well_typed_right_mode_pexp with (tenv := (Env.add x (Phi (aenv x)) tenv)); try easy.
   apply rz_full_adder_well_typed; try easy.
   assert (qft_uniform aenv (Env.add x (Phi (aenv x)) tenv) gf).
   rewrite Heqgf.
   Check qft_uniform_exp_trans.
   apply qft_uniform_exp_trans with (tenv := (Env.add x (Phi (aenv x)) tenv)); try easy.
   apply rz_full_adder_well_typed; try easy.
   assert (qft_gt aenv (Env.add x (Phi (aenv x)) tenv) gf).
   subst.
   apply qft_gt_exp_trans with  (tenv := (Env.add x (Phi (aenv x)) tenv)); try easy.
   apply rz_full_adder_well_typed; try easy.
   assert (forall z, z <> x -> (forall i, gf (z,i) = f (z,i))).
   intros. rewrite Heqgf.
   bdestruct (z =? y). rewrite H23 in *.
   rewrite rz_full_adder_y_same with (tenv := (Env.add x (Phi (aenv x)) tenv)); try easy.
   subst.
   rewrite efresh_exp_sem_irrelevant; try easy.
   constructor. constructor. unfold or_not_eq. left. iner_p.
   constructor. unfold or_not_eq. left. iner_p.
   rewrite efresh_exp_sem_irrelevant; try easy. rewrite H12. easy. lia.
   apply efresh_rz_full_adder; try easy.
   apply inv_pexp_reverse with (tenv' := (Env.add x (Phi (aenv x)) tenv)) (tenv := tenv); try easy.
   apply right_mode_exp_put_cus_same; try easy.
   apply qft_uniform_put_cus_same; try easy.
   apply qft_gt_put_cus_same; try easy.
   remember (put_cus f x (sumfb false (get_cus n f y) (get_cus n f x)) n) as h.
   assert (get_r_qft (exp_sem aenv (Rev x; QFT x) h) x = fbrev n (get_cus n h x)).
   apply xfactor_sem with (tenv := tenv); try easy.
   rewrite Heqh.
   apply right_mode_exp_put_cus_same; try easy.
   apply functional_extensionality; intros.
   destruct x0.
   bdestruct (v =? x). rewrite H18 in *. clear H18.
   bdestruct (n0 <? n).
   assert (get_r (gf (x,n0)) = get_r (g (x,n0))).
   rewrite Heqgf. 
   rewrite rz_full_adder_r with (tenv := (Env.add x (Phi (aenv x)) tenv)); try easy.
   rewrite H24 in *.
   assert (get_r (h (x, n - 1 - n0)) = get_r (f (x, n - 1 - n0))).
   rewrite Heqh. rewrite get_r_put_same; try easy.
   unfold qft_uniform in H20.
   apply phi_mode_two_same.
   apply type_phi_mode with (aenv := aenv) (env := (Env.add x (Phi (aenv x)) tenv)).
   simpl. apply Env.add_1. easy. simpl. rewrite <- H1. easy.
   apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
   subst.
   apply right_mode_exp_put_cus_same; try easy.
   apply type_phi_mode with (aenv := aenv) (env := (Env.add x (Phi (aenv x)) tenv)).
   simpl. apply Env.add_1. easy. simpl. rewrite <- H1. easy. easy.
   rewrite xfactor_r with (tenv := tenv) (n := n); try easy.
   rewrite H26.
   assert ((@pair Env.key nat x n0) = (@pair var nat x n0)) by easy.
   rewrite H27 in *.
   rewrite H25. rewrite Heqg.
   rewrite xfactor_r with (tenv := tenv) (n := n); try easy.
   subst.
   apply right_mode_exp_put_cus_same; try easy.
   rewrite H20; try easy. rewrite eq6.
   assert (qft_uniform aenv (Env.add x (Phi (aenv x)) tenv) (exp_sem aenv (Rev x; QFT x) h) ).
   rewrite Heqh.
   apply qft_uniform_exp_trans with (tenv := tenv); try easy.
   apply qft_uniform_put_cus_same; try easy.
   apply right_mode_exp_put_cus_same; try easy.
   unfold qft_uniform in H27. rewrite H27. rewrite H23. rewrite Heqh.
   assert ((get_cus n f x) = cut_n (get_cus n f x) n).
   remember (cut_n (get_cus n f x) n) as t.
   rewrite <- put_get_cus_eq with (f := f) (x := x) (n := n); try easy.
   rewrite get_put_cus_cut_n; try easy.
   rewrite <- H28 in *. rewrite eq2. rewrite eq4.
   rewrite sumfb_correct_carry0.
   rewrite bindecomp_spec.
   rewrite get_put_cus_cut_n.
   rewrite cut_n_mod.
   rewrite Nat.add_mod_idemp_r by lia.
   rewrite plus_comm. easy.
   rewrite H1.
   apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
   apply Env.add_1. easy.
   rewrite <- H1. easy.
   rewrite <- H1. easy.
   simpl.
   unfold turn_qft. rewrite H24 in *.
   rewrite assign_r_ge by lia.
   unfold reverse. simpl.
   rewrite <- H1. bdestruct (n0 <? n). lia. bdestruct ((x =? x)). simpl.
   rewrite Heqh.
   rewrite put_cus_out by lia.
   rewrite Heqgf.
   rewrite efresh_exp_sem_irrelevant with (p := (x,n0)).
   rewrite Heqg.
   simpl.
   unfold turn_qft.
   rewrite assign_r_ge by lia.
   unfold reverse. simpl.
   rewrite <- H1. bdestruct (n0 <? n). lia. bdestruct ((x =? x)). simpl.
   easy. lia. apply exp_fresh_rz_full_adder'_ge; try lia.
   lia. rewrite H22.
   simpl.
   unfold turn_qft.
   rewrite assign_r_out by iner_p.
   unfold reverse. simpl.
   rewrite <- H1. bdestruct (v =? x). lia. simpl.
   rewrite Heqh.
   rewrite put_cus_neq by lia.
   easy. easy.
Qed.


Definition rz_adder_form (x:var) (n:nat) (M:nat -> bool) :=
   (Rev x); QFT x; rz_adder x n M ;
  inv_exp ( (Rev x); QFT x).

Lemma rz_adder_form_well_typed : forall n x M aenv tenv, aenv x = n ->
      Env.MapsTo x Nor tenv -> well_typed_pexp aenv tenv (rz_adder_form x n M) tenv.
Proof.
 intros. unfold rz_adder_form.
  apply pe_seq with (env' := Env.add x (Phi (aenv x)) tenv).
  apply pe_seq with (env' := Env.add x (Phi (aenv x)) tenv).
  apply pe_seq with (env' := tenv).
  constructor. constructor. easy.
  constructor; try easy.
  Local Transparent rz_adder.
  unfold rz_adder.
  Local Opaque rz_adder.
  apply rz_adder_well_typed; try lia.
  apply Env.add_1. easy.
  apply typed_inv_pexp.
  apply pe_seq with (env' := tenv).
  constructor. constructor;try easy.
  constructor; try easy.
Qed.

Lemma rz_adder_form_correct :
  forall n f x M aenv tenv ,
    0 < n -> M < 2^n -> aenv x = n -> Env.MapsTo x Nor tenv ->
    right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    exp_sem aenv (rz_adder_form x n (nat2fb M)) f =
        (put_cus f x (sumfb false (nat2fb M) (get_cus n f x)) n).
Proof.
  intros.
   unfold rz_adder_form in *. 
   rewrite exp_sem_seq.
   rewrite exp_sem_seq.
   specialize (xfactor_well_typed x aenv tenv H2) as eq1.
   remember (exp_sem aenv (Rev x; QFT x) f) as g.
   assert (right_mode_env aenv (Env.add x (Phi (aenv x)) tenv) g).
   subst.
   apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
   assert (qft_uniform aenv (Env.add x (Phi (aenv x)) tenv) g).
   subst.
   apply qft_uniform_exp_trans with (tenv := tenv); try easy.
   assert (qft_gt aenv (Env.add x (Phi (aenv x)) tenv) g).
   subst.
   apply qft_gt_exp_trans with (tenv := tenv); try easy.
   assert (get_r_qft g x = fbrev n ((get_cus n f x))).
   rewrite Heqg.
   apply xfactor_sem with (tenv := tenv); try easy.
   assert (forall z, z <> x -> (forall i, g (z,i) = f (z,i))).
   intros. rewrite Heqg.
   rewrite efresh_exp_sem_irrelevant; try easy.
   constructor. constructor. unfold or_not_eq. left. easy.
   constructor. unfold or_not_eq. left. easy.
   assert (nor_modes f x n).
   rewrite <- H1.
   apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
   assert (fbrev n (get_r_qft g x) = get_cus n f x).
   rewrite H9. rewrite fbrev_twice_same. easy.
   clear H9.
   assert (exists A, (get_cus n f x) = nat2fb A).
   rewrite <- put_get_cus_eq with (f := f) (x := x) (n := n); try easy.
   rewrite get_put_cus_cut_n; try easy.
   apply f_num_0. destruct H9 as [A eq2]. rewrite eq2 in H12.
   assert (eq3 := eq2).
   rewrite <- put_get_cus_eq with (f := f) (x := x) (n := n) in eq2; try easy.
   rewrite get_put_cus_cut_n in eq2; try easy.
   apply f_num_small in eq3.
  Local Transparent rz_adder.
  unfold rz_adder in *.
  Local Opaque rz_adder.
  symmetry in H1.
  assert (Env.MapsTo x (Phi (aenv x)) (Env.add x (Phi (aenv x)) tenv)).
  apply Env.add_1. easy.
   Check rz_adder_full.
  specialize (rz_adder_full n g x A M aenv (Env.add x (Phi (aenv x)) tenv)
        H1 H9 H6 H0 eq3 H12) as eq4.
  Local Transparent rz_adder.
  unfold rz_adder in *.
  Local Opaque rz_adder.
   remember (exp_sem aenv (rz_adder' x n n (nat2fb M)) g) as gf.
   assert (right_mode_env aenv (Env.add x (Phi (aenv x)) tenv) gf).
   subst.
   apply well_typed_right_mode_pexp with (tenv := (Env.add x (Phi (aenv x)) tenv)); try easy.
   apply rz_adder_well_typed; try easy.
   assert (qft_uniform aenv (Env.add x (Phi (aenv x)) tenv) gf).
   rewrite Heqgf.
   Check qft_uniform_exp_trans.
   apply qft_uniform_exp_trans with (tenv := (Env.add x (Phi (aenv x)) tenv)); try easy.
   apply rz_adder_well_typed; try easy.
   assert (qft_gt aenv (Env.add x (Phi (aenv x)) tenv) gf).
   subst.
   apply qft_gt_exp_trans with  (tenv := (Env.add x (Phi (aenv x)) tenv)); try easy.
   apply rz_adder_well_typed; try easy.
   assert (forall z, z <> x -> (forall i, gf (z,i) = f (z,i))).
   intros. rewrite Heqgf.
   rewrite efresh_exp_sem_irrelevant; try easy. rewrite H10. easy. lia.
   apply efresh_rz_adder; try easy.
   apply inv_pexp_reverse with (tenv' := (Env.add x (Phi (aenv x)) tenv)) (tenv := tenv); try easy.
   apply right_mode_exp_put_cus_same; try easy.
   apply qft_uniform_put_cus_same; try easy.
   apply qft_gt_put_cus_same; try easy.
   remember (put_cus f x (sumfb false (nat2fb M) (get_cus n f x)) n) as h.
   assert (get_r_qft (exp_sem aenv (Rev x; QFT x) h) x = fbrev n (get_cus n h x)).
   apply xfactor_sem with (tenv := tenv); try easy.
   rewrite Heqh.
   apply right_mode_exp_put_cus_same; try easy.
   apply functional_extensionality; intros.
   destruct x0.
   bdestruct (v =? x). rewrite H18 in *. clear H18.
   bdestruct (n0 <? n).
   assert (get_r (gf (x,n0)) = get_r (g (x,n0))).
   rewrite Heqgf. 
   rewrite rz_adder_r with (tenv := (Env.add x (Phi (aenv x)) tenv)); try easy.
   assert (get_r (h (x, n - 1 - n0)) = get_r (f (x, n - 1 - n0))).
   rewrite Heqh. rewrite get_r_put_same; try easy.
   unfold qft_uniform in H14.
   apply phi_mode_two_same.
   apply type_phi_mode with (aenv := aenv) (env := (Env.add x (Phi (aenv x)) tenv)).
   simpl. apply Env.add_1. easy. simpl. rewrite <- H1. easy.
   apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
   subst.
   apply right_mode_exp_put_cus_same; try easy.
   apply type_phi_mode with (aenv := aenv) (env := (Env.add x (Phi (aenv x)) tenv)).
   simpl. apply Env.add_1. easy. simpl. rewrite <- H1. easy. easy.
   rewrite xfactor_r with (tenv := tenv) (n := n); try easy.
   rewrite H20.
   assert ((@pair Env.key nat x n0) = (@pair var nat x n0)) by easy.
   rewrite H21 in *.
   rewrite H19. rewrite Heqg.
   rewrite xfactor_r with (tenv := tenv) (n := n); try easy.
   subst.
   apply right_mode_exp_put_cus_same; try easy.
   rewrite H14; try easy. rewrite eq4.
   assert (qft_uniform aenv (Env.add x (Phi (aenv x)) tenv) (exp_sem aenv (Rev x; QFT x) h) ).
   rewrite Heqh.
   apply qft_uniform_exp_trans with (tenv := tenv); try easy.
   apply qft_uniform_put_cus_same; try easy.
   apply right_mode_exp_put_cus_same; try easy.
   unfold qft_uniform in H21. rewrite H21. rewrite H17. rewrite Heqh.
   assert ((get_cus n f x) = cut_n (get_cus n f x) n).
   remember (cut_n (get_cus n f x) n) as t.
   rewrite <- put_get_cus_eq with (f := f) (x := x) (n := n); try easy.
   rewrite get_put_cus_cut_n; try easy. rewrite H22. rewrite eq2.
   rewrite get_put_cus_cut_n; try easy.
   rewrite sumfb_correct_carry0.
   rewrite cut_n_mod.
   rewrite plus_comm. easy.
   apply Env.add_1. easy.
   rewrite <- H1. easy.
   rewrite <- H1. easy.
   unfold qft_gt in H15.
   simpl.
   unfold turn_qft.
   rewrite assign_r_ge by lia.
   unfold reverse. simpl.
   rewrite <- H1. bdestruct (n0 <? n). lia. bdestruct ((x =? x)). simpl.
   rewrite Heqh.
   rewrite put_cus_out by lia.
   rewrite Heqgf.
   rewrite efresh_exp_sem_irrelevant with (p := (x,n0)).
   rewrite Heqg.
   simpl.
   unfold turn_qft.
   rewrite assign_r_ge by lia.
   unfold reverse. simpl.
   rewrite <- H1. bdestruct (n0 <? n). lia. bdestruct ((x =? x)). simpl.
   easy. lia. apply exp_fresh_rz_adder'_ge; try lia.
   lia. rewrite H16.
   simpl.
   unfold turn_qft.
   rewrite assign_r_out by iner_p.
   unfold reverse. simpl.
   rewrite <- H1. bdestruct (v =? x). lia. simpl.
   rewrite Heqh.
   rewrite put_cus_neq by lia.
   easy. easy.
Qed.

Lemma put_cus_sumfb_cut : forall n f x b M g, put_cus f x (sumfb b M g) n = put_cus f x (sumfb b (cut_n M n) g) n.
Proof.
 intros. unfold put_cus.
  apply functional_extensionality. intros.
  destruct x0. simpl.
  bdestruct (v =? x). bdestruct (n0 <? n).
  assert ((sumfb b M g n0) = (sumfb b (cut_n M n) g n0)).
  unfold sumfb. rewrite <- carry_cut_n; try easy.
  unfold cut_n. bdestruct (n0 <? n). easy. lia.
  rewrite H1. easy. easy. easy.
Qed.

Lemma rz_adder'_cut_n_equal :
   forall n x size m M, n <= size <= m -> rz_adder' x n size M = rz_adder' x n size (cut_n M m).
Proof.
  induction n; intros; simpl.
  easy.
  rewrite IHn with ( m:= m) by lia.
  assert (M n = cut_n M m n).
  unfold cut_n. bdestruct (n <? m). easy. lia.
  rewrite H0. easy.
Qed.

Lemma rz_adder_form_correct_1 :
  forall n f x M aenv tenv ,
    0 < n -> aenv x = n -> Env.MapsTo x Nor tenv ->
    right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    exp_sem aenv (rz_adder_form x n M) f =
        (put_cus f x (sumfb false M (get_cus n f x)) n).
Proof.
  intros.
  assert ((rz_adder_form x n M) = (rz_adder_form x n (cut_n M n))).
  Local Transparent rz_adder. unfold rz_adder_form,rz_adder. Local Opaque rz_adder.
  rewrite rz_adder'_cut_n_equal with (m := n); try easy.
  rewrite H5.
  specialize (f_num_0 M n) as eq1. destruct eq1.
  rewrite H6.
  apply f_num_small in H6 as eq1.
  rewrite rz_adder_form_correct with (tenv := tenv); try easy.
  rewrite <- H6. rewrite <- put_cus_sumfb_cut. easy.
Qed.


Definition vars_for_rz_adder (size:nat) := gen_vars size (x_var::[]).

Definition rz_adder_out (size:nat) (M:nat-> bool) := rz_adder_form x_var size M.

Definition vars_for_rz_full_add (size:nat) := gen_vars size (x_var::y_var::[]).

Definition rz_full_adder_out (size:nat) := rz_full_adder_form x_var size y_var.

(* Implementing x - y subtractor. *)
Fixpoint rz_full_sub' (x:var) (n:nat) (size:nat) (y:var) :=
  match n with
  | 0 => (SKIP (x,0))
  | S m => ((CU (y,m) (SRR (size - n) x)); rz_full_sub' x m size y)
  end.
Definition rz_full_sub (x:var) (n:nat) (y:var) := rz_full_sub' x n n y.


Definition rz_full_sub_form (x:var) (n:nat) (y:var) :=
   (Rev x; QFT x) ; rz_full_sub x n y ; 
  inv_exp (Rev x; QFT x).

Lemma rz_full_sub_sem : forall n size f x y A M aenv tenv, 
           n <= size -> x <> y -> size = aenv x -> size = aenv y ->
           Env.MapsTo x (Phi (aenv x)) tenv -> Env.MapsTo y Nor tenv -> right_mode_env aenv tenv f ->
           qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
           M < 2^size -> A < 2^size ->
           fbrev size (get_r_qft f x) = nat2fb A ->
           (get_cus size f y) = nat2fb M ->
           (get_r_qft (exp_sem aenv (rz_full_sub' x n size y) f) x)
              = (fbrev size (nat2fb ((A + 2^size - (bindecomp n M)) mod 2^size))).
Proof.
  induction n;intros;simpl.
  unfold bindecomp. simpl.
  simpl. rewrite <- minus_n_O.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small by lia.
  rewrite <- H10.
  rewrite fbrev_twice_same. easy.
  destruct (get_cua (f (y, n))) eqn:eq1.
  assert ((@pair Env.key nat y n) = (@pair var nat y n)) by easy.
  rewrite H12 in *. clear H12. rewrite eq1 in *.
  unfold srr_rotate.
  assert ((get_cus size (srr_rotate' f x (S (size - S n)) (S (size - S n))) y) = get_cus size f y).
  unfold get_cus.
  apply functional_extensionality; intros.
  bdestruct (x0 <? size).
  rewrite srr_rotate'_irrelevant. easy. simpl. lia. easy.
  assert (right_mode_env aenv tenv (exp_sem aenv (SRR (size - S n) x) f)).
  apply well_typed_right_mode_exp; try easy.
  apply srr_phi with (n := aenv x); try easy. rewrite <- H1. lia.
  rewrite bindecomp_seq.
  assert (fbrev size (get_r_qft (srr_rotate' f x (S (size - S n)) (S (size - S n))) x) 
           = nat2fb ((A + 2 ^ size - Nat.b2n (nat2fb M n) * 2 ^ n) mod  2 ^ size)).
  rewrite srr_rotate_get_r by lia.
  unfold get_phi_r.
  assert (phi_modes f x (aenv x)).
  apply type_phi_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H1 in H14. unfold phi_modes in H14.
  specialize (H14 0). assert (0 < size) by lia. apply H14 in H15.
  unfold phi_mode in H15.
  unfold times_r_rotate,r_rotate.
  destruct (f (x,0)) eqn: eq2.
  assert ((@pair var nat x O) = (@pair Env.key nat x O)) by easy. rewrite H16 in *.
  rewrite eq2 in *. easy.
  assert ((@pair var nat x O) = (@pair Env.key nat x O)) by easy. rewrite H16 in *.
  rewrite eq2 in *. easy.
  assert ((@pair var nat x O) = (@pair Env.key nat x O)) by easy. rewrite H16 in *.
  rewrite eq2 in *.
  unfold qft_uniform in *.
  specialize (H6 x H3 0).
  assert (0 < aenv x) by lia.
  apply H6 in H17. 
  rewrite lshift_fun_0 in *.
  unfold get_snd_r in H17. rewrite eq2 in *.
  rewrite (add_to_n_sem size); (try easy; try lia).
  rewrite cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  rewrite H17. rewrite H10.
  rewrite sumfb_correct_carry0.
  rewrite cut_n_mod.
  assert ((size - S (size - S n)) = n) by lia. rewrite H18.
  rewrite <- H11.
  rewrite get_cus_cua. rewrite eq1. simpl.
  rewrite plus_0_r.
  assert (2^n < 2^ size).
  apply Nat.pow_lt_mono_r;try lia.
  assert ((A + (2 ^ size - 2 ^ n)) = (A + 2 ^ size - 2 ^ n)) by lia.
  rewrite H20.
  easy. lia.
  intros. rewrite H17.
  assert ((get_r_qft f x) = fbrev size (nat2fb A)).
  rewrite <- H10.
  rewrite fbrev_twice_same. easy.
  rewrite H19.
  unfold fbrev.
  bdestruct (i <? size). lia.
  rewrite nat2fb_bound with (n := size) by lia. easy.
  assert (n <= size) by lia.
  simpl in H13. unfold srr_rotate in H13.
  specialize (IHn size (srr_rotate' f x (S (size - S n)) (S (size - S n))) x y 
      ((A + 2 ^ size - Nat.b2n (nat2fb M n) * 2 ^ n) mod 2 ^ size) M aenv tenv H15 H0 H1 H2
      H3 H4 H13 ).
  rewrite IHn ; try easy.
  assert (bindecomp n M < 2^size).
  rewrite bindecomp_spec.
  assert (M mod 2 ^ n < 2^n). apply Nat.mod_upper_bound.
  apply Nat.pow_nonzero. lia.
  assert (2^n < 2^size).
  apply Nat.pow_lt_mono_r;try lia. lia.
  assert (forall (a b c : nat), c < b -> a + b - c = a  + (b - c)).
  intros. lia.
  rewrite H17 by lia.
  rewrite Nat.add_mod_idemp_l by lia.
  assert ((A + Nat.b2n (nat2fb M n) * 2 ^ n + bindecomp n M) = 
        (A + (bindecomp n M + Nat.b2n (nat2fb M n) * 2 ^ n))) by lia.
  rewrite <- H17 by lia.
  assert ((bindecomp n M + Nat.b2n (nat2fb M n) * 2 ^ n) < 2^size).
  rewrite <- bindecomp_seq.
  rewrite bindecomp_spec.
  assert (M mod 2 ^ S n < 2^S n). apply Nat.mod_upper_bound.
  apply Nat.pow_nonzero. lia.
  assert (2^S n <= 2^size).
  apply Nat.pow_le_mono_r;try lia. lia.
  assert ((A + 2 ^ size - Nat.b2n (nat2fb M n) * 2 ^ n + 2 ^ size - bindecomp n M)
       = (A + 2 ^ size - (bindecomp n M + Nat.b2n (nat2fb M n) * 2 ^ n)) + 2 ^ size) by lia.
  rewrite H20.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia. easy.
  replace ((srr_rotate' f x (S (size - S n)) (S (size - S n))))
    with (exp_sem aenv (SRR (size - S n) x) f) by easy.
  apply qft_uniform_exp_trans with (tenv := tenv); try easy.
  constructor.
  apply srr_phi with (n := aenv x); try easy. rewrite <- H1. lia.
  replace ((srr_rotate' f x (S (size - S n)) (S (size - S n))))
    with (exp_sem aenv (SRR (size - S n) x) f) by easy.
  apply qft_gt_exp_trans with (tenv := tenv); try easy.
  constructor.
  apply srr_phi with (n := aenv x); try easy. rewrite <- H1. lia.
  apply Nat.mod_upper_bound. lia.
  rewrite H12. easy.
  assert ((@pair Env.key nat y n) = (@pair var nat y n)) by easy.
  rewrite H12 in *. clear H12. rewrite eq1 in *.
  rewrite IHn with (A := A) (M := M) (tenv := tenv); try easy.
  rewrite bindecomp_seq. 
  rewrite <- H11. rewrite get_cus_cua. rewrite eq1. simpl.
  rewrite plus_0_r. easy. lia. lia.
Qed.

Lemma rz_full_sub_y_same : forall n i size f x y aenv tenv, 
           n <= size -> x <> y -> size = aenv x -> size = aenv y ->
           Env.MapsTo x (Phi (aenv x)) tenv -> Env.MapsTo y Nor tenv -> 
           (exp_sem aenv (rz_full_sub' x n size y) f) (y,i) = f (y,i).
Proof.
  induction n;intros;simpl. easy.
  destruct (get_cua (f (y, n))) eqn:eq1.
  assert ((@pair Env.key nat y n) = (@pair var nat y n)) by easy.
  rewrite H5 in *. clear H5. rewrite eq1 in *.
  rewrite IHn with (tenv := tenv); try easy.
  unfold srr_rotate. rewrite srr_rotate'_irrelevant; iner_p. easy. lia.
  assert ((@pair Env.key nat y n) = (@pair var nat y n)) by easy.
  rewrite H5 in *. clear H5. rewrite eq1 in *.
  rewrite IHn with (tenv := tenv); try easy. lia.
Qed.


Lemma efresh_rz_full_sub: forall n c x y size aenv, fst c <> x -> fst c <> y 
                 -> n <= size -> exp_fresh aenv c (rz_full_sub' x n size y).
Proof.
  induction n;intros; simpl.
  constructor. destruct c. iner_p.
  constructor.
  constructor. destruct c. iner_p.
  constructor. unfold or_not_r. left. easy.
  apply IHn. easy. easy. lia.
Qed.

Lemma exp_fresh_rz_full_sub'_ge : forall n m size x M aenv, 
     0 < n -> n <= size <= m -> exp_fresh aenv (x,m) (rz_full_sub' x n size M).
Proof.
  induction n; intros; simpl.
  constructor. iner_p.
  constructor.
  constructor. iner_p. constructor.  unfold or_not_r. right. simpl. lia.
  destruct n. simpl. constructor. iner_p.
  apply IHn. lia. lia.
Qed.

Lemma rz_full_sub_well_typed : forall n x y size aenv tenv, x <> y -> n <= size -> size = aenv x -> size = aenv y ->
           Env.MapsTo x (Phi (aenv x)) tenv -> Env.MapsTo y Nor tenv
           -> well_typed_pexp aenv tenv (rz_full_sub' x n size y) tenv.
Proof.
 induction n; intros; simpl.
 constructor. constructor.
 apply pe_seq with (env' := tenv).
  apply pcu_nor; try easy. simpl.
 constructor. unfold or_not_r. left. simpl. lia.
 constructor. constructor. apply srr_phi with (n := aenv x). easy. rewrite <- H1. lia.
 apply IHn; try easy. lia.
Qed.

Lemma rz_full_sub_phi_modes : forall n x size y f aenv tenv, n <= size -> size = aenv x ->
          size = aenv y ->  Env.MapsTo x (Phi (aenv x)) tenv -> Env.MapsTo y Nor tenv 
          -> right_mode_env aenv tenv f -> 
             phi_modes (exp_sem aenv (rz_full_sub' x n size y) f) x size.
Proof.
  induction n; intros.
  simpl in *. rewrite H0. apply type_phi_modes with (env := tenv); easy.
  simpl.
  destruct (get_cua (f (y, n))) eqn:eq1.
  assert ((@pair Env.key nat y n) = (@pair var nat y n)) by easy.
  rewrite H5 in *. clear H5. rewrite eq1 in *.
  apply IHn with (tenv := tenv); try easy. lia.
  replace  (srr_rotate f x (size - S n)) with (exp_sem aenv (SRR (size - S n) x) f) by easy.
  apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
  constructor. apply srr_phi with (n := aenv x). easy. rewrite <- H0. lia.
  assert ((@pair Env.key nat y n) = (@pair var nat y n)) by easy.
  rewrite H5 in *. clear H5. rewrite eq1 in *.
  apply IHn with (tenv := tenv); try easy. lia.
Qed. 


Lemma rz_full_sub_r : forall n size i x y aenv tenv f, n <= size -> i < size -> aenv x = size
       -> aenv y = size -> Env.MapsTo x (Phi (aenv x)) tenv -> Env.MapsTo y Nor tenv -> right_mode_env aenv tenv f ->
      get_r (exp_sem aenv (rz_full_sub' x n size y) f (x,i)) = get_r (f (x,i)).
Proof.
 induction n; intros; simpl.
 easy.
  destruct (get_cua (f (y, n))) eqn:eq1.
  assert ((@pair Env.key nat y n) = (@pair var nat y n)) by easy.
  rewrite H6 in *. clear H6. rewrite eq1 in *.
 rewrite (IHn size i x y aenv tenv (srr_rotate f x (size - S n))); try easy.
 assert (phi_mode f (x,i)).
 apply type_phi_mode with (aenv := aenv) (env := tenv); try easy. simpl. lia.
 unfold get_r.
 unfold phi_mode in H6.
 unfold srr_rotate.
 bdestruct (i <? (S (size - S n))).
 rewrite srr_rotate'_lt_1; try lia.
 unfold times_r_rotate.
 destruct (f (x,i)) eqn:eq2.
  assert ((@pair Env.key nat x i) = (@pair var nat x i)) by easy.
  rewrite H8 in *. clear H8. rewrite eq2 in *. lia. easy.
  assert ((@pair Env.key nat x i) = (@pair var nat x i)) by easy.
  rewrite H8 in *. clear H8. rewrite eq2 in *. easy.
 rewrite srr_rotate'_ge.
 easy. simpl. lia. lia.
  replace  (srr_rotate f x (size - S n)) with (exp_sem aenv (SRR (size - S n) x) f) by easy.
  apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
  constructor. apply srr_phi with (n := aenv x). easy. rewrite <- H1. lia.
   assert ((@pair Env.key nat y n) = (@pair var nat y n)) by easy.
  rewrite H6 in *. clear H6. rewrite eq1 in *.
 rewrite (IHn size i x y aenv tenv f); try easy. lia.
Qed.

Lemma rz_full_sub_form_correct :
  forall n f x y aenv tenv ,
    0 < n ->  x<> y -> aenv x = n -> aenv y = n ->
    Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv ->
    right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    exp_sem aenv (rz_full_sub_form x n y) f =
        (put_cus f x (sumfb true (negatem n (get_cus n f y)) (get_cus n f x)) n).
Proof.
  intros.
   unfold rz_full_sub_form in *. 
   rewrite exp_sem_seq.
   rewrite exp_sem_seq.
   specialize (xfactor_well_typed x aenv tenv H3) as eq1.
   remember (exp_sem aenv (Rev x; QFT x) f) as g.
   assert (right_mode_env aenv (Env.add x (Phi (aenv x)) tenv) g).
   subst.
   apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
   assert (qft_uniform aenv (Env.add x (Phi (aenv x)) tenv) g).
   subst.
   apply qft_uniform_exp_trans with (tenv := tenv); try easy.
   assert (qft_gt aenv (Env.add x (Phi (aenv x)) tenv) g).
   subst.
   apply qft_gt_exp_trans with (tenv := tenv); try easy.
   assert (get_r_qft g x = fbrev n ((get_cus n f x))).
   rewrite Heqg.
   apply xfactor_sem with (tenv := tenv); try easy.
   assert (forall z, z <> x -> (forall i, g (z,i) = f (z,i))).
   intros. rewrite Heqg.
   rewrite efresh_exp_sem_irrelevant; try easy.
   constructor. constructor. unfold or_not_eq. left. easy.
   constructor. unfold or_not_eq. left. easy.
   assert (nor_modes f x n).
   rewrite <- H1.
   apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
   assert (fbrev n (get_r_qft g x) = get_cus n f x).
   rewrite H11. rewrite fbrev_twice_same. easy.
   clear H11.
   assert (exists A, (get_cus n f x) = nat2fb A).
   rewrite <- put_get_cus_eq with (f := f) (x := x) (n := n); try easy.
   rewrite get_put_cus_cut_n; try easy.
   apply f_num_0. destruct H11 as [A eq2]. rewrite eq2 in H14.
   assert (eq3 := eq2).
   rewrite <- put_get_cus_eq with (f := f) (x := x) (n := n) in eq2; try easy.
   rewrite get_put_cus_cut_n in eq2; try easy.
   apply f_num_small in eq3.
   assert (nor_modes f y n).
   rewrite <- H2.
   apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
   assert (exists M, (get_cus n f y) = nat2fb M).
   rewrite <- put_get_cus_eq with (f := f) (x := y) (n := n); try easy.
   rewrite get_put_cus_cut_n; try easy.
   apply f_num_0. destruct H15 as [M eq4]. 
   assert (eq5 := eq4).
   rewrite <- put_get_cus_eq with (f := f) (x := y) (n := n) in eq5; try easy.
   rewrite get_put_cus_cut_n in eq5; try easy.
   apply f_num_small in eq5.
  unfold rz_full_sub in *.
  assert (Env.MapsTo x (Phi (aenv x)) (Env.add x (Phi (aenv x)) tenv)).
  apply Env.add_1. easy.
  assert (Env.MapsTo y Nor (Env.add x (Phi (aenv x)) tenv)).
  apply Env.add_2. lia. easy.
  assert (n <= n) by lia.
  symmetry in H1. symmetry in H2.
  assert (get_cus n f y = get_cus n g y).
  apply functional_extensionality; intros.
  rewrite Heqg.
  simpl. unfold turn_qft.
  bdestruct (x0 <? n).
  rewrite get_cus_cua.
  rewrite get_cus_cua.
  rewrite assign_r_out.
  unfold reverse.
  simpl. bdestruct (y =? x). lia. simpl. easy. iner_p. lia. lia.
  unfold get_cus. bdestruct (x0 <? n). lia. easy.
  rewrite H18 in eq4.
  specialize (rz_full_sub_sem n n g x y A M aenv (Env.add x (Phi (aenv x)) tenv)
        H17 H0 H1 H2 H15 H16 H8 H9 H10 eq5 eq3 H14 eq4) as eq6.
   remember (exp_sem aenv (rz_full_sub' x n n y) g) as gf.
   assert (right_mode_env aenv (Env.add x (Phi (aenv x)) tenv) gf).
   subst.
   apply well_typed_right_mode_pexp with (tenv := (Env.add x (Phi (aenv x)) tenv)); try easy.
   apply rz_full_sub_well_typed; try easy.
   assert (qft_uniform aenv (Env.add x (Phi (aenv x)) tenv) gf).
   rewrite Heqgf.
   Check qft_uniform_exp_trans.
   apply qft_uniform_exp_trans with (tenv := (Env.add x (Phi (aenv x)) tenv)); try easy.
   apply rz_full_sub_well_typed; try easy.
   assert (qft_gt aenv (Env.add x (Phi (aenv x)) tenv) gf).
   subst.
   apply qft_gt_exp_trans with  (tenv := (Env.add x (Phi (aenv x)) tenv)); try easy.
   apply rz_full_sub_well_typed; try easy.
   assert (forall z, z <> x -> (forall i, gf (z,i) = f (z,i))).
   intros. rewrite Heqgf.
   bdestruct (z =? y). rewrite H23 in *.
   rewrite rz_full_sub_y_same with (tenv := (Env.add x (Phi (aenv x)) tenv)); try easy.
   subst.
   rewrite efresh_exp_sem_irrelevant; try easy.
   constructor. constructor. unfold or_not_eq. left. iner_p.
   constructor. unfold or_not_eq. left. iner_p.
   rewrite efresh_exp_sem_irrelevant; try easy. rewrite H12. easy. lia.
   apply efresh_rz_full_sub; try easy.
   apply inv_pexp_reverse with (tenv' := (Env.add x (Phi (aenv x)) tenv)) (tenv := tenv); try easy.
   apply right_mode_exp_put_cus_same; try easy.
   apply qft_uniform_put_cus_same; try easy.
   apply qft_gt_put_cus_same; try easy.
   remember (put_cus f x (sumfb true (negatem n (get_cus n f y)) (get_cus n f x)) n) as h.
   assert (get_r_qft (exp_sem aenv (Rev x; QFT x) h) x = fbrev n (get_cus n h x)).
   apply xfactor_sem with (tenv := tenv); try easy.
   rewrite Heqh.
   apply right_mode_exp_put_cus_same; try easy.
   apply functional_extensionality; intros.
   destruct x0.
   bdestruct (v =? x). rewrite H18 in *. clear H18.
   bdestruct (n0 <? n).
   assert (get_r (gf (x,n0)) = get_r (g (x,n0))).
   rewrite Heqgf. 
   rewrite rz_full_sub_r with (tenv := (Env.add x (Phi (aenv x)) tenv)); try easy.
   rewrite H24 in *.
   assert (get_r (h (x, n - 1 - n0)) = get_r (f (x, n - 1 - n0))).
   rewrite Heqh. rewrite get_r_put_same; try easy.
   unfold qft_uniform in H20.
   apply phi_mode_two_same.
   apply type_phi_mode with (aenv := aenv) (env := (Env.add x (Phi (aenv x)) tenv)).
   simpl. apply Env.add_1. easy. simpl. rewrite <- H1. easy.
   apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
   subst.
   apply right_mode_exp_put_cus_same; try easy.
   apply type_phi_mode with (aenv := aenv) (env := (Env.add x (Phi (aenv x)) tenv)).
   simpl. apply Env.add_1. easy. simpl. rewrite <- H1. easy. easy.
   rewrite xfactor_r with (tenv := tenv) (n := n); try easy.
   rewrite H26.
   assert ((@pair Env.key nat x n0) = (@pair var nat x n0)) by easy.
   rewrite H27 in *.
   rewrite H25. rewrite Heqg.
   rewrite xfactor_r with (tenv := tenv) (n := n); try easy.
   subst.
   apply right_mode_exp_put_cus_same; try easy.
   rewrite H20; try easy. rewrite eq6.
   assert (qft_uniform aenv (Env.add x (Phi (aenv x)) tenv) (exp_sem aenv (Rev x; QFT x) h) ).
   rewrite Heqh.
   apply qft_uniform_exp_trans with (tenv := tenv); try easy.
   apply qft_uniform_put_cus_same; try easy.
   apply right_mode_exp_put_cus_same; try easy.
   unfold qft_uniform in H27. rewrite H27. rewrite H23. rewrite Heqh.
   assert ((get_cus n f x) = cut_n (get_cus n f x) n).
   remember (cut_n (get_cus n f x) n) as t.
   rewrite <- put_get_cus_eq with (f := f) (x := x) (n := n); try easy.
   rewrite get_put_cus_cut_n; try easy.
   rewrite <- H28 in *. rewrite eq2. rewrite eq4.
   rewrite negatem_arith.
   rewrite sumfb_correct_carry1.
   rewrite bindecomp_spec.
   rewrite get_put_cus_cut_n.
   rewrite cut_n_mod.
   rewrite (Nat.mod_small M) by easy.
   assert ((2 ^ n - 1 - M + A + 1) = (A + 2 ^ n - M)) by lia.
   rewrite H29. easy.
   rewrite H1.
   apply type_nor_modes with (aenv := aenv) (env := tenv); try easy. easy.
   apply Env.add_1. easy.
   rewrite <- H1. easy.
   rewrite <- H1. easy.
   simpl.
   unfold turn_qft. rewrite H24 in *.
   rewrite assign_r_ge by lia.
   unfold reverse. simpl.
   rewrite <- H1. bdestruct (n0 <? n). lia. bdestruct ((x =? x)). simpl.
   rewrite Heqh.
   rewrite put_cus_out by lia.
   rewrite Heqgf.
   rewrite efresh_exp_sem_irrelevant with (p := (x,n0)).
   rewrite Heqg.
   simpl.
   unfold turn_qft.
   rewrite assign_r_ge by lia.
   unfold reverse. simpl.
   rewrite <- H1. bdestruct (n0 <? n). lia. bdestruct ((x =? x)). simpl.
   easy. lia. apply exp_fresh_rz_full_sub'_ge; try lia.
   lia. rewrite H22.
   simpl.
   unfold turn_qft.
   rewrite assign_r_out by iner_p.
   unfold reverse. simpl.
   rewrite <- H1. bdestruct (v =? x). lia. simpl.
   rewrite Heqh.
   rewrite put_cus_neq by lia.
   easy. easy.
Qed.

(* Implementing x - M subtractor. *)
Definition rz_sub_right (x:var) (n:nat) (M:nat -> bool) :=
   (Rev x; QFT x); rz_sub x n M ; inv_exp (Rev x; QFT x).

Lemma rz_sub_right_sem : forall n f x M aenv tenv ,
    0 < n -> M < 2^n -> aenv x = n -> Env.MapsTo x Nor tenv ->
    right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    exp_sem aenv (rz_sub_right x n (nat2fb M)) f =
        (put_cus f x ((sumfb true (negatem n (nat2fb M)) (get_cus n f x))) n).
Proof.
  intros.
   unfold rz_sub_right in *. 
   rewrite exp_sem_seq.
   rewrite exp_sem_seq.
   specialize (xfactor_well_typed x aenv tenv H2) as eq1.
   remember (exp_sem aenv (Rev x; QFT x) f) as g.
   assert (right_mode_env aenv (Env.add x (Phi (aenv x)) tenv) g).
   subst.
   apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
   assert (qft_uniform aenv (Env.add x (Phi (aenv x)) tenv) g).
   subst.
   apply qft_uniform_exp_trans with (tenv := tenv); try easy.
   assert (qft_gt aenv (Env.add x (Phi (aenv x)) tenv) g).
   subst.
   apply qft_gt_exp_trans with (tenv := tenv); try easy.
   assert (get_r_qft g x = fbrev n ((get_cus n f x))).
   rewrite Heqg.
   apply xfactor_sem with (tenv := tenv); try easy.
   assert (forall z, z <> x -> (forall i, g (z,i) = f (z,i))).
   intros. rewrite Heqg.
   rewrite efresh_exp_sem_irrelevant; try easy.
   constructor. constructor. unfold or_not_eq. left. easy.
   constructor. unfold or_not_eq. left. easy.
   assert (nor_modes f x n).
   rewrite <- H1.
   apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
   assert (fbrev n (get_r_qft g x) = get_cus n f x).
   rewrite H9. rewrite fbrev_twice_same. easy.
   clear H9.
   assert (exists A, (get_cus n f x) = nat2fb A).
   rewrite <- put_get_cus_eq with (f := f) (x := x) (n := n); try easy.
   rewrite get_put_cus_cut_n; try easy.
   apply f_num_0. destruct H9 as [A eq2]. rewrite eq2 in H12.
   assert (eq3 := eq2).
   rewrite <- put_get_cus_eq with (f := f) (x := x) (n := n) in eq2; try easy.
   rewrite get_put_cus_cut_n in eq2; try easy.
   apply f_num_small in eq3.
  Local Transparent rz_sub.
  unfold rz_sub in *.
  Local Opaque rz_sub.
  symmetry in H1.
  assert (Env.MapsTo x (Phi (aenv x)) (Env.add x (Phi (aenv x)) tenv)).
  apply Env.add_1. easy.
   Check rz_sub_full.
  specialize (rz_sub_full n g x A M aenv (Env.add x (Phi (aenv x)) tenv)
        H1 H9 H6 H0 eq3 H12) as eq4.
  Local Transparent rz_sub.
  unfold rz_sub in *.
  Local Opaque rz_sub.
   remember (exp_sem aenv (rz_sub' x n n (nat2fb M)) g) as gf.
   assert (right_mode_env aenv (Env.add x (Phi (aenv x)) tenv) gf).
   subst.
   apply well_typed_right_mode_pexp with (tenv := (Env.add x (Phi (aenv x)) tenv)); try easy.
   apply rz_sub_well_typed; try easy.
   assert (qft_uniform aenv (Env.add x (Phi (aenv x)) tenv) gf).
   rewrite Heqgf.
   Check qft_uniform_exp_trans.
   apply qft_uniform_exp_trans with (tenv := (Env.add x (Phi (aenv x)) tenv)); try easy.
   apply rz_sub_well_typed; try easy.
   assert (qft_gt aenv (Env.add x (Phi (aenv x)) tenv) gf).
   subst.
   apply qft_gt_exp_trans with  (tenv := (Env.add x (Phi (aenv x)) tenv)); try easy.
   apply rz_sub_well_typed; try easy.
   assert (forall z, z <> x -> (forall i, gf (z,i) = f (z,i))).
   intros. rewrite Heqgf.
   rewrite efresh_exp_sem_irrelevant; try easy. rewrite H10. easy. lia.
   apply efresh_rz_sub; try easy.
   apply inv_pexp_reverse with (tenv' := (Env.add x (Phi (aenv x)) tenv)) (tenv := tenv); try easy.
   apply right_mode_exp_put_cus_same; try easy.
   apply qft_uniform_put_cus_same; try easy.
   apply qft_gt_put_cus_same; try easy.
   remember (put_cus f x (sumfb true (negatem n (nat2fb M)) (get_cus n f x)) n) as h.
   assert (get_r_qft (exp_sem aenv (Rev x; QFT x) h) x = fbrev n (get_cus n h x)).
   apply xfactor_sem with (tenv := tenv); try easy.
   rewrite Heqh.
   apply right_mode_exp_put_cus_same; try easy.
   apply functional_extensionality; intros.
   destruct x0.
   bdestruct (v =? x). rewrite H18 in *. clear H18.
   bdestruct (n0 <? n).
   assert (get_r (gf (x,n0)) = get_r (g (x,n0))).
   rewrite Heqgf. 
   rewrite rz_sub_r with (tenv := (Env.add x (Phi (aenv x)) tenv)); try easy.
   assert (get_r (h (x, n - 1 - n0)) = get_r (f (x, n - 1 - n0))).
   rewrite Heqh. rewrite get_r_put_same; try easy.
   unfold qft_uniform in H14.
   apply phi_mode_two_same.
   apply type_phi_mode with (aenv := aenv) (env := (Env.add x (Phi (aenv x)) tenv)).
   simpl. apply Env.add_1. easy. simpl. rewrite <- H1. easy.
   apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
   subst.
   apply right_mode_exp_put_cus_same; try easy.
   apply type_phi_mode with (aenv := aenv) (env := (Env.add x (Phi (aenv x)) tenv)).
   simpl. apply Env.add_1. easy. simpl. rewrite <- H1. easy. easy.
   rewrite xfactor_r with (tenv := tenv) (n := n); try easy.
   rewrite H20.
   assert ((@pair Env.key nat x n0) = (@pair var nat x n0)) by easy.
   rewrite H21 in *.
   rewrite H19. rewrite Heqg.
   rewrite xfactor_r with (tenv := tenv) (n := n); try easy.
   subst.
   apply right_mode_exp_put_cus_same; try easy.
   rewrite H14; try easy. rewrite eq4.
   assert (qft_uniform aenv (Env.add x (Phi (aenv x)) tenv) (exp_sem aenv (Rev x; QFT x) h) ).
   rewrite Heqh.
   apply qft_uniform_exp_trans with (tenv := tenv); try easy.
   apply qft_uniform_put_cus_same; try easy.
   apply right_mode_exp_put_cus_same; try easy.
   unfold qft_uniform in H21. rewrite H21. rewrite H17. rewrite Heqh.
   assert ((get_cus n f x) = cut_n (get_cus n f x) n).
   remember (cut_n (get_cus n f x) n) as t.
   rewrite <- put_get_cus_eq with (f := f) (x := x) (n := n); try easy.
   rewrite get_put_cus_cut_n; try easy. rewrite H22. rewrite eq2.
   rewrite get_put_cus_cut_n; try easy.
   rewrite negatem_arith.
   rewrite sumfb_correct_carry1.
   rewrite cut_n_mod.
   assert ((2 ^ n - 1 - M + A + 1) = (A + 2 ^ n - M)) by lia.
   rewrite H23. easy. easy.
   apply Env.add_1. easy.
   rewrite <- H1. easy.
   rewrite <- H1. easy.
   unfold qft_gt in H15.
   simpl.
   unfold turn_qft.
   rewrite assign_r_ge by lia.
   unfold reverse. simpl.
   rewrite <- H1. bdestruct (n0 <? n). lia. bdestruct ((x =? x)). simpl.
   rewrite Heqh.
   rewrite put_cus_out by lia.
   rewrite Heqgf.
   rewrite efresh_exp_sem_irrelevant with (p := (x,n0)).
   rewrite Heqg.
   simpl.
   unfold turn_qft.
   rewrite assign_r_ge by lia.
   unfold reverse. simpl.
   rewrite <- H1. bdestruct (n0 <? n). lia. bdestruct ((x =? x)). simpl.
   easy. lia. apply exp_fresh_rz_sub'_ge; try lia.
   lia. rewrite H16.
   simpl.
   unfold turn_qft.
   rewrite assign_r_out by iner_p.
   unfold reverse. simpl.
   rewrite <- H1. bdestruct (v =? x). lia. simpl.
   rewrite Heqh.
   rewrite put_cus_neq by lia.
   easy. easy.
Qed.

Lemma put_cus_sumfb_neg_cut : forall n f x b M g, put_cus f x (sumfb b (negatem n M) g) n
            = put_cus f x (sumfb b (negatem n (cut_n M n)) g) n.
Proof.
 intros. unfold put_cus.
  apply functional_extensionality. intros.
  destruct x0. simpl.
  bdestruct (v =? x). bdestruct (n0 <? n).
  assert ((sumfb b (negatem n M) g n0) = (sumfb b (negatem n (cut_n M n)) g n0)).
  unfold sumfb. rewrite <- carry_cut_n_neg; try easy.
  unfold negatem,cut_n. bdestruct (n0 <? n). easy. lia.
  rewrite H1. easy. easy. easy.
Qed.

Lemma rz_sub'_cut_n_equal :
   forall n x size m M, n <= size <= m -> rz_sub' x n size M = rz_sub' x n size (cut_n M m).
Proof.
  induction n; intros; simpl.
  easy.
  rewrite IHn with ( m:= m) by lia.
  assert (M n = cut_n M m n).
  unfold cut_n. bdestruct (n <? m). easy. lia.
  rewrite H0. easy.
Qed.

Lemma rz_sub_right_sem_1 : forall n f x M aenv tenv ,
    0 < n -> aenv x = n -> Env.MapsTo x Nor tenv ->
    right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    exp_sem aenv (rz_sub_right x n M) f =
        (put_cus f x ((sumfb true (negatem n M) (get_cus n f x))) n).
Proof.
  intros.
  assert ((rz_sub_right x n M) = (rz_sub_right x n (cut_n M n))).
  Local Transparent rz_sub. unfold rz_sub_right,rz_sub. Local Opaque rz_sub.
  rewrite rz_sub'_cut_n_equal with (m := n); try easy.
  rewrite H5.
  specialize (f_num_0 M n) as eq1. destruct eq1.
  rewrite H6.
  apply f_num_small in H6 as eq1.
  rewrite rz_sub_right_sem with (tenv := tenv); try easy.
  rewrite <- H6. rewrite <- put_cus_sumfb_neg_cut. easy.
Qed.


(* Implementing M - x subtractor. *)
Definition rz_sub_left (M:nat -> bool) (x:var) (n:nat) :=
   (Rev x); QFT x; rz_sub x n M; inv_exp ( (Rev x); QFT x); negator0 n x.

(* Implementing x < y comparator. *)
Definition rz_full_comparator (x:var) (n:nat) (c:posi) (y:var) := 
     (Rev x; Rev y); QFT x; QFT y; (rz_full_sub x n y); RQFT x ;  (CNOT (x,0) c);
    inv_exp ( (Rev x; Rev y); QFT x; QFT y;  (rz_full_sub x n y); RQFT x).

(* compare x < M *)
Definition rz_compare_half3 (x:var) (n:nat) (c:posi) (M:nat -> bool) := 
   (rz_sub x n M) ; RQFT x ; (CNOT (x,0) c).

(* compare x >= M *)
Definition rz_compare_half2 (x:var) (n:nat) (c:posi) (M:nat -> bool) := 
   (rz_sub x n M) ; RQFT x ;  (X (x,0); CNOT (x,0) c ; X (x,0)).

(* if x >= M, then the effect of x states. at this point, high-bit of x is 0. 
    otherwise, clean up x, and move on. *)
Fixpoint rz_moder' i (n:nat) (x ex:var) (M:nat -> bool) := 
     match i with 0 =>  (SKIP (x,0))
           | S j => rz_compare_half3 x n (ex,j) M ; QFT x;
                      (CU (ex,j) ((rz_adder x n M)));
                      (X (ex,j));
                       rz_moder' j n x ex (cut_n (div_two_spec M) n)
     end.

(* x % M circuit. *)
Definition rz_moder (n:nat) (x re ex:var) (M:nat) := 
    let i := findnum M n in 
         (Rev x; Rev re); QFT x;
          rz_moder' (S i) n x ex (nat2fb (2^i * M))
            ;( (copyto x re n)); inv_exp (rz_moder' (S i) n x ex (nat2fb (2^i * M)));
        inv_exp ( (Rev x; Rev re); QFT x).

Definition vars_for_rz_moder (size:nat) := 
  gen_vars (S size) (x_var::(y_var::(z_var::([])))).


Definition avs_for_rz_moder (size:nat) := fun x => (x/ (S size), x mod (S size)).

Definition rz_moder_out (size:nat) := 
   rz_moder (S size) x_var y_var z_var.

(* x / M  circuit. *)
Definition rz_div (n:nat) (x re ex:var) (M:nat) := 
    let i := findnum M n in 
         (Rev x); QFT x;
         rz_moder' (S i) n x ex (nat2fb (2^i * M)) ;
            (copyto ex re n); inv_exp (rz_moder' (S i) n x ex (nat2fb (2^i * M)));
        inv_exp ( (Rev x); QFT x).

Definition vars_for_rz_div (size:nat) := 
  gen_vars size (x_var::(y_var::(z_var::([])))).

Definition avs_for_rz_div (size:nat) := fun x => (x/ (S size), x mod (S size)).

Definition rz_div_out (size:nat) := 
   rz_div (S size) x_var y_var z_var.


(* x = (x % M, x / M)  circuit. *)
Definition rz_div_mod (n:nat) (x ex:var) (M:nat) := 
    let i := findnum M (n-1) in 
         (Rev x); QFT x;
            rz_moder' (S i) n x ex (nat2fb (2^i * M));
        inv_exp ( (Rev x); QFT x).

Definition vars_for_rz_div_mod (size:nat) := 
  gen_vars (S size) (x_var::(y_var::(([])))).

Definition avs_for_rz_div_mod (size:nat) := fun x => (x/ (S size), x mod (S size)).

Definition rz_div_mod_out (size:nat) := 
   rz_div_mod (S size) x_var y_var.




