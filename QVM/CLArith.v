Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import PQASM.

Local Open Scope exp_scope.
Local Open Scope nat_scope.

Local Opaque CNOT. Local Opaque CCX.

(* 
  This file contains an implementation and proof of correctness for a modular
  multiplier similar to the one defined in shor/ModMult.v, but rewritten to
  use QVM.
*)


(*********** Definitions ***********)

(* modmult adder based on classical circuits. *)
Definition MAJ a b c := CNOT c b ; CNOT c a ; CCX a b c.
Definition UMA a b c := CCX a b c ; CNOT c a ; CNOT a b.

(* The following defines n-bits MAJ and UMA circuit. 
   Eventually, MAJ;UMA circuit takes [x][y] and produce [x][(x+y) % 2 ^ n] *)
Fixpoint MAJseq' n x y c : exp :=
  match n with
  | 0 => MAJ c (y,0) (x,0)
  | S m => MAJseq' m x y c; MAJ (x, m) (y, n) (x, n)
  end.
Definition MAJseq n x y c := MAJseq' (n - 1) x y c.

Fixpoint UMAseq' n x y c : exp :=
  match n with
  | 0 => UMA c (y,0) (x,0)
  | S m => UMA (x, m) (y,n) (x, n); UMAseq' m x y c
  end.
Definition UMAseq n x y c := UMAseq' (n - 1) x y c.

Definition adder01 n x y c: exp := MAJseq n x y c; UMAseq n x y c.

(* The following implements an comparator. 
   THe first step is to adjust the adder circuit above to be
    MAJ;high_bit_manipulate;UMA.
    This is based on a binary number circuit observation that:
    To compare if x < y, we just need to do x - y, and see the high bit of the binary
    format of x - y. If the high_bit is zero, that means that x >= y;
    otherwise x < y. *)
Definition highbit n x c2 := X (x,n-1) ; X c2 ; CNOT (x,n-1) c2 ; X c2; X (x,n-1).

Definition highb01 n x y c1 c2: exp := MAJseq n x y c1; highbit n x c2 ; inv_exp (MAJseq n x y c1).

(* The following will do the negation of the first input value in the qubit sequence 00[x][y][z].
   THe actual effect is to make the sequence to be 00[-x][y][z]. *)
Fixpoint negator0 i x : exp :=
  match i with
  | 0 => SKIP (x,0)
  | S i' => negator0 i' x; X (x, i')
  end.

(* The actual comparator implementation. 
    We first flip the x positions, then use the high-bit comparator above. 
    Then, we use an inverse circuit of flipping x positions to turn the
    low bits back to store the value x.
    The actual implementation in the comparator is to do (x' + y)' as x - y,
    and then, the high-bit actually stores the boolean result of x - y < 0.  *)
Definition comparator01 n x y c1 c2 := (X c1; negator0 n x); highb01 n x y c1 c2; inv_exp (X c1; negator0 n x).

(* The implementation of a subtractor. It takes two values [x][y], and the produces
    the result of [x][y + 2^n - x]. *)
Definition subtractor01 n x y c1:= (X c1; negator0 n x); adder01 n x y c1; inv_exp (X c1; negator0 n x).

(* The implementation of a modulo adder. It takes [M][x][y], and then produces the result of [M][x+y % M][y]. 
   The modulo operation is not reversible. It will flip the high-bit to be the comparator factor.
   To flip the high-bit to zero, we use the inverse circuit of the comparator in the modulo adder to
   flip the high-bit back to zero.*)
Definition modadder21 n x y M c1 c2 := adder01 n y x c1 ; (*  adding y to x *)
                                       comparator01 n M x c1 c2; (* compare M < x + y (in position x) *)
                                       X c2 ; CU c2 (subtractor01 n M x c1) ; (* doing -M + x to x, then flip c2. *)
                                       inv_exp(comparator01 n y x c1 c2). (* compare M with x+y % M to clean c2. *)

(* Here we implement the doubler circuit based on binary shift operation.
   It assumes an n-1 value x that live in a cell of n-bits (so the high-bit must be zero). 
   Then, we shift one position, so that the value looks like 2*x in a n-bit cell. *)
Definition doubler1 y := Rshift y.

(* Another version of the mod adder only for computing [x][M] -> [2*x % M][M].
   This version will mark the high-bit, and the high-bit is not clearable.
   However, eventually, we will clean all high-bit
   by using a inverse circuit of the whole implementation. *)
Definition moddoubler01 n x M c1 c2 :=
                doubler1 x;  (comparator01 n x M c1 c2; CU c2 (subtractor01 n M x c1)).

(* The following implements the modulo adder for all bit positions in the
   binary boolean function of C. 
   For every bit in C, we do the two items:
   we first to double the factor (originally 2^(i-1) * x %M, now 2^i * x %M).
   Then, we see if we need to add the factor result to the sum of C*x%M
   based on if the i-th bit of C is zero or not.
modadder21 n x y M c1 c2
[M][x][0][0] -> [M][2^i * x % M][C^i*x % M][0]
 *)
(* A function to compile positive to a bool function. *)
(* fb_push is to take a qubit and then push it to the zero position 
        in the bool function representation of a number. *)

(* A function to compile a natural number to a bool function. *)

Fixpoint modsummer' i n M x y c1 c2 s (fC : nat -> bool) :=
  match i with
  | 0 => if (fC 0) then (adder01 n x y c1) else (SKIP (x,0))
  | S i' =>  modsummer' i' n M x y c1 c2 s fC; moddoubler01 n x M c1 c2;
          (SWAP c2 (s,i));
        (if (fC i) then (modadder21 n y x M c1 c2) else (SKIP (x,i)))
  end.
Definition modsummer n M x y c1 c2 s C := modsummer' (n - 1) n M x y c1 c2 s (nat2fb C).

(* This is the final clean-up step of the mod multiplier to do C*x %M. 
    Here, modmult_half will first clean up all high bits.  *)
Definition modmult_half n M x y c1 c2 s C := modsummer n M x y c1 c2 s C; (inv_exp (modsummer n M x y c1 c2 s 0)).

Definition modmult_full C Cinv n M x y c1 c2 s := modmult_half n M x y c1 c2 s C; inv_exp (modmult_half n M x y c1 c2 s Cinv).

Definition modmult M C Cinv n x y z s c1 c2 := (init_v n z M); modmult_full C Cinv n z x y c1 c2 s; inv_exp ( (init_v n z M)).

Definition modmult_rev M C Cinv n x y z s c1 c2 := Rev x;; modmult M C Cinv n x y z s c1 c2;; Rev x.


Definition x_var := 0. Definition y_var := 1. Definition z_var := 2. Definition s_var := 3.
Definition c_var := 4.
Definition vars_for_cl' (size:nat) := gen_vars size (x_var::(y_var::(z_var::(s_var::[])))).

Definition vars_for_cl (size:nat) := fun x => if x =? c_var then (size * 4,2,id_nat,id_nat) else vars_for_cl' size x.

Definition real_modmult_rev (M C Cinv size:nat) :=
    modmult_rev (nat2fb M) C Cinv size x_var y_var z_var s_var (c_var,0) (c_var,1).

Definition trans_modmult_rev (M C Cinv size:nat) :=
        trans_pexp (vars_for_cl size) (4*size+2) (real_modmult_rev M C Cinv size) (avs_for_arith size).

(*********** Proofs ***********)

Lemma maj_fwf : forall x y z aenv, x <> y -> y <> z -> z <> x -> exp_fwf aenv (MAJ x y z).
Proof.
  intros.
  unfold MAJ.
  constructor.
  constructor. 
  apply cnot_fwf. nor_sym.
  apply cnot_fwf. easy.
  apply ccx_fwf; easy. 
Qed.

(*
Lemma maj_well_typed : forall f tenv x y z, nor_mode f x -> nor_mode f y -> nor_mode f z
            -> right_mode_exp tenv f (MAJ x y z) -> well_typed_exp tenv (MAJ x y z).
Proof.
  intros.
  unfold MAJ in *. inv H3. inv H8.
  constructor.
  constructor. eapply cnot_well_typed. apply H2. easy. easy.
  eapply cnot_well_typed. apply H2. easy. easy.
  eapply ccx_well_typed. apply H0. easy. easy. easy.
Qed.
*)

Lemma uma_fwf : forall x y z aenv, x <> y -> y <> z -> z <> x -> exp_fwf aenv (UMA x y z).
Proof.
  intros.
  unfold UMA.
  constructor.
  constructor. 
  apply ccx_fwf; easy. 
  apply cnot_fwf. easy.
  apply cnot_fwf. easy.
Qed.

Lemma MAJ_correct :
  forall a b c f aenv,
    nor_mode f a -> nor_mode f b -> nor_mode f c ->
    a <> b -> b <> c -> a <> c ->
    exp_sem aenv (MAJ c b a) f = (((f[a |-> put_cu (f a) (majb (get_cua (f a)) (get_cua (f b)) (get_cua (f c)))])
                              [b |-> put_cu (f b) (get_cua (f b) ⊕ get_cua (f a))])
                              [c |-> put_cu (f c) (get_cua (f c) ⊕ (get_cua (f a)))]).
Proof.
  intros ? ? ? ? ? HNa HNb HNc Hab' Hbc' Hac'.
  unfold MAJ.
  simpl.
  rewrite cnot_sem.
  rewrite cnot_sem.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite ccx_sem.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite get_put_cu by assumption.
  rewrite get_put_cu by assumption.
  apply functional_extensionality.
  intros.
  bdestruct (c ==? x).
  subst.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite xorb_comm. easy.
  bdestruct (x ==? a).
  subst.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  assert ((get_cua (f a)
   ⊕ (get_cua (f a) ⊕ get_cua (f b) && get_cua (f a) ⊕ get_cua (f c)))
    = (majb (get_cua (f a)) (get_cua (f b)) (get_cua (f c)))).
  unfold majb. btauto.
  rewrite H0. easy.
  bdestruct (x ==? b).
  subst.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite xorb_comm. easy.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  easy.
  rewrite eupdate_twice_neq by nor_sym.
  apply nor_mode_up ; nor_sym.
  apply nor_mode_up_1. assumption.
  apply nor_mode_up ; nor_sym.
  apply nor_mode_up_1. assumption.
  apply nor_mode_up ; nor_sym.
  apply nor_mode_up ; nor_sym.
  1-3:nor_sym. 1-2:assumption.
  rewrite cnot_sem by assumption.
  apply nor_mode_up ; nor_sym.
  rewrite cnot_sem by assumption.
  apply nor_mode_up ; nor_sym.
Qed.

Lemma UMA_correct_partial :
  forall a b c f' fa fb fc aenv,
    nor_mode f' a -> nor_mode f' b -> nor_mode f' c ->
    a <> b -> b <> c -> a <> c ->
    get_cua (f' a) = majb fa fb fc ->
    get_cua (f' b) = (fb ⊕ fa) -> get_cua (f' c) = (fc ⊕ fa) ->
    exp_sem aenv (UMA c b a) f' = (((f'[a |-> put_cu (f' a) fa])
                  [b |-> put_cu (f' b) (fa ⊕ fb ⊕ fc)])[c |-> put_cu (f' c) fc]).
Proof.
  unfold majb. intros.
  unfold UMA.
  simpl.
  rewrite ccx_sem by (try assumption; try nor_sym).
  rewrite cnot_sem.
  rewrite cnot_sem.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite get_put_cu by assumption.
  rewrite get_put_cu by assumption.
  apply functional_extensionality.
  intros.
  bdestruct (x ==? c).
  subst.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  assert (((get_cua (f' a) ⊕ (get_cua (f' b) && get_cua (f' c))) ⊕ get_cua (f' c)) = fc).
  rewrite H5. rewrite H6. rewrite H7.
  btauto.
  rewrite H8. easy.
  bdestruct (x ==? b).
  subst.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  assert ((((get_cua (f' a) ⊕ (get_cua (f' b) && get_cua (f' c))) ⊕ get_cua (f' c))
   ⊕ get_cua (f' b)) = ((fa ⊕ fb) ⊕ fc)).
  rewrite H5. rewrite H6. rewrite H7.
  btauto.
  rewrite H9. easy.
  bdestruct (x ==? a).
  subst.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  assert ((get_cua (f' a) ⊕ (get_cua (f' b) && get_cua (f' c))) = fa).
  rewrite H5. rewrite H6. rewrite H7.
  btauto.
  rewrite H10. easy.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  easy.
  apply nor_mode_up_1. assumption.
  apply nor_mode_up ; nor_sym.
  rewrite cnot_sem.
  apply nor_mode_up_1.
  apply nor_mode_up ; nor_sym.
  apply nor_mode_up_1. assumption.
  apply nor_mode_up ; nor_sym.
  rewrite cnot_sem.
  apply nor_mode_up ; nor_sym.
  apply nor_mode_up ; nor_sym.
  apply nor_mode_up_1. assumption.
  apply nor_mode_up ; nor_sym.
Qed.

Local Transparent CNOT. Local Transparent CCX.

Lemma majseq'_fwf : forall n x y c aenv,
       x <> fst c -> y <> fst c -> x <> y -> exp_fwf aenv (MAJseq' n x y c).
Proof.
  intros.
  induction n. simpl.
  apply maj_fwf.
  iner_p. iner_p. iner_p.
  simpl.
  constructor.
  apply IHn.
  apply maj_fwf.
  1-3:iner_p.
Qed.

Lemma majseq_fwf : forall n x y c aenv,
       x <> fst c -> y <> fst c -> x <> y -> exp_fwf aenv (MAJseq n x y c).
Proof.
  intros. unfold MAJseq.
  apply majseq'_fwf; assumption.
Qed.

Lemma umaseq'_fwf : forall n x y c aenv,
       x <> fst c -> y <> fst c -> x <> y -> exp_fwf aenv (UMAseq' n x y c).
Proof.
  intros.
  induction n. simpl.
  apply uma_fwf.
  iner_p. iner_p. iner_p.
  simpl.
  constructor.
  apply uma_fwf.   1-3:iner_p.
  apply IHn.
Qed.

Lemma umaseq_fwf : forall n x y c aenv,
       x <> fst c -> y <> fst c -> x <> y -> exp_fwf aenv (UMAseq n x y c).
Proof.
  intros. unfold UMAseq.
  apply umaseq'_fwf; assumption.
Qed.

(*
Lemma umaseq'_well_typed : forall m n tenv f x y c, m < n -> nor_modes f x n -> nor_modes f y n -> nor_mode f c
            -> right_mode_exp tenv f (UMAseq' m x y c)  -> well_typed_exp tenv (UMAseq' m x y c).
Proof.
  intros.
  induction m; simpl.
  eapply uma_well_typed. apply H3. apply H2. lia. apply H1. lia.
  simpl in H4. easy.
  simpl in H4. inv H4.
  constructor. 
  eapply uma_well_typed. apply H1. lia. apply H2. lia. apply H1. lia. easy.
  apply IHm. lia. easy.
Qed.

Lemma umaseq_well_typed : forall n tenv f x y c, 0 < n -> nor_modes f x n -> nor_modes f y n -> nor_mode f c
            -> right_mode_exp tenv f (UMAseq n x y c)  -> well_typed_exp tenv (UMAseq n x y c).
Proof.
  intros. unfold UMAseq in *.
  apply (umaseq'_well_typed (n-1) n tenv f); try assumption. lia.
Qed.
*)

Lemma adder_fwf : forall n x y c aenv,
       x <> fst c -> y <> fst c -> x <> y -> exp_fwf aenv (adder01 n x y c).
Proof.
  intros. unfold adder01. constructor.
  apply majseq_fwf; assumption.
  apply umaseq_fwf; assumption.
Qed.


Lemma msm_eq1 :
  forall n i c f g,
    S i < n ->
    msma i c f g i ⊕ msma i c f g (S i) = msma (S i) c f g i.
Proof.
  intros. unfold msma. IfExpSimpl. easy.
Qed.

Lemma msm_eq2 :
  forall n i c f g,
    S i < n ->
    msmb i c f g (S i) ⊕ msma i c f g (S i) = msmb (S i) c f g (S i).
Proof.
  intros. unfold msma. unfold msmb. IfExpSimpl. btauto.
Qed.
       

Lemma msm_eq3 :
  forall n i c f g,
    S i < n ->
    majb (msma i c f g (S i)) (msmb i c f g (S i)) (msma i c f g i) = msma (S i) c f g (S i).
Proof.
  intros. unfold msma. unfold msmb. IfExpSimpl.
  simpl. unfold majb. easy.
Qed.

Definition var_prop (f:var -> nat) (x y c : var) (n:nat) : Prop :=
      n <= (f x) /\  n <= f y /\ f c = 1.

Lemma msmb_put : forall n i st x b f g, 
        S i < n -> put_cus st x (msmb (S i) b f g) n = (put_cus st x
             (msmb i b f g) n)[(x,S i) |-> put_cu (st (x,S i)) (msmb i b f g (S i) ⊕ msma i b f g (S i))].
Proof.
  intros.
  apply functional_extensionality.
  intros. destruct x0.
  bdestruct (x =? v).
  subst.
  unfold put_cus. simpl.
  bdestruct (n0 =? S i). subst.
  rewrite eupdate_index_eq.
  bdestruct (v =? v).
  bdestruct (S i <? n).
  assert ((msmb (S i) b f g (S i)) = (msmb i b f g (S i) ⊕ msma i b f g (S i))).
  erewrite msm_eq2. easy. apply H.
  rewrite H2. easy. lia. lia.
  rewrite eupdate_index_neq. simpl.
  bdestruct (v =? v).
  bdestruct (n0 <? n).
  unfold msmb.
  bdestruct (n0 <=? S i).
  bdestruct (n0 <=? i).
  easy. lia.
  bdestruct (n0 <=? i). lia. easy.
  easy. easy. intros R. inv R. lia.
  rewrite put_cus_neq. rewrite eupdate_index_neq.
  rewrite put_cus_neq. easy. assumption.
  intros R. inv R. lia. lia.
Qed.

Lemma msma_put : forall n i st x b f g, 
        S i < n -> put_cus st x (msma (S i) b f g) n = ((put_cus st x
             (msma i b f g) n)[(x,S i) |-> put_cu (st (x,S i))
                          (majb (msma i b f g (S i)) (msmb i b f g (S i)) (msma i b f g i))])
                      [(x,i) |-> put_cu (st (x,i)) (msma i b f g i ⊕ msma i b f g (S i))].
Proof.
  intros.
  apply functional_extensionality.
  intros. destruct x0.
  unfold put_cus. simpl.
  bdestruct (v =? x). subst.
  bdestruct (n0 =? i). subst.
  rewrite eupdate_index_eq.
  bdestruct (i <? n).
  unfold put_cu.
  destruct (st (x, i)).
  assert ((msma (S i) b f g i)  = (msma i b f g i ⊕ msma i b f g (S i))).
  erewrite <- msm_eq1. easy. apply H.
  rewrite H1. easy. easy. easy.
  lia.
  rewrite eupdate_index_neq.
  bdestruct (n0 =? S i). subst.
  rewrite eupdate_index_eq.
  bdestruct (S i <? n).
  unfold put_cu.
  destruct (st (x, S i)).
  assert ((msma (S i) b f g (S i))  = majb (msma i b f g (S i)) (msmb i b f g (S i)) (msma i b f g i)).
  erewrite <- msm_eq3. easy. apply H1.
  rewrite H2. easy. easy. easy. lia.
  rewrite eupdate_index_neq.
  simpl.
  bdestruct (n0 <? n).
  bdestruct (x =? x).
  assert ((msma (S i) b f g n0) = (msma i b f g n0)).
  unfold msma.
  bdestruct (n0 <? S i).
  bdestruct (n0 <? i).
  easy. lia.
  bdestruct (n0 =? S i).
  lia.
  bdestruct (n0 <? i). lia.
  bdestruct (n0 =? i). lia.
  easy.
  rewrite H4. easy.
  lia.
  bdestruct (x =? x). easy. easy.
  intros R. inv R. lia.
  intros R. inv R. lia.
  rewrite eupdate_index_neq.
  rewrite eupdate_index_neq. simpl.
  bdestruct (v =? x). lia.
  easy.
  apply iner_neq. lia.
  apply iner_neq. lia.
Qed.

Lemma msma_0 : forall f x b g n, 0 < n -> nor_modes f x n -> put_cus f x (msma 0 b (get_cus n f x) g) n =
                     f[(x,0) |-> put_cu (f (x,0)) (carry b (S 0) (get_cus n f x) g)].
Proof.
  intros.
  unfold put_cus, msma.
  apply functional_extensionality.
  intros.
  destruct x0. simpl in *.
  bdestruct (v =? x). subst.
  bdestruct (n0 <? n).
  bdestruct (n0 =? 0).
  subst.
  rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq.
  rewrite get_cus_cua.
  rewrite put_get_cu. easy.
  unfold nor_modes in *. apply H0. lia. lia.
  intros R. inv R. contradiction.
  rewrite eupdate_index_neq. easy.
  intros R. inv R. lia.
  rewrite eupdate_index_neq. easy.
  apply iner_neq. lia.
Qed.

Lemma msmb_0 : forall S f b y n, 0 < n -> nor_modes S y n -> put_cus S y (msmb 0 b f (get_cus n S y)) n =
                     S[(y,0) |-> put_cu (S (y,0)) (f 0 ⊕ (get_cua (S (y,0))))].
Proof.
  intros.
  unfold put_cus, msmb.
  apply functional_extensionality.
  intros.
  destruct x. simpl in *.
  bdestruct (v =? y). subst.
  bdestruct (n0 <? n).
  bdestruct (n0 <=? 0).
  inv H2.
  rewrite eupdate_index_eq.
  rewrite get_cus_cua. easy. lia.
  rewrite eupdate_index_neq.
  rewrite get_cus_cua.
  rewrite put_get_cu. easy.
  unfold nor_modes in *. apply H0. lia. lia.
  intros R. inv R. lia.
  rewrite eupdate_index_neq. easy.
  intros R. inv R. lia.
  rewrite eupdate_index_neq. easy.
  apply iner_neq. lia.
Qed.

Local Opaque MAJ. Local Opaque UMA.

Lemma MAJseq'_correct :
  forall i n S x y c aenv,
    0 < n -> i < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    exp_sem aenv (MAJseq' i x y c) S = 
     (put_cus 
        (put_cus (S[c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x,0)))])
                   x (msma i (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n)
          y (msmb i (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n).
Proof.
  induction i; intros.
  - simpl. rewrite MAJ_correct.
    apply functional_extensionality.
    intros.
    bdestruct (x0 ==? c).
    subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_neq_1 by assumption.
    rewrite put_cus_neq_1 by assumption.
    rewrite eupdate_index_eq. easy.
    rewrite eupdate_index_neq by nor_sym.
    destruct x0.
    bdestruct (v =? y).
    subst.
    bdestruct (n0 <? n).
    rewrite put_cus_eq by assumption.
    rewrite put_cus_neq by assumption.
    unfold msmb.
    bdestruct (n0 =? 0).
    subst.
    rewrite eupdate_index_eq.
    bdestruct (0 <=? 0).
    rewrite eupdate_index_neq by nor_sym.
    rewrite get_cus_cua by lia.
    rewrite get_cus_cua by lia.
    rewrite xorb_comm. easy.
    lia.
    bdestruct (n0 <=? 0). lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by nor_sym.
    rewrite get_cus_cua by lia.
    rewrite put_get_cu. easy.
    apply H2. easy.
    rewrite put_cus_out by lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq by nor_sym.
    easy.
    bdestruct (v =? x). subst.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq_1 by nor_sym.
    bdestruct (n0 <? n).
    rewrite put_cus_eq by assumption.
    unfold msma.
    bdestruct (n0 =? 0).
    subst.
    rewrite eupdate_index_eq.
    bdestruct (0 <? 0). lia.
    rewrite eupdate_index_neq by nor_sym.
    rewrite carry_1.
    rewrite get_cus_cua by lia.
    rewrite get_cus_cua by lia. easy.
    bdestruct (n0 <? 0). lia.
    rewrite get_cus_cua by lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by nor_sym.
    rewrite put_get_cu. easy.
    apply H1. lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_out by nor_sym.
    rewrite eupdate_index_neq by nor_sym.
    easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq by nor_sym.
    easy.
    apply H1. lia.
    apply H2. lia.
    assumption.
    tuple_eq. destruct c. simpl in *.
    tuple_eq. destruct c. simpl in *. tuple_eq.
  - simpl. rewrite (IHi n).
    rewrite MAJ_correct.
    rewrite cus_get_eq.
    rewrite cus_get_neq by lia.
    rewrite cus_get_eq.
    rewrite cus_get_neq by lia.
    rewrite cus_get_eq.
    apply functional_extensionality.
    intros.
    destruct x0.
    bdestruct (n0 <? n). 
    bdestruct (v =? x). subst.
    bdestruct (n0 =? i).
    subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_neq by lia.
    rewrite (put_cus_neq (put_cus (S [c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x, 0)))]) x
     (msma (Datatypes.S i) (get_cua (S c)) (get_cus n S x) (get_cus n S y))
     n)) by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cus_eq by lia.
    rewrite <- (msm_eq1 n).
    rewrite put_cu_twice_eq.
    easy. lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    bdestruct (n0 =? Datatypes.S i).
    subst. rewrite eupdate_index_eq.
    rewrite put_cus_neq by lia.
    rewrite (put_cus_neq (put_cus (S [c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x, 0)))]) x
     (msma (Datatypes.S i) (get_cua (S c)) (get_cus n S x) (get_cus n S y))
     n)) by lia.
    rewrite (put_cus_eq (S [c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x, 0)))])).
    rewrite (msm_eq3 n).
    rewrite put_cu_twice_eq.
    rewrite put_cus_eq by lia. easy.
    lia. lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    unfold msma.
    bdestruct (n0 <? i).
    bdestruct (n0 <? Datatypes.S i).
    easy. lia.
    bdestruct (n0 =? i). lia.
    bdestruct (n0 <? Datatypes.S i). lia.
    bdestruct (n0 =? Datatypes.S i). lia.
    easy.
    rewrite eupdate_index_neq by tuple_eq.
    bdestruct (v =? y). subst.
    bdestruct (n0 =? Datatypes.S i). subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_eq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cu_twice_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite (msm_eq2 n). easy. lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_eq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    unfold msmb.
    bdestruct (n0 <=? i).
    bdestruct (n0 <=? Datatypes.S i). easy.
    lia.
    bdestruct (n0 <=? Datatypes.S i). lia. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia. easy. lia.
    unfold nor_modes. intros.
    apply nor_mode_up. 
    destruct c. simpl in *. tuple_eq.
    apply H1. lia. lia.
    unfold nor_modes. intros.
    apply nor_mode_up. 
    destruct c. simpl in *. tuple_eq.
    apply H1. lia. lia.
    unfold nor_modes. intros.
    apply nor_mode_cus_eq.
    apply nor_mode_up.
    apply iner_neq_1. easy. 
    apply H2. lia.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up.
    apply iner_neq_1. easy. 
    apply H1. lia.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up.
    apply iner_neq_1. easy. 
    apply H2. lia.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up.
    apply iner_neq_1. easy. 
    apply H1. lia.
    tuple_eq. tuple_eq. tuple_eq.
    lia. lia.
    unfold nor_modes. intros.
    apply H1. lia.
    unfold nor_modes. intros.
    apply H2. lia.
    apply H3. lia. lia. lia.
Qed.

Local Transparent carry.

Lemma UMAseq'_correct :
  forall i n S x y c aenv,
    0 < n -> i < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    exp_sem aenv (UMAseq' i x y c) (put_cus 
        (put_cus (S[c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x,0)))])
                   x (msma i (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n)
          y (msmc i (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n) = 
         (put_cus S y (sumfb (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n).
Proof.
  induction i; intros. 
  - simpl.
    rewrite UMA_correct_partial with (fa := (get_cus n S x) 0) (fb := (get_cus n S y) 0)
                   (fc := carry (get_cua (S c)) 0 (get_cus n S x) (get_cus n S y)).
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cu_twice_eq.
    rewrite eupdate_index_neq.
    rewrite put_cus_eq by lia.
    rewrite put_cu_twice_eq.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq.
    simpl. 
    rewrite put_cus_neq_1 by nor_sym. 
    rewrite put_cus_neq_1 by nor_sym. 
    rewrite eupdate_index_eq.
    rewrite put_cu_twice_eq_1.
    apply functional_extensionality.
    intros.
    bdestruct (x0 ==? c). subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_neq_1 by lia.
    rewrite put_get_cu. easy.  assumption.
    rewrite eupdate_index_neq by nor_sym.
    destruct x0.
    bdestruct (v =? y).
    subst.
    bdestruct (n0 <? n).
    rewrite put_cus_eq by lia.
    bdestruct (n0 =? 0). subst.
    rewrite eupdate_index_eq.
    unfold sumfb. simpl.
    assert (((get_cus n S x 0 ⊕ get_cus n S y 0) ⊕ get_cua (S c)) 
          = ((get_cua (S c) ⊕ get_cus n S x 0) ⊕ get_cus n S y 0)) by btauto.
    rewrite H9. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_eq by lia.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq by nor_sym.
    unfold sumfb.
    unfold msmc.
    bdestruct (n0 <=? 0). lia. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite eupdate_index_neq by nor_sym.
    rewrite put_cus_neq_2 by lia. easy.
    bdestruct (v =? x).
    subst.
    bdestruct (n0 <? n).
    rewrite put_cus_neq by lia.
    bdestruct (n0 =? 0). subst.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_eq.
    rewrite get_cus_cua by lia.
    rewrite put_get_cu. easy. apply H1. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by nor_sym.
    rewrite put_cus_eq by lia.
    rewrite eupdate_index_neq by nor_sym.
    unfold msma.
    bdestruct ( n0 <? 0). lia.
    bdestruct (n0 =? 0). lia.
    rewrite get_cus_cua by lia.
    rewrite put_get_cu. easy. apply H1. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite eupdate_index_neq by nor_sym.
    easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq by nor_sym. easy.
    destruct c. simpl in *. tuple_eq.
    destruct c. simpl in *. tuple_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1; assumption. apply H1. lia.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1; assumption. apply H2. lia.
    destruct c.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up_1. apply H3. apply iner_neq. assumption.
    apply iner_neq_1; assumption.
    apply iner_neq_1; assumption.
    rewrite put_cus_neq by lia.
    rewrite cus_get_eq.
    unfold msma.
    bdestruct (0 <? 0). lia.
    bdestruct (0 =? 0). 
    rewrite carry_1.
    unfold carry. easy. lia. lia.
    unfold nor_modes. intros.
    apply nor_mode_up. apply iner_neq_1. assumption.
    apply H1. lia.
    rewrite cus_get_eq.
    unfold msmc.
    bdestruct (0 <=? 0).
    rewrite xorb_comm. easy.
    lia. lia.
    unfold nor_modes. intros.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1. assumption.
    apply H2. lia.
    rewrite put_cus_neq_1 by lia.
    rewrite put_cus_neq_1 by lia.
    rewrite get_cua_eq.
    simpl. rewrite get_cus_cua. easy. lia.
    assumption.
  - simpl.
    rewrite UMA_correct_partial with (fa := (get_cus n S x) (Datatypes.S i)) (fb := (get_cus n S y) (Datatypes.S i))
                   (fc := carry (get_cua (S c)) (Datatypes.S i) (get_cus n S x) (get_cus n S y)).
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cu_twice_eq.
    rewrite eupdate_index_neq.
    rewrite get_cus_cua by lia.
    rewrite put_get_cu.
    rewrite put_cus_eq by lia.
    rewrite put_cu_twice_eq.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cu_twice_eq.
    rewrite eupdate_index_neq.
    rewrite <- (IHi n) with (aenv:=aenv).
    assert (((((put_cus
        (put_cus
           (S [c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x, 0)))]) x
           (msma (Datatypes.S i) (get_cua (S c)) 
              (get_cus n S x) (get_cus n S y)) n) y
        (msmc (Datatypes.S i) (get_cua (S c)) (get_cus n S x)
           (get_cus n S y)) n) [(x, Datatypes.S i)
     |-> S (x, Datatypes.S i)]) [(y, Datatypes.S i)
    |-> put_cu (S (y, Datatypes.S i))
          ((get_cua (S (x, Datatypes.S i)) ⊕ get_cus n S y (Datatypes.S i))
           ⊕ carry (get_cua (S c)) (Datatypes.S i) 
               (get_cus n S x) (get_cus n S y))]) [
   (x, i)
   |-> put_cu (S (x, i))
         (carry (get_cua (S c)) (Datatypes.S i) (get_cus n S x)
            (get_cus n S y))])
     = (put_cus
     (put_cus (S [c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x, 0)))])
        x (msma i (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n) y
     (msmc i (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n)).
    apply functional_extensionality.
    intros.
    bdestruct (x0 ==? c). subst.
    rewrite put_cus_neq_1 by nor_sym.
    rewrite put_cus_neq_1 by nor_sym.
    rewrite eupdate_index_neq.
    rewrite eupdate_index_neq.
    rewrite eupdate_index_neq.
    rewrite put_cus_neq_1 by nor_sym.
    rewrite put_cus_neq_1 by nor_sym.
    rewrite eupdate_index_eq. easy.
    1-3:apply iner_neq_1; lia.
    destruct x0.
    bdestruct (n0 <? n).
    bdestruct (v =? x). subst.
    rewrite put_cus_neq by lia.
    bdestruct (n0 =? i). subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_eq by lia.
    rewrite eupdate_index_neq by nor_sym.
    unfold msma.
    bdestruct (i <? i). lia.
    bdestruct (i =? i). easy. lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_eq by lia.
    bdestruct (n0 =? Datatypes.S i).
    subst.
    rewrite eupdate_index_eq.
    rewrite eupdate_index_neq by nor_sym.
    unfold msma.
    bdestruct (Datatypes.S i <? i). lia.
    bdestruct (Datatypes.S i =? i). lia.
    rewrite get_cus_cua by lia.
    rewrite put_get_cu. easy.
    apply H1. lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    unfold msma.
    bdestruct (n0 <? i).
    bdestruct (n0 <? Datatypes.S i). easy. lia.
    bdestruct (n0 <? Datatypes.S i). lia.
    bdestruct (n0 =? i). lia.
    bdestruct (n0 =? Datatypes.S i). lia.
    easy.
    bdestruct (v =? y). subst.
    rewrite eupdate_index_neq by tuple_eq.
    bdestruct (n0 =? Datatypes.S i). subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_eq by lia.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq by nor_sym.
    unfold msmc.
    bdestruct (Datatypes.S i <=? i). lia.
    assert (((get_cua (S (x, Datatypes.S i)) ⊕ get_cus n S y (Datatypes.S i))
       ⊕ carry (get_cua (S c)) (Datatypes.S i) (get_cus n S x) (get_cus n S y))
     = ((carry (get_cua (S c)) (Datatypes.S i) (get_cus n S x) (get_cus n S y)
    ⊕ get_cus n S x (Datatypes.S i)) ⊕ get_cus n S y (Datatypes.S i))).
    rewrite <- (get_cus_cua n). btauto. lia.
    rewrite H11. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_eq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    unfold msmc.
    bdestruct (n0 <=? i).
    bdestruct (n0 <=? Datatypes.S i). easy.
    lia. bdestruct (n0 <=? Datatypes.S i). lia. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    easy.
    rewrite H7. rewrite IHi. easy.
    lia. lia.
    1-7:easy.
    lia.
    1-6:easy.
    apply neq_sym.
    apply iner_neq_1. assumption.
    apply neq_sym.
    apply iner_neq_1.
    assumption.
    apply H1. lia.
    apply neq_sym.
    apply iner_neq_1. assumption.
    apply nor_mode_cus_eq. 
    apply nor_mode_cus_eq. 
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H1. lia.
    apply nor_mode_cus_eq. 
    apply nor_mode_cus_eq. 
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H2. lia.
    apply nor_mode_cus_eq. 
    apply nor_mode_cus_eq. 
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H1. lia.
    1-3:tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite get_put_cu.
    unfold msma.
    bdestruct (Datatypes.S i <? Datatypes.S i). lia.
    bdestruct (Datatypes.S i =? Datatypes.S i).
    unfold majb.
    simpl. btauto. lia.
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H1. lia.
    rewrite put_cus_eq by lia.
    rewrite get_put_cu.
    unfold msmc.
    bdestruct (Datatypes.S i <=? Datatypes.S i).
    btauto.
    lia.
    apply nor_mode_cus_eq. 
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H2. lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite get_put_cu.
    unfold msma.
    bdestruct (i <? Datatypes.S i). easy. lia.
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H1. lia.
Qed.

(* adder correctness proofs. *)
Lemma adder01_correct_fb :
  forall n S x y c aenv,
    0 < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    exp_sem aenv (adder01 n x y c) S = (put_cus S y (sumfb (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n).
Proof.
  intros. unfold adder01. unfold MAJseq, UMAseq.
  simpl.
  rewrite MAJseq'_correct with (n := n). 
  assert (forall S', put_cus S' y (msmb (n - 1) (get_cua (S c)) 
        (get_cus n S x) (get_cus n S y)) n = put_cus S' y (msmc (n - 1) (get_cua (S c)) 
        (get_cus n S x) (get_cus n S y)) n).
  intros. apply put_cus_sem_eq. intros.
  unfold msmb,msmc.
  bdestruct (m <=? n - 1). easy. lia.
  rewrite H6.
  apply UMAseq'_correct. assumption. lia. 1 - 6: assumption.
  apply H. lia. 1 - 6 : assumption.
Qed.
(*
Lemma adder01_nor_fb :
  forall n env S S' x y c,
    0 < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    S' = (put_cus S y (sumfb (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n) ->
    exp_sem env S (adder01 n x y c) S'.
Proof.
  intros.
  subst. apply adder01_correct_fb. 1-7:assumption.
Qed.

Check put_cus.
*)
Definition reg_push (f : posi -> val)  (x : var) (v:nat) (n : nat) : posi -> val := put_cus f x (nat2fb v) n.


Lemma reg_push_exceed :
  forall n x v f,
    reg_push f x v n = reg_push f x (v mod 2^n) n.
Proof.
  intros. unfold reg_push. unfold nat2fb.
  apply put_cus_sem_eq. intros.
  rewrite Nofnat_mod. 2: apply Nat.pow_nonzero; lia.
  rewrite Nofnat_pow. simpl.
  do 2 rewrite N2fb_Ntestbit. rewrite N.mod_pow2_bits_low. easy. lia.
Qed.

(* The following two lemmas show the correctness of the adder implementation based on MAJ;UMA circuit. 
   The usage of the adder is based on the carry0 lemma. *)
Lemma adder01_correct_carry0 :
  forall n (S S' S'' : posi -> val) x y c v1 v2 aenv,
    0 < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    v1 < 2^n -> v2 < 2^n ->
    S' = reg_push (reg_push (S[c |-> put_cu (S c) false]) x v1 n) y v2 n ->
    S'' = reg_push (reg_push (S[c |-> put_cu (S c) false]) x v1 n) y (v1+v2) n ->
    exp_sem aenv (adder01 n x y c) S' = S''.
Proof.
  intros. unfold reg_push in *. rewrite adder01_correct_fb; try assumption.
  subst. destruct c. simpl in *. rewrite cus_get_neq by lia.
  rewrite cus_get_neq by lia.
  rewrite eupdate_index_eq. 
  rewrite get_put_cu by easy.
  rewrite get_cus_put_neq by lia.
  rewrite get_cus_put_eq.
  rewrite get_cus_put_eq.
  rewrite sumfb_correct_carry0.
  rewrite put_cus_twice_eq. easy. easy.
  unfold nor_modes. intros. 
  apply nor_mode_cus_eq. apply nor_mode_up. iner_p.
  apply H1. easy. easy.
  unfold nor_modes. intros. apply nor_mode_up. iner_p.
  apply H0. easy. subst.
  unfold nor_modes. intros. 
  repeat apply nor_mode_cus_eq. apply nor_mode_up. iner_p.
  apply H0. easy. subst.
  unfold nor_modes. intros. 
  repeat apply nor_mode_cus_eq. apply nor_mode_up. iner_p.
  apply H1. easy. subst.
  destruct c.
  repeat apply nor_mode_cus_eq.
  apply nor_mode_up_1. easy.
Qed.

Lemma adder01_correct_carry1 :
  forall n (S S' S'' : posi -> val) x y c v1 v2 aenv,
    0 < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    v1 < 2^n -> v2 < 2^n ->
    S' = reg_push (reg_push (S[c |-> put_cu (S c) true]) x v1 n) y v2 n ->
    S'' = reg_push (reg_push (S[c |-> put_cu (S c) true]) x v1 n) y (v1+v2+1) n ->
    exp_sem aenv (adder01 n x y c) S'  = S''.
Proof.
  intros. unfold reg_push in *. rewrite adder01_correct_fb; try assumption.
  subst. destruct c. simpl in *. rewrite cus_get_neq by lia.
  rewrite cus_get_neq by lia.
  rewrite eupdate_index_eq. 
  rewrite get_put_cu by easy.
  rewrite get_cus_put_neq by lia.
  rewrite get_cus_put_eq.
  rewrite get_cus_put_eq.
  rewrite sumfb_correct_carry1.
  rewrite put_cus_twice_eq. easy. easy.
  unfold nor_modes. intros. 
  apply nor_mode_cus_eq. apply nor_mode_up. iner_p.
  apply H1. lia. easy.
  unfold nor_modes. intros. 
  apply nor_mode_up. iner_p. apply H0. easy.
  subst.
  unfold nor_modes. intros. 
  repeat apply nor_mode_cus_eq. apply nor_mode_up. iner_p.
  apply H0. easy. 
  subst.
  unfold nor_modes. intros. 
  repeat apply nor_mode_cus_eq. apply nor_mode_up. iner_p.
  apply H1. easy. 
  subst.
  destruct c.
  repeat apply nor_mode_cus_eq.
  apply nor_mode_up_1. easy.
Qed.

Local Opaque adder01.

Lemma negator0_fwf : forall n x aenv, exp_fwf aenv (negator0 n x).
Proof.
  intros. induction n;simpl.
  constructor. constructor. easy. constructor.
Qed.

Lemma negatem_put_get : forall i n f x, S i <= n ->
       put_cus f x (negatem (S i) (get_cus n f x)) n =
              (put_cus f x (negatem i (get_cus n f x)) n)[(x,i) |-> put_cu (f (x,i)) (¬ (get_cua (f (x,i))))].
Proof.
  intros.
  unfold negatem.
  apply functional_extensionality. intros.
  destruct x0.
  bdestruct (x =? v).
  bdestruct (n0 =? i).
  subst.
  rewrite eupdate_index_eq.
  unfold put_cus. simpl.
  bdestruct (v =? v).
  bdestruct (i <? n).
  bdestruct (i <? S i).
  rewrite get_cus_cua. easy. lia.
  lia. lia. lia.
  rewrite eupdate_index_neq.
  unfold put_cus. simpl.
  bdestruct (v =? x).
  bdestruct (n0 <? n).
  bdestruct (n0 <? S i).
  bdestruct (n0 <? i). easy.
  lia.
  bdestruct (n0 <? i). lia. easy.
  easy. easy.
  intros R. inv R. lia.
  rewrite put_cus_neq.
  rewrite eupdate_index_neq.
  rewrite put_cus_neq.
  easy. 
  lia.
  intros R. inv R. lia. lia.
Qed.

Lemma negator0_correct :
  forall i n f x aenv,
    0 < n ->
    i <= n ->
    nor_modes f x n ->
    exp_sem aenv (negator0 i x) f = (put_cus f x (negatem i (get_cus n f x)) n).
Proof.
 induction i; intros.
 simpl.
 assert ((negatem 0 (get_cus n f x)) = get_cus n f x).
  apply functional_extensionality. intros.
 unfold negatem. bdestruct (x0 <? 0).
 lia. easy.
 rewrite H2.
 rewrite put_get_cus_eq. constructor. assumption.
 simpl. 
 rewrite (IHi n) ; try lia; try easy.
 rewrite negatem_put_get.
 assert (exchange (put_cus f x (negatem i (get_cus n f x)) n (x, i)) = 
            put_cu (f (x, i)) (¬ (get_cua (f (x, i))))).
 unfold negatem. simpl.
 unfold put_cus. simpl. bdestruct (x=?x).
 bdestruct (i<?n). bdestruct (i <? i). lia.
 assert (nor_mode f (x,i)).
 apply H1. easy.
 unfold nor_mode in H5. destruct (f (x,i)) eqn:eq1.
 rewrite get_cus_cua.
 unfold exchange,put_cu,get_cua. rewrite eq1. easy. lia. lia. lia. lia. lia.
 rewrite H2. easy. lia.
Qed.

(*
Lemma negator0_nor :
  forall i n env f f' x,
    0 < n ->
    i <= n ->
    nor_modes f x n ->
    f' = (put_cus f x (negatem i (get_cus n f x)) n) ->
    exp_sem env f (negator0 i x) f'.
Proof.
 intros. subst. apply negator0_correct. 1 - 3: assumption.
Qed.
*)
(* The correctness represents the actual effect of flip all bits for the number x.
   The effect is to make the x number positions to store the value  2^n - 1 - x. *)
Lemma negator0_sem :
  forall n x v f aenv,
    0 < n ->
    v < 2^n -> nor_modes f x n ->
    exp_sem aenv (negator0 n x) (reg_push f x v n) = reg_push f x (2^n - 1 - v) n.
Proof.
  intros. unfold reg_push in *.
  rewrite (negator0_correct n n); try assumption.
  rewrite put_cus_twice_eq.
  rewrite get_cus_put_eq; try easy.
  rewrite negatem_arith ; try easy. lia.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq. apply H1. lia.
Qed.

Local Opaque CNOT. Local Opaque CCX.

Definition no_equal (x y:var) (c1 c2 : posi) : Prop := x <> y /\ x <> fst c1 /\  x <> fst c2 
                   /\ y <> fst c1 /\ y <> fst c2 /\ c1 <> c2.

Lemma highbit_fwf : forall n x c2 aenv, fst c2 <> x -> exp_fwf aenv (highbit n x c2).
Proof.
 intros. repeat constructor.
 apply cnot_fwf. destruct c2. iner_p.
Qed.

Lemma highb01_fwf : forall n x y c1 c2 aenv, no_equal x y c1 c2 -> exp_fwf aenv (highb01 n x y c1 c2).
Proof.
  intros. unfold no_equal in H.  destruct H as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  constructor. constructor.
  apply majseq_fwf; try assumption.
  apply highbit_fwf; try iner_p.
  apply fwf_inv_exp.
  apply majseq_fwf; try assumption.
Qed.

Lemma exp_sem_seq : forall e1 e2 f aenv, exp_sem aenv (e1 ; e2) f = exp_sem aenv e2 (exp_sem aenv e1 f).
Proof.
intros. simpl. easy.
Qed.

Lemma exp_sem_x : forall p f aenv, exp_sem aenv (X p) f = (f[p |-> exchange (f p)]).
Proof.
intros. simpl. easy.
Qed.

Lemma put_cu_exchange : forall (f : posi -> val) p v, nor_mode f p ->  put_cu (exchange (f p)) v = put_cu (f p) v.
Proof.
 intros. unfold exchange. unfold nor_mode in H.
 destruct (f p) eqn:eq1. simpl. easy. lia. lia.
Qed.

Lemma highbit_correct :
  forall n f x c2 aenv,
    0 < n -> fst c2 <> x -> nor_mode f c2 -> nor_modes f x n -> get_cua (f c2) = false ->
    exp_sem aenv (highbit n x c2) f = f[c2 |-> put_cu (f c2) ((majb true false (get_cus n f x (n-1))) ⊕ true)].
Proof.
 intros. unfold highbit. repeat rewrite exp_sem_seq.
 rewrite exp_sem_x with (f:=f). rewrite exp_sem_x with (f := (f [(x, n - 1) |-> exchange (f (x, n - 1))])).
 destruct c2.
 rewrite eupdate_index_neq by iner_p.
 rewrite cnot_sem.
 rewrite eupdate_index_eq.
 rewrite eupdate_index_neq by iner_p. 
 rewrite eupdate_index_eq.
 rewrite eupdate_twice_eq.
 rewrite put_cu_exchange by easy.
 assert (get_cua (exchange (f (v, n0))) = true).
 unfold get_cua in H3. unfold nor_mode in H1.
 unfold get_cua,exchange.
 destruct (f (v, n0)) eqn:eq1. subst. easy. lia. lia.
 rewrite H4.
 unfold majb. bt_simpl.
 rewrite exp_sem_x with (p := (v, n0)) by easy.
 rewrite eupdate_twice_eq by easy.
 rewrite eupdate_index_eq.
 rewrite exp_sem_x by easy.
 rewrite eupdate_twice_neq by iner_p.
 rewrite eupdate_twice_eq.
 rewrite eupdate_index_neq by iner_p.
 rewrite eupdate_index_eq.
 rewrite exchange_twice_same.
 apply eupdate_same_1.
 rewrite eupdate_same. easy. easy.
 unfold nor_modes in H2. specialize (H2 (n-1)).
 assert (n - 1 < n) by lia. specialize (H2 H5).
 unfold nor_mode in H1.
 unfold nor_mode in H2.
 unfold exchange.
 rewrite get_cus_cua.
 destruct (f (x, n - 1)) eqn:eq1. simpl.
 unfold put_cu. destruct (f (v, n0)) eqn:eq2.
 assert ((¬ (¬ (¬ b))) = (¬ b)) by btauto. rewrite H6. easy. lia. lia. lia. lia. easy.
 apply nor_mode_up. iner_p.
 unfold nor_mode.
 rewrite eupdate_index_eq.
 unfold nor_modes in H3. assert (n -1 < n) by lia.
 specialize (H2 (n-1) H4). unfold nor_mode in H2.
 unfold exchange.
 destruct (f (x, n - 1)) eqn:eq1. easy. lia. lia.
 unfold nor_mode.
 rewrite eupdate_index_eq.
 unfold nor_mode in H1.
 unfold exchange.
 destruct (f (v, n0)) eqn:eq1. easy. lia. lia.
Qed.

Lemma highbit_correct_2 :
  forall n f x c2 aenv,
    0 < n -> fst c2 <> x -> nor_mode f c2 -> nor_modes f x n -> get_cua (f c2) = true ->
    exp_sem aenv (highbit n x c2) f = f[c2 |-> put_cu (f c2) ((majb true false (get_cus n f x (n-1))))].
Proof.
 intros. unfold highbit. repeat rewrite exp_sem_seq.
 rewrite exp_sem_x with (f:=f). rewrite exp_sem_x with (f := (f [(x, n - 1) |-> exchange (f (x, n - 1))])).
 destruct c2.
 rewrite eupdate_index_neq by iner_p.
 rewrite cnot_sem.
 rewrite eupdate_index_eq.
 rewrite eupdate_index_neq by iner_p. 
 rewrite eupdate_index_eq.
 rewrite eupdate_twice_eq.
 rewrite put_cu_exchange by easy.
 assert (get_cua (exchange (f (v, n0))) = false).
 unfold get_cua in H3. unfold nor_mode in H1.
 unfold get_cua,exchange.
 destruct (f (v, n0)) eqn:eq1. subst. easy. lia. lia.
 rewrite H4.
 unfold majb. bt_simpl.
 rewrite exp_sem_x with (p := (v, n0)) by easy.
 rewrite eupdate_twice_eq by easy.
 rewrite eupdate_index_eq.
 rewrite exp_sem_x by easy.
 rewrite eupdate_twice_neq by iner_p.
 rewrite eupdate_twice_eq.
 rewrite eupdate_index_neq by iner_p.
 rewrite eupdate_index_eq.
 rewrite exchange_twice_same.
 apply eupdate_same_1.
 rewrite eupdate_same. easy. easy.
 unfold nor_modes in H2. specialize (H2 (n-1)).
 assert (n - 1 < n) by lia. specialize (H2 H5).
 unfold nor_mode in H1.
 unfold nor_mode in H2.
 unfold exchange.
 rewrite get_cus_cua.
 destruct (f (x, n - 1)) eqn:eq1. simpl.
 unfold put_cu. destruct (f (v, n0)) eqn:eq2.
 assert (((¬ (¬ b))) = (b)) by btauto. rewrite H6. easy. lia. lia. lia. lia. easy.
 apply nor_mode_up. iner_p.
 unfold nor_mode.
 rewrite eupdate_index_eq.
 unfold nor_modes in H3. assert (n -1 < n) by lia.
 specialize (H2 (n-1) H4). unfold nor_mode in H2.
 unfold exchange.
 destruct (f (x, n - 1)) eqn:eq1. easy. lia. lia.
 unfold nor_mode.
 rewrite eupdate_index_eq.
 unfold nor_mode in H1.
 unfold exchange.
 destruct (f (v, n0)) eqn:eq1. easy. lia. lia.
Qed.

Local Opaque highbit.

Lemma highb01_correct :
  forall n tenv f x y c1 c2 aenv,
    0 < n -> no_equal x y c1 c2 ->
    nor_mode f c2 -> nor_mode f c1 -> nor_modes f x n -> nor_modes f y n -> 
    get_cua (f c2) = false -> well_typed_exp tenv (MAJseq n x y c1) -> right_mode_env aenv tenv f ->
    exp_sem aenv (highb01 n x y c1 c2) f =
      f[c2 |-> put_cu (f c2) ((majb true false (carry (get_cua (f c1)) n (get_cus n f x) (get_cus n f y))) ⊕ true)].
Proof.
  intros.
  unfold highb01. unfold no_equal in H0.
  destruct H0 as [V1 [V2 [V3 [V4 [V5 V6]]]]].
  destruct c1. destruct c2.
  simpl. unfold MAJseq. rewrite (MAJseq'_correct (n-1) n); (try easy; try lia).
  rewrite highbit_correct; try lia.
  rewrite put_cu_cus. rewrite put_cu_cus.
  rewrite get_cus_cua by lia.
  rewrite put_cus_neq by lia.
  rewrite cus_get_eq; try lia.
  rewrite eupdate_index_neq by iner_p.
  erewrite inv_exp_reverse. easy.
  apply majseq'_fwf ; try easy. apply H6.
  apply right_mode_exp_up_same. apply H7.
  rewrite (MAJseq'_correct (n-1) n); (try easy; try lia).
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite get_cus_up by iner_p.
  rewrite eupdate_twice_neq by iner_p.
  rewrite put_cus_update_flip by iner_p.
  rewrite put_cus_update_flip by iner_p.
  apply eupdate_same_1. easy.
  unfold msma. bdestruct (n - 1 <? n - 1). lia.
  bdestruct (n - 1 =? n - 1).
  assert ((S (n - 1)) = n) by lia. rewrite H9. easy. lia.
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p. apply H3. easy.
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p. apply H4. easy.
  apply nor_mode_up ; iner_p. 
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p. apply H3. easy.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p. apply H3. easy.
  repeat rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_neq by iner_p. easy.
Qed.

Lemma highb01_correct_2 :
  forall n tenv f x y c1 c2 aenv,
    0 < n -> no_equal x y c1 c2 ->
    nor_mode f c2 -> nor_mode f c1 -> nor_modes f x n -> nor_modes f y n -> 
    get_cua (f c2) = true -> well_typed_exp tenv (MAJseq n x y c1) -> right_mode_env aenv tenv f ->
    exp_sem aenv (highb01 n x y c1 c2) f =
      f[c2 |-> put_cu (f c2) ((majb true false (carry (get_cua (f c1)) n (get_cus n f x) (get_cus n f y))))].
Proof.
  intros.
  unfold highb01. unfold no_equal in H0.
  destruct H0 as [V1 [V2 [V3 [V4 [V5 V6]]]]].
  destruct c1. destruct c2.
  simpl. unfold MAJseq. rewrite (MAJseq'_correct (n-1) n); (try easy; try lia).
  rewrite highbit_correct_2; try lia.
  rewrite put_cu_cus. rewrite put_cu_cus.
  rewrite get_cus_cua by lia.
  rewrite put_cus_neq by lia.
  rewrite cus_get_eq; try lia.
  rewrite eupdate_index_neq by iner_p.
  erewrite inv_exp_reverse. easy.
  apply majseq'_fwf ; try easy. apply H6.
  apply right_mode_exp_up_same. apply H7.
  rewrite (MAJseq'_correct (n-1) n); (try easy; try lia).
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite get_cus_up by iner_p.
  rewrite eupdate_twice_neq by iner_p.
  rewrite put_cus_update_flip by iner_p.
  rewrite put_cus_update_flip by iner_p.
  apply eupdate_same_1. easy.
  unfold msma. bdestruct (n - 1 <? n - 1). lia.
  bdestruct (n - 1 =? n - 1).
  assert ((S (n - 1)) = n) by lia. rewrite H9. easy. lia.
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p. apply H3. easy.
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p. apply H4. easy.
  apply nor_mode_up ; iner_p. 
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p. apply H3. easy.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p. apply H3. easy.
  repeat rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_neq by iner_p. easy.
Qed.

Local Opaque highb01.

Lemma negations_aux :
  forall n x c v S v' r aenv,
    0 < n -> fst c <> x ->
    v < 2^n ->
    v' = nval false r -> nor_modes S x n ->
    exp_sem aenv (X c; negator0 n x) (reg_push (S[c |-> v']) x v n) 
           = (reg_push (S[c |-> nval true r]) x (2^n - 1 - v) n).
Proof.
  intros; subst. simpl.
  assert (((reg_push (S [c |-> nval false r]) x v n) [c
   |-> exchange (reg_push (S [c |-> nval false r]) x v n c)]) 
        = reg_push (S [c |-> nval true r]) x v n).
  unfold reg_push.
  rewrite <- put_cus_update_flip by easy.
  rewrite eupdate_twice_eq. 
  destruct c. simpl in *.
  rewrite put_cus_neq by lia.
  rewrite eupdate_index_eq.
  unfold exchange. simpl. easy.
  rewrite H2.
  rewrite (negator0_sem n) ; try easy.
  unfold nor_modes. intros.
  apply nor_mode_up. destruct c. iner_p. apply H3. easy.
Qed.

Lemma pow2_predn :
  forall n x,
    x < 2^(n-1) -> x < 2^n.
Proof.
  intros. destruct n. simpl in *. lia.
  simpl in *. rewrite Nat.sub_0_r in H. lia.
Qed.

Lemma carry_leb_equiv_true :
  forall n x y,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    x <= y ->
    carry true n (nat2fb (2^n - 1 - x)) (nat2fb y) = true.
Proof.
  intros. unfold nat2fb. specialize (carry_add_eq_carry1 n (N.of_nat (2 ^ n - 1 - x)) (N.of_nat y)) as G.
  do 2 apply xorb_move_l_r_2 in G. rewrite G.
  do 2 (pattern N2fb at 1; rewrite N2fb_Ntestbit).
  rewrite Ntestbit_lt_pow2n.
  2:{ replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow. apply pow2_predn in H1. lia.
  }
  rewrite Ntestbit_lt_pow2n.
  2:{ replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
      assert (0 < 2^n) by (apply pow_positive; easy). lia.
  }
  replace 1%N with (N.of_nat 1) by easy. do 2 rewrite <- Nnat.Nat2N.inj_add.
  rewrite N2fb_Ntestbit. rewrite Ntestbit_in_pow2n_pow2Sn. btauto.
  split.
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
  replace (2^n) with (2^(n-1) + 2^(n-1)). lia.
  destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
  rewrite <- Nnat.Nat2N.inj_succ.
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
  replace (2^(S n)) with (2^n + 2^n) by (simpl; lia).
  replace (2^n) with (2^(n-1) + 2^(n-1)). lia.
  destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
Qed.

Lemma carry_leb_equiv_false :
  forall n x y,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    x > y ->
    carry true n (nat2fb (2^n - 1 - x)) (nat2fb y) = false.
Proof.
  intros. unfold nat2fb. specialize (carry_add_eq_carry1 n (N.of_nat (2 ^ n - 1 - x)) (N.of_nat y)) as G.
  do 2 apply xorb_move_l_r_2 in G. rewrite G.
  do 2 (pattern N2fb at 1; rewrite N2fb_Ntestbit).
  rewrite Ntestbit_lt_pow2n.
  2:{ replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow. apply pow2_predn in H1. lia.
  }
  rewrite Ntestbit_lt_pow2n.
  2:{ replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
      assert (0 < 2^n) by (apply pow_positive; easy). lia.
  }
  replace 1%N with (N.of_nat 1) by easy. do 2 rewrite <- Nnat.Nat2N.inj_add.
  rewrite N2fb_Ntestbit. rewrite Ntestbit_lt_pow2n. btauto.
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
  replace (2^n) with (2^(n-1) + 2^(n-1)). lia.
  destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
Qed.

Lemma carry_leb_equiv :
  forall n x y,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    carry true n (nat2fb (2^n - 1 - x)) (nat2fb y) = (x <=? y).
Proof.
  intros. bdestruct (x <=? y). apply carry_leb_equiv_true; easy. apply carry_leb_equiv_false; easy.
Qed.

Lemma pow2_low_bit_false : forall n i, i < n -> nat2fb (2^n) i = false.
Proof.
 intros. unfold nat2fb.
 rewrite N2fb_Ntestbit.
 assert (N.of_nat i < N.of_nat n)%N.
 lia.
 specialize (N.mul_pow2_bits_low 1 (N.of_nat n) (N.of_nat i) H0) as eq1.
 assert (1 * 2 ^ N.of_nat n = 2 ^ N.of_nat n)%N by lia.
 rewrite H1 in eq1.
 assert (2%N = (N.of_nat 2)) by easy. rewrite H2 in eq1.
 rewrite Nofnat_pow.
 rewrite eq1. easy.
Qed.

Lemma carry_false_lt: forall n f g,
    (forall i, i <= n -> g i = false) -> 
    carry false n f g = false.
Proof.
  induction n;intros.
  simpl. easy.
  simpl.
  rewrite IHn.
  rewrite H by lia. btauto.
  intros. rewrite H. easy. lia.
Qed.

Lemma low_bit_same : forall n x, 0 < n -> x < 2^n -> 
    (forall i, i < n -> nat2fb (x + 2^n) i = nat2fb x i).
Proof.
  intros.
  rewrite <- sumfb_correct_carry0.
  unfold sumfb.
  rewrite pow2_low_bit_false by easy. bt_simpl.
  rewrite carry_false_lt. btauto.
  intros.
  apply pow2_low_bit_false. lia.
Qed.

Lemma carry_low_bit_same : forall m b n x g, m <= n -> 0 < n -> x < 2^n -> 
    carry b m (nat2fb (x + 2^n)) g = carry b m (nat2fb x) g.
Proof.
  induction m;intros. simpl. easy.
  simpl.
  rewrite IHm by lia.
  rewrite low_bit_same by lia. easy.
Qed.


Lemma majb_carry_s_eq : forall n x y, 0 < n -> x < 2^n -> y < 2^n ->
      majb true false (carry true n (nat2fb (2^n - 1 - x)) (nat2fb y)) 
       = carry true (S n) (nat2fb ((2^n - 1 - x) + 2^n)) (nat2fb y).
Proof.
  intros. simpl. unfold majb.
  assert (nat2fb (2 ^ n - 1 - x + 2 ^ n) n = true).
  unfold nat2fb. rewrite N2fb_Ntestbit.
  rewrite Ntestbit_in_pow2n_pow2Sn. easy.
  split. 
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow. lia.
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nnat.Nat2N.inj_succ. 
  rewrite <- Nofnat_pow.
  rewrite Nat.pow_succ_r. lia. lia.
  rewrite H2.
  assert (nat2fb y n = false).
  unfold nat2fb. rewrite N2fb_Ntestbit.
  rewrite Ntestbit_lt_pow2n. easy.
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow. lia.
  rewrite H3. rewrite carry_low_bit_same. easy.
  easy. lia. lia.
Qed.

Lemma reg_push_update_flip : forall n f g x c v, fst c <> x 
         -> reg_push (f[c |-> v]) x g n = (reg_push f x g n)[c |-> v].
Proof.
  intros. unfold reg_push.
  rewrite put_cus_update_flip. easy. lia.
Qed.

Lemma reg_push_twice_neq : forall (f:posi -> val) (x y:var) g1 g2 n, 
              x <> y -> (reg_push (reg_push f x g1 n) y g2 n)
                          = (reg_push (reg_push f y g2 n) x g1 n).
Proof.
 intros. unfold reg_push. rewrite put_cus_twice_neq. easy. lia.
Qed.


Lemma comparator01_fwf : forall n x y c1 c2 aenv, no_equal x y c1 c2 ->
               exp_fwf aenv (comparator01 n x y c1 c2).
Proof.
  intros. unfold comparator01.
  constructor. constructor. constructor. constructor.
  apply negator0_fwf. 
  apply highb01_fwf. easy.
  apply fwf_inv_exp.
  constructor. constructor. apply negator0_fwf. 
Qed.

Lemma comparator01_correct :
  forall tenv aenv n x y c1 c2 v1 v2 f f' f'',
    0 < n -> 
    v1 < 2^n -> v2 < 2^n -> no_equal x y c1 c2 ->
    nor_modes f x n -> nor_modes f y n -> nor_mode f c1 -> nor_mode f c2 -> well_typed_exp tenv (MAJseq n x y c1) ->
    well_typed_exp tenv (X c1) -> well_typed_exp tenv (negator0 n x) -> right_mode_env aenv tenv f ->
    f' = reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) false]) x v1 n) y v2 n ->
    f'' = reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) (¬(v1 <=? v2))]) x v1 n) y v2 n ->
    exp_sem aenv (comparator01 n x y c1 c2) f' = f''.
Proof.
  intros.
  unfold comparator01. remember ((X c1; negator0 n x)) as negations. simpl. subst.
  unfold no_equal in *.
  destruct H2 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  destruct c1. destruct c2.
  rewrite eupdate_twice_neq by iner_p.
  rewrite reg_push_twice_neq by easy.
  rewrite reg_push_update_flip by iner_p.
  assert (exists b r, f (v, n0) = nval b r).
  unfold nor_mode in H5. destruct (f (v, n0)). exists b. exists r. easy. lia. lia.
  destruct H2. destruct H2.
  rewrite negations_aux with (r := x1); try easy.
  unfold reg_push.
  rewrite highb01_correct with (tenv := tenv) (aenv := aenv); try easy.
  assert (put_cus
  (put_cus
     ((f [(v, n0) |-> put_cu (f (v, n0)) false]) [
      (v0, n1) |-> put_cu (f (v0, n1)) (¬(v1 <=? v2))]) x 
     (nat2fb v1) n) y (nat2fb v2) n
      = (reg_push
    ((reg_push
     (f[
      (v0, n1) |-> put_cu (f (v0, n1)) (¬(v1 <=? v2))]) y v2 n)[(v, n0) |-> put_cu (f (v, n0)) false]) x v1 n)).
  unfold reg_push.
  rewrite eupdate_twice_neq by iner_p.
  rewrite put_cus_twice_neq by lia. 
  rewrite put_cus_update_flip by iner_p. easy. 
  rewrite H11. clear H11.
  erewrite inv_exp_reverse. easy.
  constructor. constructor. apply negator0_fwf.
  constructor. apply H8. easy. 
  unfold reg_push.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same_1 ; try easy.
  apply nor_mode_cus_eq.
  apply nor_mode_up. iner_p. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. apply H10.
  Check negations_aux.
  rewrite negations_aux with (r := x1); try easy.
  repeat rewrite cus_get_neq by iner_p.
  rewrite eupdate_index_eq.
  rewrite get_cus_put_eq; try lia.
  rewrite get_cus_put_neq; try lia.
  rewrite <- put_cus_update_flip with (f := (f [(v0, n1) |-> put_cu (f (v0, n1)) false])).
  rewrite get_cus_put_eq; try lia.
  assert ((get_cua (nval true x1)) = true). unfold get_cua. easy.
  rewrite H11.
  rewrite majb_carry_s_eq.
  specialize (carry_leb_equiv (n+1) v1 v2) as eq2.
  assert (n+1 -1 = n) by lia.
  rewrite H12 in eq2. clear H12.
  assert ((n + 1) = S n) by lia.
  rewrite H12 in eq2. clear H12. 
  rewrite Nat.pow_succ_r in eq2.
  assert (2 * 2 ^ n - 1 - v1 = 2 ^ n - 1 - v1 + 2 ^ n) by lia.
  rewrite H12 in eq2. rewrite eq2.
  rewrite put_cu_cus.
  rewrite put_cu_cus.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_eq.
  rewrite double_put_cu.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite eupdate_twice_neq by iner_p.
  rewrite eupdate_twice_eq.
  rewrite put_cus_update_flip by iner_p.
  bt_simpl. unfold reg_push. easy.
  1-7:lia. 
  unfold nor_modes. intros.
  repeat apply nor_mode_up ; iner_p. apply H4. easy.
  iner_p.
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p.
  apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p. apply H3. easy. iner_p.
  rewrite H2. unfold put_cu. easy.
  unfold reg_push.
  unfold nor_modes. intros. apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p.
  apply H3. easy.
  apply nor_mode_cus_eq. apply nor_mode_up ; iner_p.
  apply nor_mode_cus_eq. apply nor_mode_up_1; iner_p.
  apply nor_mode_cus_eq.
  unfold nor_mode. rewrite eupdate_index_eq. lia.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply H3. easy.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply H4. easy.
  rewrite put_cus_neq; iner_p.
  rewrite eupdate_index_neq by iner_p.
  rewrite put_cus_neq; iner_p.
  rewrite eupdate_index_eq.
  rewrite get_put_cu. easy. apply H6.
  apply right_mode_exp_put_cus_same.
  assert (nval true x1 = put_cu (f (v,n0)) true).
  rewrite H2. easy. rewrite H11.
  apply right_mode_exp_up_same_1.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy. iner_p.
  rewrite H2. easy.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply H3. easy.
Qed.

Lemma comparator01_correct_true :
  forall tenv aenv n x y c1 c2 v1 v2 f f' f'',
    0 < n -> 
    v1 < 2^n -> v2 < 2^n -> no_equal x y c1 c2 ->
    nor_modes f x n -> nor_modes f y n -> nor_mode f c1 -> nor_mode f c2 -> well_typed_exp tenv (MAJseq n x y c1) ->
    well_typed_exp tenv (X c1) -> well_typed_exp tenv (negator0 n x) -> right_mode_env aenv tenv f ->
    f' = reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) true]) x v1 n) y v2 n ->
    f'' = reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) (v1 <=? v2)]) x v1 n) y v2 n ->
    exp_sem aenv (comparator01 n x y c1 c2) f' = f''.
Proof.
  intros.
  unfold comparator01. remember ((X c1; negator0 n x)) as negations. simpl. subst.
  unfold no_equal in *.
  destruct H2 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  destruct c1. destruct c2.
  rewrite eupdate_twice_neq by iner_p.
  rewrite reg_push_twice_neq by easy.
  rewrite reg_push_update_flip by iner_p.
  assert (exists b r, f (v, n0) = nval b r).
  unfold nor_mode in H5. destruct (f (v, n0)). exists b. exists r. easy. lia. lia.
  destruct H2. destruct H2.
  rewrite negations_aux with (r := x1); try easy.
  unfold reg_push.
  rewrite highb01_correct_2 with (tenv := tenv) (aenv := aenv); try easy.
  assert (put_cus
  (put_cus
     ((f [(v, n0) |-> put_cu (f (v, n0)) false]) [
      (v0, n1) |-> put_cu (f (v0, n1)) ((v1 <=? v2))]) x 
     (nat2fb v1) n) y (nat2fb v2) n
      = (reg_push
    ((reg_push
     (f[
      (v0, n1) |-> put_cu (f (v0, n1)) ((v1 <=? v2))]) y v2 n)
               [(v, n0) |-> put_cu (f (v, n0)) false]) x v1 n)).
  unfold reg_push.
  rewrite eupdate_twice_neq by iner_p.
  rewrite put_cus_twice_neq by lia. 
  rewrite put_cus_update_flip by iner_p. easy. 
  rewrite H11. clear H11.
  erewrite inv_exp_reverse. easy.
  constructor. constructor. apply negator0_fwf.
  constructor. apply H8. easy. 
  unfold reg_push.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same_1 ; try easy.
  apply nor_mode_cus_eq.
  apply nor_mode_up. iner_p. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. apply H10.
  Check negations_aux.
  rewrite negations_aux with (r := x1); try easy.
  repeat rewrite cus_get_neq by iner_p.
  rewrite eupdate_index_eq.
  rewrite get_cus_put_eq; try lia.
  rewrite get_cus_put_neq; try lia.
  rewrite <- put_cus_update_flip with (f := (f [(v0, n1) |-> put_cu (f (v0, n1)) true])).
  rewrite get_cus_put_eq; try lia.
  assert ((get_cua (nval true x1)) = true). unfold get_cua. easy.
  rewrite H11.
  rewrite majb_carry_s_eq.
  specialize (carry_leb_equiv (n+1) v1 v2) as eq2.
  assert (n+1 -1 = n) by lia.
  rewrite H12 in eq2. clear H12.
  assert ((n + 1) = S n) by lia.
  rewrite H12 in eq2. clear H12. 
  rewrite Nat.pow_succ_r in eq2.
  assert (2 * 2 ^ n - 1 - v1 = 2 ^ n - 1 - v1 + 2 ^ n) by lia.
  rewrite H12 in eq2. rewrite eq2.
  rewrite put_cu_cus.
  rewrite put_cu_cus.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_eq.
  rewrite double_put_cu.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite eupdate_twice_neq by iner_p.
  rewrite eupdate_twice_eq.
  rewrite put_cus_update_flip by iner_p.
  bt_simpl. unfold reg_push. easy.
  1-7:lia. 
  unfold nor_modes. intros.
  repeat apply nor_mode_up ; iner_p. apply H4. easy.
  iner_p.
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p.
  apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p. apply H3. easy. iner_p.
  rewrite H2. unfold put_cu. easy.
  unfold reg_push.
  unfold nor_modes. intros. apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p.
  apply H3. easy.
  apply nor_mode_cus_eq. apply nor_mode_up ; iner_p.
  apply nor_mode_cus_eq. apply nor_mode_up_1; iner_p.
  apply nor_mode_cus_eq.
  unfold nor_mode. rewrite eupdate_index_eq. lia.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply H3. easy.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply H4. easy.
  rewrite put_cus_neq; iner_p.
  rewrite eupdate_index_neq by iner_p.
  rewrite put_cus_neq; iner_p.
  rewrite eupdate_index_eq.
  rewrite get_put_cu. easy. apply H6.
  apply right_mode_exp_put_cus_same.
  assert (nval true x1 = put_cu (f (v,n0)) true).
  rewrite H2. easy. rewrite H11.
  apply right_mode_exp_up_same_1.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy. iner_p.
  rewrite H2. easy.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply H3. easy.
Qed.

Local Opaque comparator01.

(* The correctness proof of the subtractor. *)
Lemma subtractor01_correct :
  forall tenv aenv n x y c1 v1 v2 f f' f'',
    0 < n ->
    v1 < 2^n ->
    v2 < 2^n ->     x <> y -> x <> fst c1 -> y <> fst c1 ->
    nor_modes f x n -> nor_modes f y n -> nor_mode f c1 -> well_typed_exp tenv (MAJseq n x y c1) ->
    well_typed_exp tenv (X c1) -> well_typed_exp tenv (negator0 n x) -> right_mode_env aenv tenv f ->
    f' = reg_push (reg_push (f[c1 |-> put_cu (f c1) false]) x v1 n) y v2 n ->
    f'' = reg_push (reg_push (f[c1 |-> put_cu (f c1) false]) x v1 n) y (v2 + 2^n - v1) n ->
    exp_sem aenv (subtractor01 n x y c1) f' = f''.
Proof.
  intros.
  unfold subtractor01. remember (X c1; negator0 n x) as negations. simpl. subst.
  rewrite reg_push_twice_neq by iner_p.
  rewrite reg_push_update_flip by iner_p.
  destruct (f c1) eqn:eq2.
  rewrite negations_aux with (r:=r); (try lia; try easy).
  rewrite <- reg_push_update_flip by iner_p.
  rewrite reg_push_twice_neq by iner_p.
  assert (nval true r = put_cu (f c1) true).
  rewrite eq2. easy. rewrite H12. 
  Check adder01_correct_carry1.
  rewrite adder01_correct_carry1 with (S0 := f) (v1 := (2 ^ n - 1 - v1)) (v2:=v2)
       (S'' := reg_push (reg_push (f [c1 |-> put_cu (f c1) true])
              x (2 ^ n - 1 - v1) n) y ((2 ^ n - 1 - v1) + v2 + 1) n); try easy.
  rewrite reg_push_twice_neq by iner_p.
  rewrite reg_push_update_flip by iner_p.
  erewrite inv_exp_reverse. unfold put_cu. easy.
  constructor. constructor. apply negator0_fwf.
  constructor. apply H9. easy.
  unfold reg_push.
  repeat apply right_mode_exp_put_cus_same.
  assert (nval false r = put_cu (f c1) false).
  unfold put_cu. rewrite eq2. easy. rewrite H13.
  apply right_mode_exp_up_same. apply H11.
  rewrite reg_push_twice_neq by iner_p.
  rewrite reg_push_update_flip by iner_p.
  rewrite negations_aux with (r:=r); (try lia; try easy).
  rewrite <- H12.
  assert ((2 ^ n - 1 - v1 + v2 + 1) = (v2 + 2 ^ n - v1)) by lia.
  rewrite H13. easy.
  unfold nor_modes. intros.
  unfold reg_push. apply nor_mode_cus_eq. apply H5. easy. lia.
  unfold nor_modes. intros.
  unfold reg_push. apply nor_mode_cus_eq. apply H5. easy.
  unfold nor_mode in H7. rewrite eq2 in H7. lia.
  unfold nor_mode in H7. rewrite eq2 in H7. lia.
Qed.

Local Opaque subtractor01.

Definition no_equal_5 (x y M:var) (c1 c2 : posi) : Prop := x <> y /\ x <> M /\ x <> fst c1 /\  x <> fst c2 
                   /\ y <> M /\ y <> fst c1 /\ y <> fst c2 /\ M <> fst c1 /\ M <> fst c2 /\ fst c1 <> fst c2.

Lemma adder01_sem_carry0 :
  forall n (f f' : posi -> val) x y c v1 v2 aenv,
    0 < n -> nor_modes f x n -> nor_modes f y n -> nor_mode f c ->
    x <> y -> x <> fst c -> y <> fst c ->
    v1 < 2^n -> v2 < 2^n -> get_r (f c) = get_r (f' c) -> nor_mode f' c ->
    exp_sem aenv (adder01 n x y c) (reg_push (reg_push (f[c |-> put_cu (f' c) false]) x v1 n) y v2 n)
               = reg_push (reg_push (f[c |-> put_cu (f' c) false]) x v1 n) y (v1+v2) n.
Proof.
  intros.
  specialize (adder01_correct_carry0 n f ( reg_push
        (reg_push (f [c |-> put_cu (f c) false]) x v1 n) y v2
        n) (reg_push (reg_push (f [c |-> put_cu (f c) false]) x v1 n) y
  (v1 + v2) n) x y c v1 v2 aenv H H0 H1 H2 H3 H4 H5 H6 H7) as eq1.
  unfold put_cu in *.
  unfold get_r in H8.
  unfold nor_mode in H2. unfold nor_mode in H9.
  destruct (f c) eqn:eq2.
  destruct (f' c) eqn:eq3. subst.
  rewrite eq1. easy. easy. easy. lia. lia. lia. lia.
Qed.

Lemma comparator01_sem :
  forall tenv aenv n x y c1 c2 v1 v2 f f',
    0 < n -> 
    v1 < 2^n -> v2 < 2^n -> no_equal x y c1 c2 ->
    nor_modes f x n -> nor_modes f y n -> nor_mode f c1 -> nor_mode f c2 -> well_typed_exp tenv (MAJseq n x y c1) ->
    well_typed_exp tenv (X c1) -> well_typed_exp tenv (negator0 n x) -> right_mode_env aenv tenv f ->
    get_r (f c1) = get_r (f' c1) -> nor_mode f' c1
     -> get_r (f c2) = get_r (f' c2) -> nor_mode f' c2 ->
    exp_sem aenv (comparator01 n x y c1 c2) (reg_push (reg_push 
          ((f[c1 |-> put_cu (f' c1) false])[c2 |-> put_cu (f' c2) false]) x v1 n) y v2 n)
      = (reg_push (reg_push ((f[c1 |-> put_cu (f' c1) false])[c2 |-> put_cu (f' c2) (¬(v1 <=? v2))]) x v1 n) y v2 n).
Proof.
  intros.
  specialize (comparator01_correct tenv aenv n x y c1 c2 v1 v2 f
  (reg_push
     (reg_push
        ((f [c1 |-> put_cu (f c1) false]) [c2
         |-> put_cu (f c2) false]) x v1 n) y v2 n)
    (reg_push
  (reg_push
     ((f [c1 |-> put_cu (f c1) false]) [c2
      |-> put_cu (f c2) (¬ (v1 <=? v2))]) x v1 n) y v2 n) H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10) as eq1.
  unfold put_cu in *. unfold get_r in H11. unfold get_r in H13.
  unfold nor_mode in H5. unfold nor_mode in H6.
  destruct (f c1) eqn:eq2.  destruct (f c2) eqn:eq3.
  unfold nor_mode in H12. unfold nor_mode in H14.
  destruct (f' c1) eqn:eq4.  destruct (f' c2) eqn:eq5. subst.
  rewrite eq1. 1-11:easy.
Qed.

Lemma comparator01_sem_a :
  forall tenv aenv n x y c1 c2 v1 v2 f,
    0 < n -> 
    v1 < 2^n -> v2 < 2^n -> no_equal x y c1 c2 ->
    nor_modes f x n -> nor_modes f y n -> nor_mode f c1 -> nor_mode f c2 -> well_typed_exp tenv (MAJseq n x y c1) ->
    well_typed_exp tenv (X c1) -> well_typed_exp tenv (negator0 n x) -> right_mode_env aenv tenv f ->
    get_cus n f x = nat2fb v1 -> get_cus n f y = nat2fb v2 -> get_cua (f c1) = false -> get_cua (f c2) = false ->
    exp_sem aenv (comparator01 n x y c1 c2) f = f[c2 |-> put_cu (f c2) (¬(v1 <=? v2))].
Proof.
  intros.
  assert (f = reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) false]) x v1 n) y v2 n).
  apply functional_extensionality. intros.
  unfold reg_push in *.
  destruct x0.
  unfold no_equal in *.
  destruct H2 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  bdestruct (y =? v). subst.
  bdestruct (n0 <? n). 
  rewrite put_cus_eq by lia.
  rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite <- put_cus_eq with (n := n) by lia.
  rewrite <- H12.
  rewrite put_get_cus_eq ; easy.
  rewrite put_cus_neq_2 by iner_p.
  rewrite put_cus_neq_2 by iner_p.
  bdestruct (c2 ==? (v,n0)). subst.
  rewrite eupdate_index_eq.
  rewrite <- H14.
  rewrite put_get_cu ; easy.
  rewrite eupdate_index_neq by iner_p.
  bdestruct (c1 ==? (v,n0)). subst.
  rewrite eupdate_index_eq.
  rewrite <- H13.
  rewrite put_get_cu ; easy.
  rewrite eupdate_index_neq by iner_p. easy.
  rewrite put_cus_neq by iner_p.
  bdestruct (x =? v). subst.
  bdestruct (n0 <? n). 
  rewrite put_cus_eq by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite <- put_cus_eq with (n := n) by lia.
  rewrite <- H11.
  rewrite put_get_cus_eq ; easy.
  rewrite put_cus_neq_2 by iner_p.
  bdestruct (c2 ==? (v,n0)). subst.
  rewrite eupdate_index_eq.
  rewrite <- H14.
  rewrite put_get_cu ; easy.
  rewrite eupdate_index_neq by iner_p.
  bdestruct (c1 ==? (v,n0)). subst.
  rewrite eupdate_index_eq.
  rewrite <- H13.
  rewrite put_get_cu ; easy.
  rewrite eupdate_index_neq by iner_p. easy.
  rewrite put_cus_neq by iner_p.
  bdestruct (c2 ==? (v,n0)). subst.
  rewrite eupdate_index_eq.
  rewrite <- H14.
  rewrite put_get_cu ; easy.
  rewrite eupdate_index_neq by iner_p.
  bdestruct (c1 ==? (v,n0)). subst.
  rewrite eupdate_index_eq.
  rewrite <- H13.
  rewrite put_get_cu ; easy.
  rewrite eupdate_index_neq by iner_p. easy.
  rewrite H15. 
  erewrite comparator01_correct with (tenv:=tenv) (v1:=v1) (v2:=v2) (f:=f)
       (f':= reg_push
        (reg_push
           ((f [c1 |-> put_cu (f c1) false]) [c2 |-> put_cu (f c2) false])
           x v1 n) y v2 n); try easy.
  unfold reg_push.
  destruct c2.
  rewrite put_cu_cus.
  rewrite put_cu_cus.
  rewrite eupdate_index_eq.
  rewrite put_cu_twice_eq.
  unfold no_equal in *.
  destruct H2 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- put_cus_update_flip by iner_p.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite eupdate_twice_eq. easy.
Qed.

Lemma comparator01_sem_true :
  forall tenv aenv n x y c1 c2 v1 v2 f f',
    0 < n -> 
    v1 < 2^n -> v2 < 2^n -> no_equal x y c1 c2 ->
    nor_modes f x n -> nor_modes f y n -> nor_mode f c1 -> nor_mode f c2 -> well_typed_exp tenv (MAJseq n x y c1) ->
    well_typed_exp tenv (X c1) -> well_typed_exp tenv (negator0 n x) -> right_mode_env aenv tenv f ->
    get_r (f c1) = get_r (f' c1) -> nor_mode f' c1
     -> get_r (f c2) = get_r (f' c2) -> nor_mode f' c2 ->
    exp_sem aenv (comparator01 n x y c1 c2) (reg_push (reg_push 
          ((f[c1 |-> put_cu (f' c1) false])[c2 |-> put_cu (f' c2) true]) x v1 n) y v2 n)
      = (reg_push (reg_push ((f[c1 |-> put_cu (f' c1) false])[c2 |-> put_cu (f' c2) ((v1 <=? v2))]) x v1 n) y v2 n).
Proof.
  intros.
  specialize (comparator01_correct_true tenv aenv n x y c1 c2 v1 v2 f
  (reg_push
     (reg_push
        ((f [c1 |-> put_cu (f c1) false]) [c2
         |-> put_cu (f c2) true]) x v1 n) y v2 n)
    (reg_push
  (reg_push
     ((f [c1 |-> put_cu (f c1) false]) [c2
      |-> put_cu (f c2) ((v1 <=? v2))]) x v1 n) y v2 n) H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10) as eq1.
  unfold put_cu in *. unfold get_r in H11. unfold get_r in H13.
  unfold nor_mode in H5. unfold nor_mode in H6.
  destruct (f c1) eqn:eq2.  destruct (f c2) eqn:eq3.
  unfold nor_mode in H12. unfold nor_mode in H14.
  destruct (f' c1) eqn:eq4.  destruct (f' c2) eqn:eq5. subst.
  rewrite eq1. 1-11:easy.
Qed.

Lemma subtractor01_sem :
  forall tenv aenv n x y c1 v1 v2 f f',
    0 < n ->
    v1 < 2^n ->
    v2 < 2^n ->  x <> y -> x <> fst c1 -> y <> fst c1 ->
    nor_modes f x n -> nor_modes f y n -> nor_mode f c1 -> well_typed_exp tenv (MAJseq n x y c1) ->
    well_typed_exp tenv (X c1) -> well_typed_exp tenv (negator0 n x) -> right_mode_env aenv tenv f ->
    get_r (f c1) = get_r (f' c1) -> nor_mode f' c1 ->
    exp_sem aenv (subtractor01 n x y c1) (reg_push (reg_push (f[c1 |-> put_cu (f' c1) false]) x v1 n) y v2 n) 
     = (reg_push (reg_push (f[c1 |-> put_cu (f' c1) false]) x v1 n) y (v2 + 2^n - v1) n).
Proof.
  intros.
  specialize (subtractor01_correct tenv aenv n x y c1 v1 v2 f
     (reg_push (reg_push (f [c1 |-> put_cu (f c1) false]) x v1 n) y v2 n)
     (reg_push (reg_push (f [c1 |-> put_cu (f c1) false]) x v1 n) y
        (v2 + 2 ^ n - v1) n) H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11) as eq1.
  unfold put_cu,get_r in *.
  unfold nor_mode in H7. unfold nor_mode in H13.
  destruct (f c1) eqn:eq2. destruct (f' c1) eqn:eq4.
  subst. rewrite eq1. 1-4:easy.
  1-3:lia.
Qed.

(* The correctness statement of the modulo adder. *)
Lemma modadder21_correct :
  forall tenv aenv n x y M c1 c2 v1 v2 vM f,
    0 < n -> v1 < vM -> v2 < vM -> vM < 2^(n-1) -> no_equal_5 x y M c1 c2 ->
    nor_modes f x n -> nor_modes f y n -> nor_modes f M n -> nor_mode f c1 -> nor_mode f c2
     -> well_typed_exp tenv (modadder21 n x y M c1 c2) -> right_mode_env aenv tenv f ->
    exp_sem aenv (modadder21 n x y M c1 c2) 
      (reg_push (reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) false]) M vM n) y v2 n) x v1 n)
    = (reg_push (reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) false]) M vM n) y v2 n) x ((v1 + v2) mod vM) n).
Proof.
  intros.
  assert (v1 + v2 < 2^n).
  { replace (2^n) with (2^(n-1) + 2^(n-1)). lia.
    destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
  }
  assert (vM < 2^n).
  { apply pow2_predn. easy.
  }
  assert (v1 <2^(n-1)) by lia.
  assert (v2 <2^(n-1)) by lia.
  unfold modadder21. remember (CU c2 (subtractor01 n M x c1)) as csub01.
  remember (X c2) as csub02. simpl. subst.
  unfold no_equal_5 in H4.
  destruct H3 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  destruct c1 as [c1 cp1]. destruct c2 as [c2 cp2].
  rewrite eupdate_twice_neq by iner_p.
  rewrite reg_push_update_flip by iner_p.
  rewrite adder01_sem_carry0 ; (try lia ; try easy).
  rewrite <- reg_push_update_flip by iner_p.
  rewrite reg_push_twice_neq with (x:=M) by lia.
  rewrite reg_push_update_flip by iner_p.
  rewrite reg_push_update_flip with (x:=y) by iner_p.
  rewrite eupdate_twice_neq by iner_p.
  rewrite comparator01_sem with (tenv := tenv) (aenv := aenv); (try lia; try easy).
  rewrite exp_sem_x.
  assert (exchange
            (reg_push
               (reg_push
                  (((reg_push f y v2 n) [(c1, cp1)
                    |-> put_cu (f (c1, cp1)) false]) [
                   (c2, cp2)
                   |-> put_cu (f (c2, cp2)) (¬ (vM <=? v2 + v1))])
                  M vM n) x (v2 + v1) n (c2, cp2))
        = put_cu (f (c2, cp2)) (vM <=? v2 + v1)).
  unfold reg_push.
  rewrite put_cus_neq by iner_p.
  rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_eq.
  unfold exchange. unfold put_cu.
  unfold nor_mode in H8. destruct (f (c2, cp2)) eqn:eq1.
  assert ((¬ (¬ (vM <=? v2 + v1))) = (vM <=? v2 + v1)) by btauto. rewrite H3. easy. lia. lia.
  rewrite H3. clear H3. simpl.
  rewrite eupdate_index_eq. rewrite get_put_cu by easy.
  bdestruct (vM <=? v2 + v1). simpl.
  rewrite <- reg_push_update_flip by iner_p.
  rewrite <- reg_push_update_flip by iner_p.
  rewrite eupdate_twice_eq.
  rewrite eupdate_twice_neq by iner_p.
  rewrite subtractor01_sem with (tenv:= tenv) (aenv:=aenv); (try lia; try easy).
  erewrite inv_exp_reverse.
  rewrite reg_push_update_flip with (x := M) by iner_p.
  rewrite reg_push_update_flip with (x := M) by iner_p.
  rewrite reg_push_twice_neq by iner_p.
  rewrite <- reg_push_update_flip with (x := y) by iner_p.
  rewrite <- reg_push_update_flip with (x := y) by iner_p.
  easy.
  apply comparator01_fwf. unfold no_equal. split. lia. split. easy.
  split. easy. split. lia. split. lia. iner_p.
  unfold modadder21 in H9. inv H9. 
  apply typed_inv_exp in H19. rewrite inv_exp_involutive in H19. apply H19.
  unfold reg_push. 
  repeat apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same_1.
  apply nor_mode_up ; try iner_p. apply nor_mode_cus_eq. easy. easy.
  apply right_mode_exp_up_same_1. apply nor_mode_cus_eq. easy. easy.
  apply right_mode_exp_put_cus_same. apply H10.
  rewrite comparator01_sem with (tenv := tenv) (aenv:=aenv); (try lia; try easy).
  rewrite <- reg_push_update_flip by iner_p.
  rewrite <- reg_push_update_flip by iner_p.
  rewrite reg_push_twice_neq with (x:=M) by iner_p.
  rewrite reg_push_update_flip by iner_p.
  rewrite reg_push_update_flip with (x:=y) by iner_p.
  rewrite eupdate_twice_neq by iner_p.
  clear H4 H5 H6 H7 H8 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 H9 H10 H11 H12 H13 H14.
  rewrite plus_comm.
  rewrite <- mod_sum_lt_bool by lia. rewrite plus_comm.
  rewrite plus_comm in H3.
  assert (v1 + v2 + 2 ^ n - vM = v1 + v2 - vM + 2^n) by lia.
  rewrite H4.
  rewrite reg_push_exceed with (v:= v1 + v2 - vM + 2 ^ n).
  assert (2^n <> 0) by (apply Nat.pow_nonzero; easy).
  rewrite <- Nat.add_mod_idemp_r with (a := v1 + v2 - vM) by easy.
  rewrite Nat.mod_same by easy.
  rewrite Nat.add_0_r. rewrite <- reg_push_exceed.
  rewrite Nat.mod_eq by lia.
  assert (v1 + v2 < 2 * vM) by lia.
  assert ((v1 + v2) / vM < 2) by (apply Nat.div_lt_upper_bound; lia).
  assert (1 <= (v1 + v2) / vM) by (apply Nat.div_le_lower_bound; lia).
  assert ((v1 + v2) / vM = 1) by lia.
  replace (v1 + v2 - vM * ((v1 + v2) / vM)) with (v1 + v2 - vM) by lia.
  bdestruct (vM <=? v1 + v2). simpl. easy. lia.
  assert ((v1 + v2) mod vM < vM).
  apply Nat.mod_upper_bound. lia. lia.
  unfold no_equal. split. lia. split. easy. split. easy. split. easy. split. easy. iner_p.
  unfold nor_modes. intros. nor_mode_simpl.
  apply H5. easy.
  unfold nor_modes. intros. nor_mode_simpl.
  apply H4. easy.
  nor_mode_simpl. nor_mode_simpl.
  right_simpl. right_simpl. right_simpl.
  Local Transparent adder01 subtractor01 comparator01.
  inv H9. inv H18. inv H17. inv H18. inv H17. easy.
  inv H9. inv H18. inv H20. inv H21. inv H20. inv H21. easy.
  inv H9. inv H19. inv H17. rewrite inv_exp_involutive in H21. easy.
  unfold reg_push. apply right_mode_exp_put_cus_same. easy.
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  unfold nor_modes. intros. nor_mode_simpl.
  apply H6. easy.
  unfold nor_modes. intros. nor_mode_simpl.
  apply H4. easy. nor_mode_simpl.
  right_simpl. right_simpl. right_simpl.
  inv H9. inv H18. inv H20. inv H21. inv H20. inv H23. easy.
  inv H9. inv H18. inv H20. inv H21. inv H20. inv H21. easy.
  inv H9. inv H18. inv H17. inv H18. inv H22. inv H18. inv H22. easy.
  unfold reg_push. apply right_mode_exp_up_same_1.
  nor_mode_simpl. apply H8.
  apply right_mode_exp_put_cus_same. easy.
  unfold reg_push. rewrite eupdate_index_neq by iner_p.
  rewrite put_cus_neq by iner_p. easy.
  erewrite inv_exp_reverse.
  rewrite reg_push_update_flip with (x := M) by iner_p.
  rewrite reg_push_update_flip with (x := M) by iner_p.
  rewrite reg_push_twice_neq by iner_p.
  rewrite <- reg_push_update_flip with (x := y) by iner_p.
  rewrite <- reg_push_update_flip with (x := y) by iner_p.
  easy.
  apply comparator01_fwf. unfold no_equal. split. lia.
  split. easy. split. easy. split. easy. split. easy. iner_p.
  Local Opaque comparator01.
  inv H9.
  apply typed_inv_exp in H19. rewrite inv_exp_involutive in H19. apply H19.
  unfold reg_push.
  repeat apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same_1. nor_mode_simpl. easy.
  apply right_mode_exp_up_same_1. nor_mode_simpl. easy.
  apply right_mode_exp_put_cus_same. apply H10.
  rewrite comparator01_sem with (tenv := tenv) (aenv:=aenv); (try lia; try easy).
  rewrite reg_push_update_flip by iner_p.
  rewrite reg_push_update_flip by iner_p.
  rewrite reg_push_update_flip with (x := M) by iner_p.
  rewrite reg_push_update_flip with (x := x) by iner_p.
  rewrite eupdate_twice_eq.
  rewrite reg_push_update_flip with (x:=M) by iner_p.
  rewrite reg_push_twice_neq with (x:=y) (y:=M) by iner_p.
  rewrite reg_push_update_flip with (x:=y) by iner_p.
  rewrite plus_comm.
  rewrite <- mod_sum_lt_bool by lia.
  bdestruct (vM <=? v2 + v1). lia. simpl.
  rewrite Nat.mod_small by lia. easy.
  assert ((v1 + v2) mod vM < vM).
  apply Nat.mod_upper_bound. lia. lia.
  unfold no_equal. split. lia.
  split. easy. split. easy. split. easy. split. easy. iner_p.
  unfold nor_modes. intros. nor_mode_simpl. apply H5. lia.
  unfold nor_modes. intros. nor_mode_simpl. apply H4. lia.
  nor_mode_simpl. nor_mode_simpl.
  Local Transparent comparator01.
  inv H9. inv H18. inv H17. inv H18. inv H17. easy.
  inv H9. inv H18. inv H17. inv H18. inv H22. inv H18. inv H22. easy.
  inv H9. inv H19. inv H17. rewrite inv_exp_involutive in H21. easy.
  right_simpl. 
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  unfold no_equal. split. lia.
  split. easy. split. easy. split. easy. split. easy. iner_p.
  unfold nor_modes. intros. nor_mode_simpl. apply H6. lia.
  unfold nor_modes. intros. nor_mode_simpl. apply H4. lia.
  1-2:nor_mode_simpl. 
  inv H9. inv H17. inv H19. inv H20. inv H19. inv H22. easy.
  inv H9. inv H18. inv H16. easy.
  inv H9. inv H17. inv H19. inv H20. inv H19. inv H20. easy.
  right_simpl.
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  unfold nor_modes. intros. nor_mode_simpl. apply H5. lia.
  unfold nor_modes. intros. nor_mode_simpl. apply H4. lia.
  nor_mode_simpl.
  unfold reg_push. rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_neq by iner_p. easy.
Qed.


(** Functions for extraction & evaluation: **)

(* Supporting data for adder01 *)
Definition vars_for_adder01' (size:nat) := gen_vars size (x_var::y_var::[]).
Definition vars_for_adder01 (size:nat) :=
  fun x => if x =? z_var then (size * 2,1,id_nat,id_nat) else vars_for_adder01' size x.

(* z = x + y *)
Definition adder01_out (size:nat) := adder01 size x_var y_var (z_var,0).


(* Implementing x * M circuit *)
Definition one_cl_cu_adder (c2:posi) (ex:var) (re:var) (n:nat) (c1:posi) (M:nat -> bool) :=
  CU c2 (init_v n ex M; adder01 n ex re c1; init_v n ex M).

(* adding 02, only adding x_...x_m to y_i+1,...,y_i+m *)
Fixpoint MAJseq'_i n x y c (i:nat) : exp :=
  match n with
  | 0 => MAJ c (y,i) (x,0)
  | S m => MAJseq'_i m x y c i; MAJ (x, m) (y, n+i) (x, n)
  end.
Definition MAJseq_i n x y c i := MAJseq'_i (n - 1) x y c i.

Fixpoint UMAseq'_i n x y c i : exp :=
  match n with
  | 0 => UMA c (y,i) (x,0)
  | S m => UMA (x, m) (y,n+i) (x, n); UMAseq'_i m x y c i
  end.
Definition UMAseq_i n x y c i := UMAseq'_i (n - 1) x y c i.

Definition adder_i n x y c i: exp := MAJseq_i n x y c i ; UMAseq_i n x y c i.

(* z = x * M *)
Fixpoint cl_nat_mult' (n:nat) (size:nat) (x:var) (re:var) (c:posi) (M:nat->bool) :=
   match n with 
   | 0 => SKIP (re,0)
   | S m => cl_nat_mult' m size x re c M;
             if (M m) then adder_i (size - m) x re c m else SKIP (re,0)
  end.

Definition cl_nat_mult (size:nat) (x:var) (re:var) (c:posi) (M:nat -> bool) := 
  Exp (cl_nat_mult' size size x re c M).

Definition vars_for_cl_nat_m' (size:nat) := gen_vars size (x_var::y_var::[]).

Definition vars_for_cl_nat_m (size:nat) :=
  fun x => if x =? z_var then (size * 2,1,id_nat,id_nat) else vars_for_cl_nat_m' size x.

Definition cl_nat_mult_out (size:nat) (M:nat -> bool) := 
  cl_nat_mult size x_var y_var (z_var,0) M.


(* Implementing x * M circuit for fixedP values *)
Fixpoint cl_flt_mult' (n:nat) (size:nat) (x:var) (ex:var) (re:var) (c:posi) (M:nat->bool) :=
  match n with 
  | 0 => SKIP (x,0)
  | S m => one_cl_cu_adder (x,size - n) ex re size c M; 
          cl_flt_mult' m size x ex re c (cut_n (div_two_spec M) size)
  end.
Definition cl_flt_mult (size:nat) (x:var) (re:var) (ex:var) (c:posi) (M:nat -> bool) := 
  cl_flt_mult' size size x ex re c M.

(* z = x * y circuit for nats *)
Definition one_cu_cl_full_adder_i (c2:posi) (y:var) (x:var) (c1:posi) (n:nat) (i:nat) := 
  CU c2 (adder_i n x y c1 i).

Fixpoint cl_full_mult' (n:nat) (size:nat) (x:var) (y:var) (re:var) (c:posi) :=
   match n with 
   | 0 => SKIP (re,0)
   | S m => cl_full_mult' m size x y re c;
           one_cu_cl_full_adder_i (y,m) x re c (size-m) m
   end.

(* Here x and y are in nor_mode and re in phi_mode. 
      [x][y][phi(re)] ->[x][y][phi(x*y mod 2^n)], re is supposed to be zero, 
    ex is in nor_mode. *)
Definition cl_full_mult (size:nat) (x y:var) (re:var) (c:posi) :=
  Exp (cl_full_mult' size size x y re c).

Definition vars_for_cl_nat_full_m' (size:nat) := 
  gen_vars size (x_var::(y_var::(z_var::([])))).

Definition vars_for_cl_nat_full_m (size:nat) :=
  fun x => if x =? s_var then (size * 3,1,id_nat,id_nat) 
        else vars_for_cl_nat_full_m' size x.

Definition cl_full_mult_out (size:nat) := 
   cl_full_mult size x_var y_var z_var (s_var,0).


(* x * y circuit for fixedP values. *)
Definition one_cu_cl_full_adder (c2:posi) (y:var) (x:var) (c1:posi) (n:nat) := 
  CU c2 (adder01 n x y c1).


Fixpoint clf_full_mult' (n:nat) (size:nat) (x:var) (y:var) (re:var) (ex:var) (c:posi) :=
   match n with 0 => SKIP (x,0)
            | S m => clf_full_mult' m size x y re ex c; 
                  one_cu_cl_full_adder (x,m) re y c size; SWAP (y,0) (ex,m); Rshift y
   end.
Definition clf_full_mult_quar (size:nat) (x y:var) (re:var) (ex:var) (c:posi)
                       := clf_full_mult' size size x y re ex c.

Fixpoint clean_high_flt (n:nat) (size:nat) (y:var) (ex:var) :=
    match n with 0 => SKIP (y,0)
               | S m => clean_high_flt m size y ex ;SWAP (y,0) (ex,m); Rshift y
    end.

(*Here x and y are in nor_mode and re in phi_mode.
      [x][y][phi(re)] ->[x][y][phi((x*2^n*y)/2^n)], re is supposed to be zero, 
    ex is in nor_mode. *)
Definition clf_full_mult (size:nat) (x y:var) (re:var) (ex:var) (c:posi) :=
            (Exp (clf_full_mult_quar size x y re ex c; inv_exp (clean_high_flt size size y ex))).


(* compare x <=? y 
Definition comparator02 n x y c1 c2 := (negator0 n x); highb01 n x y c1 c2; inv_exp (negator0 n x).
*)

(* x % M circuit. *)
Fixpoint cl_moder' i (n:nat) (x y ex:var) c1 c2 (M:nat -> bool) := 
     match i with 0 => SKIP (x,0)
           | S j => init_v n y M ; X c2 ; comparator01 n y x c1 c2 ; 
                       CU c2 (subtractor01 n y x c1); SWAP c2 (ex,j); X c2; init_v n y M ; 
                       cl_moder' j n x y ex c1 c2 (cut_n (div_two_spec M) n)
     end.
Definition cl_moder (n:nat) (x re y ex:var) c1 c2 (M:nat) := 
    let i := findnum M n in 
         cl_moder' (S i) n x y ex c1 c2 (nat2fb (2^i*M)) ; copyto x re n; inv_exp (cl_moder' (S i) n x y ex c1 c2 (nat2fb (2^i*M))).

Definition vars_for_cl_moder' (size:nat) := 
  gen_vars size (x_var::(y_var::(z_var::(s_var::[])))).

Definition vars_for_cl_moder (size:nat) :=
  fun x => if x =? c_var then (size * 4,2,id_nat,id_nat) 
        else vars_for_cl_moder' size x.

Definition cl_moder_out (size:nat)  := 
   cl_moder size x_var y_var z_var s_var (c_var,0) (c_var, 1).

(* x / M circuit. *)
Definition cl_div (n:nat) (x re y ex:var) c1 c2 (M:nat) := 
    let i := findnum M n in 
         cl_moder' (S i) n x y ex c1 c2 (nat2fb (2^i*M)) ; copyto ex re n; inv_exp (cl_moder' (S i) n x y ex c1 c2 (nat2fb (2^i*M))).

Definition vars_for_cl_div' (size:nat) := 
  gen_vars size (x_var::(y_var::(z_var::(s_var::[])))).

Definition vars_for_cl_div (size:nat) :=
  fun x => if x =? c_var then (size * 4,2,id_nat,id_nat) 
        else vars_for_cl_div' size x.

Definition cl_div_out (size:nat) := 
   cl_div size x_var y_var z_var s_var (c_var,0) (c_var, 1).


(* x = (x % M, x / M) mod value is in x, and ex stores div results. *)
Definition cl_div_mod (n:nat) (x y ex:var) c1 c2 (M:nat) :=
   let i := findnum M n in cl_moder' (S i) n x y ex c1 c2 (nat2fb (2^i*M)).

Definition vars_for_cl_div_mod' (size:nat) := 
  gen_vars size (x_var::(y_var::(z_var::([])))).

Definition vars_for_cl_div_mod (size:nat) :=
  fun x => if x =? s_var then (size * 3,2,id_nat,id_nat) 
        else vars_for_cl_div_mod' size x.

Definition cl_div_mod_out (size:nat) := 
   cl_div_mod size x_var y_var z_var (s_var,0) (s_var, 1).









