Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import MathSpec.
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
                                       comparator01 n M x c1 c2; (* compare M > x + y (in position x) *)
                                       X c2 ; CU c2 (subtractor01 n M x c1) ; (* doing -M + x to x, then flip c2. *)
                                       inv_exp(comparator01 n y x c1 c2). (* compare x with x+y % M to clean c2. *)

(* Here we implement the doubler circuit based on binary shift operation.
   It assumes an n-1 value x that live in a cell of n-bits (so the high-bit must be zero). 
   Then, we shift one position, so that the value looks like 2*x in a n-bit cell. *)
Definition doubler1 y := Lshift y.

(* Another version of the mod adder only for computing [x][M] -> [2*x % M][M].
   This version will mark the high-bit, and the high-bit is not clearable.
   However, eventually, we will clean all high-bit
   by using a inverse circuit of the whole implementation. *)
Definition moddoubler01 n x M c1 c2 :=
                doubler1 x;  X c2; (comparator01 n M x c1 c2; CU c2 (subtractor01 n M x c1)).

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

Fixpoint modsummer' i n M x y c1 s (fC : nat -> bool) :=
  match i with
  | 0 => SKIP (x,0)
  | S i' =>  modsummer' i' n M x y c1 s fC; 
            (if (fC i') then (modadder21 n y x M c1 (s,i')) else (SKIP (x,i'))); moddoubler01 n x M c1 (s,i')
  end.
Definition modsummer n M x y c1 s C := modsummer' (n-1) n M x y c1 s (nat2fb C).

(* This is the final clean-up step of the mod multiplier to do C*x %M. 
    Here, modmult_half will first clean up all high bits.  *)
Definition modmult_half n M x y c1 s C := modsummer n M x y c1 s C; (inv_exp (modsummer n M x y c1 s 0)).

Definition modmult_full C Cinv n M x y c1 s := modmult_half n M x y c1 s C; inv_exp (modmult_half n M y x c1 s Cinv).

Definition modmult M C Cinv n x y z s c1 := (init_v n z M); modmult_full C Cinv n z x y c1 s; inv_exp ( (init_v n z M)).

Definition modmult_rev M C Cinv n x y z s c1 := modmult M C Cinv n x y z s c1.


Definition x_var := 0. Definition y_var := 1. Definition z_var := 2. Definition s_var := 3.
Definition c_var := 4.
Definition vars_for_cl' (size:nat) := gen_vars size (x_var::(y_var::(z_var::(s_var::[])))).

Definition vars_for_cl (size:nat) := fun x => if x =? c_var then (size * 4,1,id_nat,id_nat) else vars_for_cl' size x.

Definition real_modmult_rev (M C Cinv size:nat) :=
    modmult (nat2fb M) C Cinv size x_var y_var z_var s_var (c_var,0).

Definition trans_modmult_rev (M C Cinv size:nat) :=
        trans_exp (vars_for_cl size) (4*size+1) (real_modmult_rev M C Cinv size) (avs_for_arith size).

(*********** Proofs ***********)

Definition no_equal (x y:var) (c1 c2 : posi) : Prop := x <> y /\ x <> fst c1 /\  x <> fst c2 
                   /\ y <> fst c1 /\ y <> fst c2 /\ c1 <> c2.

Definition no_equal_5 (x y M:var) (c1 c2 : posi) : Prop := x <> y /\ x <> M /\ x <> fst c1 /\  x <> fst c2 
                   /\ y <> M /\ y <> fst c1 /\ y <> fst c2 /\ M <> fst c1 /\ M <> fst c2 /\ c1 <> c2.


Definition no_equal_5a (x y M s:var) (c1 : posi) : Prop := x <> y /\ x <> M /\ x <> s /\  x <> fst c1 
                   /\ y <> M /\ y <> s /\ y <> fst c1 /\ M <> s /\ M <> fst c1 /\ s <> fst c1.

Definition hbf n M x := fun (i : nat) =>
                          if (i <? n)
                               then (M <=? 2 * ((2^i * x) mod M)) else false.

Lemma maj_wt : forall aenv env x y z, x <> y -> y <> z -> z <> x ->
                   Env.MapsTo (fst x) Nor env -> Env.MapsTo (fst y) Nor env
                   -> Env.MapsTo (fst z) Nor env -> well_typed_pexp aenv env (MAJ x y z) env.
Proof.
  intros.
  unfold MAJ.
  apply pe_seq with (env' := env).
  apply pe_seq with (env' := env).
  apply cnot_wt_nor; try easy. iner_p.
  apply cnot_wt_nor; try easy.
  apply ccx_wt_nor; try easy.
Qed.

Lemma uma_wt : forall aenv env x y z, x <> y -> y <> z -> z <> x ->
                   Env.MapsTo (fst x) Nor env -> Env.MapsTo (fst y) Nor env
                   -> Env.MapsTo (fst z) Nor env -> well_typed_pexp aenv env (UMA x y z) env.
Proof.
  intros.
  unfold UMA.
  apply pe_seq with (env' := env).
  apply pe_seq with (env' := env).
  apply ccx_wt_nor; try easy.
  apply cnot_wt_nor; try easy.
  apply cnot_wt_nor; try easy.
Qed.

Local Transparent CNOT CCX.

Lemma maj_fresh : forall aenv x y z c, x <> c -> y <> c -> z <> c ->
                      exp_fresh aenv c (MAJ x y z). 
Proof.
  intros.
  unfold MAJ. constructor. constructor.
  unfold CNOT. constructor. iner_p. constructor. iner_p.
  unfold CNOT. constructor. iner_p. constructor. iner_p.
  unfold CCX.
  unfold CNOT. constructor. iner_p. constructor. iner_p.
  constructor. iner_p.
Qed.

Lemma uma_fresh : forall aenv x y z c, x <> c -> y <> c -> z <> c ->
                      exp_fresh aenv c (UMA x y z). 
Proof.
  intros.
  unfold UMA. constructor. constructor.
  unfold CNOT. constructor. iner_p. constructor. iner_p.
  unfold CNOT. constructor. iner_p. constructor. iner_p.
  constructor. iner_p.
  unfold CNOT. constructor. iner_p. constructor. iner_p.
Qed.

Lemma maj_neu : forall l x y z, exp_neu_l l [] (MAJ x y z) []. 
Proof.
  intros.
  unfold MAJ. 
  apply seq_neul with (l' := []).
  unfold CNOT. 
  apply seq_neul with (l' := []).
  constructor. constructor.
  constructor. constructor.
  unfold CCX.
  unfold CNOT. constructor. constructor. constructor.
Qed.

Lemma uma_neu : forall l x y z, exp_neu_l l [] (UMA x y z) []. 
Proof.
  intros.
  unfold UMA. 
  apply seq_neul with (l' := []).
  unfold CCX.
  unfold CNOT.
  apply seq_neul with (l' := []). constructor. constructor.
  constructor. constructor. constructor.
  unfold CNOT. constructor. constructor.
Qed.

Local Opaque CNOT CCX.

Lemma MAJseq'_wt : forall n aenv tenv x y c, x <> fst c -> y <> fst c -> x <> y -> Env.MapsTo x Nor tenv
      -> Env.MapsTo y Nor tenv -> Env.MapsTo (fst c) Nor tenv -> 
       well_typed_pexp aenv tenv (MAJseq' n x y c) tenv.
Proof.
 induction n;intros;simpl.
 apply maj_wt. iner_p. iner_p. iner_p. easy. simpl. easy. simpl. easy.
  apply pe_seq with (env' := tenv).
  apply IHn; try easy.
  apply maj_wt. iner_p. iner_p. iner_p. easy. easy. easy.
Qed.

Lemma MAJseq'_fresh : forall n aenv x y c c2, c <> c2 -> y <> fst c2 -> x <> fst c2->
                      exp_fresh aenv c2 (MAJseq' n x y c). 
Proof.
 induction n;intros;simpl.
 apply maj_fresh. destruct c2. destruct c. iner_p. iner_p. iner_p.
 constructor. 
 apply IHn; try easy.
 apply maj_fresh. iner_p. iner_p. iner_p.
Qed.

Lemma MAJseq'_neu : forall n l x y c, exp_neu_l l [] (MAJseq' n x y c) []. 
Proof.
 induction n;intros;simpl.
 apply maj_neu.
 apply seq_neul with (l' := []).
 apply IHn.
 apply maj_neu.
Qed.

Lemma MAJseq_wt : forall n aenv tenv x y c, x <> fst c -> y <> fst c -> x <> y -> Env.MapsTo x Nor tenv
      -> Env.MapsTo y Nor tenv -> Env.MapsTo (fst c) Nor tenv -> 
       well_typed_pexp aenv tenv (MAJseq n x y c) tenv.
Proof.
 intros. unfold MAJseq. apply MAJseq'_wt; try easy.
Qed.

Lemma MAJseq_fresh : forall n aenv x y c c2, c <> c2 -> y <> fst c2 -> x <> fst c2->
                      exp_fresh aenv c2 (MAJseq n x y c). 
Proof.
 intros. unfold MAJseq. apply MAJseq'_fresh; try easy.
Qed.

Lemma MAJseq_neu : forall n l x y c, exp_neu_l l [] (MAJseq n x y c) []. 
Proof.
 intros. unfold MAJseq. apply MAJseq'_neu; try easy.
Qed.

Lemma UMAseq'_wt : forall n aenv tenv x y c, x <> fst c -> y <> fst c -> x <> y -> Env.MapsTo x Nor tenv
      -> Env.MapsTo y Nor tenv -> Env.MapsTo (fst c) Nor tenv -> 
       well_typed_pexp aenv tenv (UMAseq' n x y c) tenv.
Proof.
 induction n;intros;simpl.
 apply uma_wt. iner_p. iner_p. iner_p. easy. simpl. easy. simpl. easy.
  apply pe_seq with (env' := tenv).
 apply uma_wt. iner_p. iner_p. iner_p. easy. simpl. easy. simpl. easy.
  apply IHn; try easy.
Qed.

Lemma UMAseq'_fresh : forall n aenv x y c c2, c <> c2 -> y <> fst c2 -> x <> fst c2->
                      exp_fresh aenv c2 (UMAseq' n x y c). 
Proof.
 induction n;intros;simpl.
 apply uma_fresh. destruct c2. destruct c. iner_p. iner_p. iner_p.
 constructor. 
 apply uma_fresh. iner_p. iner_p. iner_p.
 apply IHn; try easy.
Qed.

Lemma UMAseq'_neu : forall n l x y c, exp_neu_l l [] (UMAseq' n x y c) []. 
Proof.
 induction n;intros;simpl.
 apply uma_neu.
 apply seq_neul with (l' := []).
 apply uma_neu.
 apply IHn.
Qed.

Lemma UMAseq_wt : forall n aenv tenv x y c, x <> fst c -> y <> fst c -> x <> y -> Env.MapsTo x Nor tenv
      -> Env.MapsTo y Nor tenv -> Env.MapsTo (fst c) Nor tenv -> 
       well_typed_pexp aenv tenv (UMAseq n x y c) tenv.
Proof.
 intros. unfold UMAseq. apply UMAseq'_wt; try easy.
Qed.

Lemma UMAseq_fresh : forall n aenv x y c c2, c <> c2 -> y <> fst c2 -> x <> fst c2->
                      exp_fresh aenv c2 (UMAseq n x y c). 
Proof.
 intros. unfold UMAseq. apply UMAseq'_fresh; try easy.
Qed.

Lemma UMAseq_neu : forall n l x y c, exp_neu_l l [] (UMAseq n x y c) []. 
Proof.
 intros. unfold UMAseq. apply UMAseq'_neu; try easy.
Qed.

Lemma negator0_wt : forall n aenv tenv x, Env.MapsTo x Nor tenv ->
       well_typed_pexp aenv tenv (negator0 n x) tenv.
Proof.
 induction n;intros;simpl. constructor. constructor.
  apply pe_seq with (env' := tenv).
  apply IHn. easy.
  constructor. constructor. easy.
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

(*

Lemma negator0_fwf : forall n x aenv, exp_fwf aenv (negator0 n x).
Proof.
  intros. induction n;simpl.
  constructor. constructor. easy. constructor.
Qed.
*)

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



(*
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
*)
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
    0 < n -> n = aenv x -> n = aenv y -> no_equal x y c1 c2 -> snd c1 < aenv (fst c1) -> snd c2 < aenv (fst c2)
    -> Env.MapsTo (fst c2) Nor tenv -> Env.MapsTo (fst c1) Nor tenv -> 
    Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f -> get_cua (f c2) = false ->
    exp_sem aenv (highb01 n x y c1 c2) f =
      f[c2 |-> put_cu (f c2) ((majb true false (carry (get_cua (f c1)) n (get_cus n f x) (get_cus n f y))) ⊕ true)].
Proof.
  intros.
  unfold highb01. unfold no_equal in H2.
  destruct H2 as [V1 [V2 [V3 [V4 [V5 V6]]]]].
  assert (nor_mode f c1) as X1. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_mode f c2) as X2. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_modes f x (aenv x)) as X3.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H0 in X3.
  assert (nor_modes f y (aenv y)) as X4.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H1 in X4.
  destruct c1. destruct c2.
  simpl. unfold MAJseq. rewrite (MAJseq'_correct (n-1) n); (try easy; try lia).
  rewrite highbit_correct; try lia.
  rewrite put_cu_cus. rewrite put_cu_cus.
  rewrite get_cus_cua by lia.
  rewrite put_cus_neq by lia.
  rewrite cus_get_eq; try lia.
  rewrite eupdate_index_neq by iner_p.
  erewrite inv_pexp_reverse. easy.
  apply MAJseq'_wt; try easy. apply H7. apply H8.  apply H6. 
  apply right_mode_exp_up_same. easy.
  apply qft_uniform_put_cu_same. easy.
  apply qft_gt_put_cu_same. easy.
  rewrite (MAJseq'_correct (n-1) n); (try easy; try lia).
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite get_cus_up by iner_p.
  rewrite eupdate_twice_neq by iner_p.
  rewrite put_cus_update_flip by iner_p.
  rewrite put_cus_update_flip by iner_p.
  apply eupdate_same_1. easy.
  unfold msma. bdestruct (n - 1 <? n - 1). lia.
  bdestruct (n - 1 =? n - 1).
  assert ((S (n - 1)) = n) by lia. rewrite H14. easy. lia.
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p. apply X3. easy.
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p. apply X4. easy.
  apply nor_mode_up ; iner_p. 
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p. apply X3. easy.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p. apply X3. easy.
  repeat rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_neq by iner_p. easy.
Qed.

Lemma highb01_correct_2 :
  forall n tenv f x y c1 c2 aenv,
    0 < n -> n = aenv x -> n = aenv y -> no_equal x y c1 c2 -> snd c1 < aenv (fst c1) -> snd c2 < aenv (fst c2)
    -> Env.MapsTo (fst c2) Nor tenv -> Env.MapsTo (fst c1) Nor tenv -> 
    Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f -> get_cua (f c2) = true ->
    exp_sem aenv (highb01 n x y c1 c2) f =
      f[c2 |-> put_cu (f c2) ((majb true false (carry (get_cua (f c1)) n (get_cus n f x) (get_cus n f y))))].
Proof.
  intros.
  unfold highb01. unfold no_equal in H2.
  destruct H2 as [V1 [V2 [V3 [V4 [V5 V6]]]]].
  assert (nor_mode f c1) as X1. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_mode f c2) as X2. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_modes f x (aenv x)) as X3.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H0 in X3.
  assert (nor_modes f y (aenv y)) as X4.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H1 in X4.
  destruct c1. destruct c2.
  simpl. unfold MAJseq. rewrite (MAJseq'_correct (n-1) n); (try easy; try lia).
  rewrite highbit_correct_2; try lia.
  rewrite put_cu_cus. rewrite put_cu_cus.
  rewrite get_cus_cua by lia.
  rewrite put_cus_neq by lia.
  rewrite cus_get_eq; try lia.
  rewrite eupdate_index_neq by iner_p.
  erewrite inv_pexp_reverse. easy.
  apply MAJseq'_wt; try easy. apply H7. apply H8.  apply H6. 
  apply right_mode_exp_up_same. easy.
  apply qft_uniform_put_cu_same. easy.
  apply qft_gt_put_cu_same. easy.
  rewrite (MAJseq'_correct (n-1) n); (try easy; try lia).
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite get_cus_up by iner_p.
  rewrite eupdate_twice_neq by iner_p.
  rewrite put_cus_update_flip by iner_p.
  rewrite put_cus_update_flip by iner_p.
  apply eupdate_same_1. easy.
  unfold msma. bdestruct (n - 1 <? n - 1). lia.
  bdestruct (n - 1 =? n - 1).
  assert ((S (n - 1)) = n) by lia. rewrite H14. easy. lia.
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p. apply X3. easy.
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p. apply X4. easy.
  apply nor_mode_up ; iner_p. 
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p. apply X3. easy.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p. apply X3. easy.
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

Lemma negations_aux_1 :
  forall n x c v S v' r aenv,
    0 < n -> fst c <> x ->
    v < 2^n ->
    v' = nval false r -> nor_modes S x n ->
    get_cus n S x = nat2fb v -> S c = v' ->
    exp_sem aenv (X c; negator0 n x) S = (reg_push (S[c |-> nval true r]) x (2^n - 1 - v) n).
Proof.
  intros; subst. simpl.
  rewrite H5. unfold exchange. simpl.
  assert (reg_push (S [c |-> nval true r]) x v n = (S [c |-> nval true r])).
  apply put_cus_same.
  unfold nor_modes. intros. nor_mode_simpl. destruct c. iner_p. apply H3. easy.
  rewrite get_cus_up; try easy.
  rewrite <- H2.
  rewrite (negator0_sem n) ; try easy.
  unfold reg_push.
  rewrite put_cus_twice_eq. easy.
  unfold nor_modes. intros. nor_mode_simpl. destruct c. iner_p. apply H3. easy.
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

Lemma comparator01_wt : forall n x y c1 c2 aenv tenv, no_equal x y c1 c2 ->
    Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> Env.MapsTo (fst c1) Nor tenv ->
    Env.MapsTo (fst c2) Nor tenv -> well_typed_pexp aenv tenv (comparator01 n x y c1 c2) tenv.
Proof.
  Local Transparent highb01 highbit.
  intros. unfold comparator01.
  unfold no_equal in *.
  destruct H as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  apply pe_seq with (env' := tenv).
  apply pe_seq with (env' := tenv).
  apply pe_seq with (env' := tenv).
  constructor. constructor. easy.
  apply negator0_wt. easy.
  unfold highb01.
  apply pe_seq with (env' := tenv).
  apply pe_seq with (env' := tenv).
  apply MAJseq_wt; try easy.
  unfold highbit.
  apply pe_seq with (env' := tenv).
  apply pe_seq with (env' := tenv).
  apply pe_seq with (env' := tenv).
  apply pe_seq with (env' := tenv).
  constructor. constructor. easy.
  constructor. constructor. easy.
  apply cnot_wt_nor; try easy. iner_p.
  constructor. constructor. easy.
  constructor. constructor. easy.
  apply typed_inv_pexp.
  apply MAJseq_wt; try easy.
  apply typed_inv_pexp.
  apply pe_seq with (env' := tenv).
  constructor. constructor. easy.
  apply negator0_wt. easy.
  Local Opaque highb01 highbit.
Qed.

Lemma comparator01_correct :
  forall tenv aenv n x y c1 c2 v1 v2 f f' f'',
    0 < n ->  n = aenv x -> n = aenv y -> snd c1 < aenv (fst c1) -> snd c2 < aenv (fst c2) ->
    v1 < 2^n -> v2 < 2^n -> no_equal x y c1 c2 -> Env.MapsTo (fst c2) Nor tenv -> Env.MapsTo (fst c1) Nor tenv -> 
    Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f -> 
    f' = reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) false]) x v1 n) y v2 n ->
    f'' = reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) (¬(v1 <=? v2))]) x v1 n) y v2 n ->
    exp_sem aenv (comparator01 n x y c1 c2) f' = f''.
Proof.
  intros.
  unfold comparator01. remember ((X c1; negator0 n x)) as negations. simpl. rewrite H14 in *. rewrite H15 in *.
  unfold no_equal in *.
  destruct H6 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  assert (nor_mode f c1) as V1. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_mode f c2) as V2. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_modes f x (aenv x)) as V3.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H0 in V3.
  assert (nor_modes f y (aenv y)) as V4.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H1 in V4.
  destruct c1. destruct c2.
  rewrite eupdate_twice_neq by iner_p.
  rewrite reg_push_twice_neq by easy.
  rewrite reg_push_update_flip by iner_p.
  assert (exists b r, f (v, n0) = nval b r).
  unfold nor_mode in V1. destruct (f (v, n0)). exists b. exists r. easy. lia. lia.
  destruct H6. destruct H6.
  rewrite Heqnegations.
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
  rewrite H16. clear H16.
  erewrite inv_pexp_reverse. easy.
  apply pe_seq with (env' := tenv).
  constructor. constructor. easy.
  apply negator0_wt. easy.
  unfold reg_push.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same_1 ; try easy.
  apply nor_mode_cus_eq.
  apply nor_mode_up. iner_p. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy.
  unfold reg_push.
  apply qft_uniform_put_cus_same.
  rewrite <- put_cus_update_flip; try iner_p.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cu_same_1; try easy.
  apply right_mode_exp_up_same_1; try easy.
  apply nor_mode_up. iner_p. easy.
  apply right_mode_exp_up_same. easy.
  apply right_mode_exp_up_same_1; try easy.
  apply nor_mode_cus_eq.
  apply nor_mode_up. iner_p. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same_1 ; try easy.
  apply qft_gt_put_cus_same.
  unfold reg_push.
  rewrite <- put_cus_update_flip; try iner_p.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cu_same_1.
  apply qft_gt_put_cu_same. easy. easy.
  unfold nor_modes. intros.
  apply nor_mode_up. iner_p.
  apply nor_mode_up. iner_p.
  apply V4. easy.
  unfold reg_push.
  unfold nor_modes. intros.
  apply nor_mode_up. iner_p.
  apply nor_mode_cus_eq.
  apply nor_mode_up. iner_p.
  apply V3. easy.
  Check negations_aux.
  rewrite negations_aux with (r := x1); try easy.
  repeat rewrite cus_get_neq by iner_p.
  rewrite eupdate_index_eq.
  rewrite get_cus_put_eq; try lia.
  rewrite get_cus_put_neq; try lia.
  rewrite <- put_cus_update_flip with (f := (f [(v0, n1) |-> put_cu (f (v0, n1)) false])).
  rewrite get_cus_put_eq; try lia.
  assert ((get_cua (nval true x1)) = true). unfold get_cua. easy.
  rewrite H16.
  rewrite majb_carry_s_eq.
  specialize (carry_leb_equiv (n+1) v1 v2) as eq2.
  assert (n+1 -1 = n) by lia.
  rewrite H17 in eq2. clear H17.
  assert ((n + 1) = S n) by lia.
  rewrite H17 in eq2. clear H17. 
  rewrite Nat.pow_succ_r in eq2.
  assert (2 * 2 ^ n - 1 - v1 = 2 ^ n - 1 - v1 + 2 ^ n) by lia.
  rewrite H17 in eq2. rewrite eq2.
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
  repeat apply nor_mode_up ; iner_p. apply V4. easy.
  iner_p.
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p.
  apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p. apply V3. easy. iner_p.
  rewrite H6. unfold put_cu. easy.
  unfold reg_push.
  unfold nor_modes. intros. apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p.
  apply V3. easy.
  apply right_mode_exp_put_cus_same.
  assert (nval true x1 = put_cu (f (v,n0)) true).
  rewrite H6. easy. rewrite H16.
  apply right_mode_exp_up_same_1.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy.
  apply qft_uniform_put_cus_same.
  rewrite <- put_cus_update_flip by iner_p.
  apply qft_uniform_put_cus_same.
  assert (nval true x1 = put_cu (f (v,n0)) true).
  rewrite H6. easy. rewrite H16.
  apply qft_uniform_put_cu_same_1; try easy.
  assert (nval true x1 = put_cu (f (v,n0)) true).
  rewrite H6. easy. rewrite H16.
  apply right_mode_exp_up_same_1; try easy.
  apply nor_mode_up; iner_p.
  apply right_mode_exp_up_same; try easy.
  assert (nval true x1 = put_cu (f (v,n0)) true).
  rewrite H6. easy. rewrite H16.
  apply right_mode_exp_up_same_1; try easy.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same; try easy.
  apply qft_gt_put_cus_same.
  assert (nval true x1 = put_cu (f (v,n0)) true).
  rewrite H6. easy. rewrite H16.
  apply qft_gt_put_cu_same_1.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cu_same. easy.
  unfold nor_modes. intros. apply nor_mode_up; iner_p. apply V4. easy. easy.
  unfold nor_modes. intros. apply nor_mode_up; iner_p.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p. apply V3. easy.
  rewrite put_cus_neq; iner_p.
  rewrite eupdate_index_neq; iner_p.
  rewrite put_cus_neq; iner_p.
  rewrite eupdate_index_eq.
  rewrite get_put_cu. easy. easy. iner_p.
  rewrite H6. easy.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply V3. easy.
Qed.

Lemma comparator01_correct_1 :
  forall tenv aenv n x y c1 c2 v1 v2 f f',
    0 < n ->  n = aenv x -> n = aenv y -> snd c1 < aenv (fst c1) -> snd c2 < aenv (fst c2) ->
    v1 < 2^n -> v2 < 2^n -> no_equal x y c1 c2 -> Env.MapsTo (fst c2) Nor tenv -> Env.MapsTo (fst c1) Nor tenv -> 
    Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> right_mode_env aenv tenv f -> right_mode_env aenv tenv f' ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f -> 
    get_cus n f x = nat2fb v1 -> get_cus n f y = nat2fb v2 -> get_cua (f c1) = false -> get_cua (f c2) = false ->
    get_r (f c2) = get_r (f' c2) ->
    exp_sem aenv (comparator01 n x y c1 c2) f = f[c2 |-> put_cu (f' c2) (¬(v1 <=? v2))].
Proof.
  intros.
  unfold comparator01. remember ((X c1; negator0 n x)) as negations. simpl. rewrite Heqnegations in *.
  unfold no_equal in *.
  destruct H6 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  assert (nor_mode f c1) as V1. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_mode f c2) as V2. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_modes f x (aenv x)) as V3.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H0 in V3.
  assert (nor_modes f y (aenv y)) as V4.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H1 in V4.
  rewrite negations_aux_1 with (v := v1) (v' := f c1) (r := get_r (f c1)); try easy.
  rewrite highb01_correct with (tenv := tenv) (aenv := aenv); try easy.
  unfold reg_push.
  rewrite put_cus_neq_1 by iner_p.
  destruct c1. destruct c2.
  rewrite eupdate_index_neq by iner_p.
  rewrite put_cus_neq_1 by iner_p.
  rewrite eupdate_index_eq.
  rewrite get_put_cus_cut_n.
  rewrite cut_n_mod.
  rewrite Nat.mod_small by lia.
  unfold get_cua.
  rewrite get_cus_put_neq by iner_p.
  rewrite get_cus_up by iner_p.
  rewrite H16.
  rewrite majb_carry_s_eq.
  specialize (carry_leb_equiv (n+1) v1 v2) as eq2.
  assert (n+1 -1 = n) by lia.
  rewrite H6 in eq2. clear H6.
  assert ((n + 1) = S n) by lia.
  rewrite H6 in eq2. clear H6. 
  rewrite Nat.pow_succ_r in eq2.
  assert (2 * 2 ^ n - 1 - v1 = 2 ^ n - 1 - v1 + 2 ^ n) by lia.
  rewrite H6 in eq2. rewrite eq2.
  bt_simpl.
  erewrite inv_pexp_reverse. easy.
  apply pe_seq with (env' := tenv).
  constructor. constructor. easy.
  apply negator0_wt. easy.
  apply right_mode_exp_up_same_1; try easy.
  apply H12 in H7. unfold nor_mode. inv H7. easy. easy.
  apply qft_uniform_put_cu_same_2; try easy.
  apply qft_gt_put_cu_same_1; try easy.
  apply H12 in H7. unfold nor_mode. inv H7. easy. easy.
  rewrite negations_aux_1 with (v := v1) (v' := f (v, n0)) (r := get_r (f (v, n0))); try easy.
  rewrite eupdate_twice_neq by iner_p.
  rewrite reg_push_update_flip by iner_p.
  unfold reg_push.
  assert (nor_mode f' (v0, n1)).
  apply H12 in H7. unfold nor_mode. inv H7. easy. easy.
  unfold nor_mode,put_cu,get_r in *.
  destruct (f (v0, n1)). destruct (f' (v0, n1)). subst. easy. easy. easy. easy. easy. iner_p.
  unfold nor_mode,get_r,get_cua in *.
  destruct (f (v, n0)). subst. easy. easy. easy.  
  unfold nor_modes. intros. nor_mode_simpl. apply V3. easy. 
  rewrite get_cus_up by iner_p. easy.
  rewrite eupdate_index_neq by iner_p. easy.
  1-7:lia. 
  unfold nor_modes. intros. nor_mode_simpl. apply V3. easy. 
  unfold reg_push.
  apply right_mode_exp_put_cus_same.
  assert (nval true (get_r (f c1)) = put_cu (f c1) true).
  unfold nor_mode,get_r,put_cu in *.
  destruct (f c1). subst. easy. easy. easy.
  rewrite H6.  
  apply right_mode_exp_up_same_1; try easy.
  apply qft_uniform_put_cus_same.
  assert (nval true (get_r (f c1)) = put_cu (f c1) true).
  unfold nor_mode,get_r,put_cu in *.
  destruct (f c1). subst. easy. easy. easy.
  rewrite H6.  
  apply qft_uniform_put_cu_same; try easy.
  assert (nval true (get_r (f c1)) = put_cu (f c1) true).
  unfold nor_mode,get_r,put_cu in *.
  destruct (f c1). subst. easy. easy. easy.
  rewrite H6.  
  apply right_mode_exp_up_same_1; try easy.
  apply qft_gt_put_cus_same.
  assert (nval true (get_r (f c1)) = put_cu (f c1) true).
  unfold nor_mode,get_r,put_cu in *.
  destruct (f c1). subst. easy. easy. easy. rewrite H6.
  apply qft_gt_put_cu_same. easy.
  unfold nor_modes. intros. apply nor_mode_up; iner_p. apply V3. easy.
  unfold reg_push.
  rewrite put_cus_neq_1 by iner_p.
  destruct c1.
  rewrite eupdate_index_neq by iner_p. easy. iner_p. 
  unfold nor_mode,get_r,get_cua in *.
  destruct (f c1). subst. easy. easy. easy.
Qed.

Lemma comparator01_correct_true :
  forall tenv aenv n x y c1 c2 v1 v2 f f' f'',
    0 < n ->  n = aenv x -> n = aenv y -> snd c1 < aenv (fst c1) -> snd c2 < aenv (fst c2) ->
    v1 < 2^n -> v2 < 2^n -> no_equal x y c1 c2 -> Env.MapsTo (fst c2) Nor tenv -> Env.MapsTo (fst c1) Nor tenv -> 
    Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f -> 
    f' = reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) true]) x v1 n) y v2 n ->
    f'' = reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) (v1 <=? v2)]) x v1 n) y v2 n ->
    exp_sem aenv (comparator01 n x y c1 c2) f' = f''.
Proof.
  intros.
  unfold comparator01. remember ((X c1; negator0 n x)) as negations. simpl.
  rewrite H14 in *. rewrite H15 in *. rewrite Heqnegations in *.
  clear H14. clear H15. clear Heqnegations.
  unfold no_equal in *.
  destruct H6 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  assert (nor_mode f c1) as V1. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_mode f c2) as V2. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_modes f x (aenv x)) as V3.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H0 in V3.
  assert (nor_modes f y (aenv y)) as V4.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H1 in V4.
  destruct c1. destruct c2.
  rewrite eupdate_twice_neq by iner_p.
  rewrite reg_push_twice_neq by easy.
  rewrite reg_push_update_flip by iner_p.
  assert (exists b r, f (v, n0) = nval b r).
  unfold nor_mode in V1. destruct (f (v, n0)). exists b. exists r. easy. lia. lia.
  destruct H6. destruct H6.
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
  rewrite H14. clear H14.
  erewrite inv_pexp_reverse. easy.
  apply pe_seq with (env' := tenv).
  constructor. constructor. easy.
  apply negator0_wt. easy.
  unfold reg_push.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same_1 ; try easy.
  apply nor_mode_cus_eq.
  apply nor_mode_up. iner_p. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy.
  unfold reg_push.
  apply qft_uniform_put_cus_same.
  rewrite <- put_cus_update_flip; try iner_p.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cu_same_1; try easy.
  apply right_mode_exp_up_same_1; try easy.
  apply nor_mode_up. iner_p. easy.
  apply right_mode_exp_up_same. easy.
  apply right_mode_exp_up_same_1; try easy.
  apply nor_mode_cus_eq.
  apply nor_mode_up. iner_p. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same_1 ; try easy.
  apply qft_gt_put_cus_same.
  unfold reg_push.
  rewrite <- put_cus_update_flip; try iner_p.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cu_same_1.
  apply qft_gt_put_cu_same. easy. easy.
  unfold nor_modes. intros.
  apply nor_mode_up. iner_p.
  apply nor_mode_up. iner_p.
  apply V4. easy.
  unfold reg_push.
  unfold nor_modes. intros.
  apply nor_mode_up. iner_p.
  apply nor_mode_cus_eq.
  apply nor_mode_up. iner_p.
  apply V3. easy.
  Check negations_aux.
  rewrite negations_aux with (r := x1); try easy.
  repeat rewrite cus_get_neq by iner_p.
  rewrite eupdate_index_eq.
  rewrite get_cus_put_eq; try lia.
  rewrite get_cus_put_neq; try lia.
  rewrite <- put_cus_update_flip with (f := (f [(v0, n1) |-> put_cu (f (v0, n1)) true])).
  rewrite get_cus_put_eq; try lia.
  assert ((get_cua (nval true x1)) = true). unfold get_cua. easy.
  rewrite H14.
  rewrite majb_carry_s_eq.
  specialize (carry_leb_equiv (n+1) v1 v2) as eq2.
  assert (n+1 -1 = n) by lia.
  rewrite H15 in eq2. clear H15.
  assert ((n + 1) = S n) by lia.
  rewrite H15 in eq2. clear H15. 
  rewrite Nat.pow_succ_r in eq2.
  assert (2 * 2 ^ n - 1 - v1 = 2 ^ n - 1 - v1 + 2 ^ n) by lia.
  rewrite H15 in eq2. rewrite eq2.
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
  repeat apply nor_mode_up ; iner_p. apply V4. easy.
  iner_p.
  unfold nor_modes. intros.
  apply nor_mode_up ; iner_p.
  apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p. apply V3. easy. iner_p.
  rewrite H6. unfold put_cu. easy.
  unfold reg_push.
  unfold nor_modes. intros. apply nor_mode_cus_eq.
  apply nor_mode_up ; iner_p.
  apply V3. easy.
  apply right_mode_exp_put_cus_same.
  assert (nval true x1 = put_cu (f (v,n0)) true).
  rewrite H6. easy. rewrite H14.
  apply right_mode_exp_up_same_1.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy.
  apply qft_uniform_put_cus_same.
  rewrite <- put_cus_update_flip by iner_p.
  apply qft_uniform_put_cus_same.
  assert (nval true x1 = put_cu (f (v,n0)) true).
  rewrite H6. easy. rewrite H14.
  apply qft_uniform_put_cu_same_1; try easy.
  assert (nval true x1 = put_cu (f (v,n0)) true).
  rewrite H6. easy. rewrite H14.
  apply right_mode_exp_up_same_1; try easy.
  apply nor_mode_up; iner_p.
  apply right_mode_exp_up_same; try easy.
  assert (nval true x1 = put_cu (f (v,n0)) true).
  rewrite H6. easy. rewrite H14.
  apply right_mode_exp_up_same_1; try easy.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same; try easy.
  apply qft_gt_put_cus_same.
  assert (nval true x1 = put_cu (f (v,n0)) true).
  rewrite H6. easy. rewrite H14.
  apply qft_gt_put_cu_same_1.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cu_same. easy.
  unfold nor_modes. intros. apply nor_mode_up; iner_p. apply V4. easy. easy.
  unfold nor_modes. intros. apply nor_mode_up; iner_p.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p. apply V3. easy.
  rewrite put_cus_neq; iner_p.
  rewrite eupdate_index_neq; iner_p.
  rewrite put_cus_neq; iner_p.
  rewrite eupdate_index_eq.
  rewrite get_put_cu. easy. easy. iner_p.
  rewrite H6. easy.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq. apply nor_mode_up; iner_p.
  apply V3. easy.
Qed.

Lemma comparator01_correct_true_1 :
  forall tenv aenv n x y c1 c2 v1 v2 f f',
    0 < n ->  n = aenv x -> n = aenv y -> snd c1 < aenv (fst c1) -> snd c2 < aenv (fst c2) ->
    v1 < 2^n -> v2 < 2^n -> no_equal x y c1 c2 -> Env.MapsTo (fst c2) Nor tenv -> Env.MapsTo (fst c1) Nor tenv -> 
    Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> right_mode_env aenv tenv f -> right_mode_env aenv tenv f' ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f -> 
    get_cus n f x = nat2fb v1 -> get_cus n f y = nat2fb v2 -> get_cua (f c1) = false -> get_cua (f c2) = true ->
    get_r (f c2) = get_r (f' c2) ->
    exp_sem aenv (comparator01 n x y c1 c2) f = f[c2 |-> put_cu (f' c2) ((v1 <=? v2))].
Proof.
  intros.
  unfold comparator01. remember ((X c1; negator0 n x)) as negations. simpl. rewrite Heqnegations in *.
  unfold no_equal in *.
  destruct H6 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  assert (nor_mode f c1) as V1. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_mode f c2) as V2. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_modes f x (aenv x)) as V3.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H0 in V3.
  assert (nor_modes f y (aenv y)) as V4.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H1 in V4.
  rewrite negations_aux_1 with (v := v1) (v' := f c1) (r := get_r (f c1)); try easy.
  rewrite highb01_correct_2 with (tenv := tenv) (aenv := aenv); try easy.
  unfold reg_push.
  rewrite put_cus_neq_1 by iner_p.
  destruct c1.
  rewrite eupdate_index_neq by iner_p.
  rewrite put_cus_neq_1 by iner_p.
  rewrite eupdate_index_eq.
  rewrite get_put_cus_cut_n.
  rewrite cut_n_mod.
  rewrite Nat.mod_small by lia.
  unfold get_cua.
  rewrite get_cus_put_neq by iner_p.
  rewrite get_cus_up by iner_p.
  rewrite H16.
  rewrite majb_carry_s_eq.
  specialize (carry_leb_equiv (n+1) v1 v2) as eq2.
  assert (n+1 -1 = n) by lia.
  rewrite H6 in eq2. clear H6.
  assert ((n + 1) = S n) by lia.
  rewrite H6 in eq2. clear H6. 
  rewrite Nat.pow_succ_r in eq2.
  assert (2 * 2 ^ n - 1 - v1 = 2 ^ n - 1 - v1 + 2 ^ n) by lia.
  rewrite H6 in eq2. rewrite eq2.
  bt_simpl.
  erewrite inv_pexp_reverse. easy.
  apply pe_seq with (env' := tenv).
  constructor. constructor. easy.
  apply negator0_wt. easy.
  apply right_mode_exp_up_same_1; try easy.
  apply H12 in H7. unfold nor_mode. inv H7. easy. easy.
  apply qft_uniform_put_cu_same_2; try easy.
  apply qft_gt_put_cu_same_1; try easy.
  apply H12 in H7. unfold nor_mode. inv H7. easy. easy.
  rewrite negations_aux_1 with (v := v1) (v' := f (v, n0)) (r := get_r (f (v, n0))); try easy.
  rewrite eupdate_twice_neq by iner_p.
  rewrite reg_push_update_flip by iner_p.
  unfold reg_push.
  assert (nor_mode f' c2).
  apply H12 in H7. unfold nor_mode. inv H7. easy. easy.
  unfold nor_mode,put_cu,get_r in *.
  destruct (f c2). destruct (f' c2). subst. easy. easy. easy. easy. easy. iner_p.
  unfold nor_mode,get_r,get_cua in *.
  destruct (f (v, n0)). subst. easy. easy. easy.  
  unfold nor_modes. intros. nor_mode_simpl. apply V3. easy. 
  rewrite get_cus_up by iner_p. easy.
  rewrite eupdate_index_neq by iner_p. easy.
  1-7:lia. 
  unfold nor_modes. intros. nor_mode_simpl. apply V3. easy. 
  unfold reg_push.
  apply right_mode_exp_put_cus_same.
  assert (nval true (get_r (f c1)) = put_cu (f c1) true).
  unfold nor_mode,get_r,put_cu in *.
  destruct (f c1). subst. easy. easy. easy.
  rewrite H6.  
  apply right_mode_exp_up_same_1; try easy.
  apply qft_uniform_put_cus_same.
  assert (nval true (get_r (f c1)) = put_cu (f c1) true).
  unfold nor_mode,get_r,put_cu in *.
  destruct (f c1). subst. easy. easy. easy.
  rewrite H6.  
  apply qft_uniform_put_cu_same; try easy.
  assert (nval true (get_r (f c1)) = put_cu (f c1) true).
  unfold nor_mode,get_r,put_cu in *.
  destruct (f c1). subst. easy. easy. easy.
  rewrite H6.  
  apply right_mode_exp_up_same_1; try easy.
  apply qft_gt_put_cus_same.
  assert (nval true (get_r (f c1)) = put_cu (f c1) true).
  unfold nor_mode,get_r,put_cu in *.
  destruct (f c1). subst. easy. easy. easy. rewrite H6.
  apply qft_gt_put_cu_same. easy.
  unfold nor_modes. intros. apply nor_mode_up; iner_p. apply V3. easy.
  unfold reg_push.
  rewrite put_cus_neq_1 by iner_p.
  destruct c1.
  rewrite eupdate_index_neq by iner_p. easy. iner_p. 
  unfold nor_mode,get_r,get_cua in *.
  destruct (f c1). subst. easy. easy. easy.
Qed.

Local Opaque comparator01.


Lemma subtractor01_wt : forall n x y c aenv tenv, x <> y -> x <> fst c -> y <> fst c ->
    Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> Env.MapsTo (fst c) Nor tenv ->
    well_typed_pexp aenv tenv (subtractor01 n x y c) tenv.
Proof.
  intros. unfold subtractor01.
  apply pe_seq with (env' := tenv).
  apply pe_seq with (env' := tenv).
  apply pe_seq with (env' := tenv).
  constructor. constructor. easy.
  apply negator0_wt. easy.
  Local Transparent adder01.
  unfold adder01.
  Local Opaque adder01.
  apply pe_seq with (env' := tenv).
  apply MAJseq_wt; try easy.
  apply UMAseq_wt; try easy.
  apply typed_inv_pexp.
  apply pe_seq with (env' := tenv).
  constructor. constructor. easy.
  apply negator0_wt. easy.
Qed.


Lemma negator0_fresh : forall n x c2 aenv, x <> fst c2 ->
    exp_fresh aenv c2 (negator0 n x).
Proof.
  induction n;intros;simpl.
  constructor. iner_p.
  constructor. apply IHn. easy. constructor. iner_p.
Qed.


Lemma adder01_fresh : forall n x y c c2 aenv, x <> fst c2 -> y <> fst c2 -> c <> c2 ->
    exp_fresh aenv c2 (adder01 n x y c).
Proof.
  intros.
  Local Transparent adder01.
  unfold adder01.
  Local Opaque adder01.
  constructor. iner_p.
  apply MAJseq_fresh; try easy.
  apply UMAseq_fresh; try easy.
Qed.


Lemma subtractor01_fresh : forall n x y c c2 aenv, x <> fst c2 -> y <> fst c2 -> c <> c2 ->
    exp_fresh aenv c2 (subtractor01 n x y c).
Proof.
  intros. unfold subtractor01.
  constructor. constructor.
  constructor. constructor. destruct c2. destruct c. iner_p.
  apply negator0_fresh. easy.
  apply adder01_fresh; try easy.
  apply fresh_inv_exp.
  constructor. constructor. destruct c2. destruct c. iner_p.
  apply negator0_fresh. easy.
Qed.

Lemma negator0_neu : forall l n x, exp_neu_l l [] (negator0 n x) [].
Proof.
  induction n;intros;simpl.
  constructor.
  apply seq_neul with (l' := []).
  apply IHn. constructor.
Qed.

Lemma adder01_neu : forall l n x y c, exp_neu_l l [] (adder01 n x y c) [].
Proof.
  intros.
  Local Transparent adder01.
  unfold adder01.
  Local Opaque adder01.
  apply seq_neul with (l' := []).
  apply MAJseq_neu; try easy.
  apply UMAseq_neu; try easy.
Qed.

Lemma subtractor01_neu : forall l n x y c, exp_neu_l l [] (subtractor01 n x y c) [].
Proof.
  intros. unfold subtractor01.
  apply seq_neul with (l' := []).
  apply seq_neul with (l' := []).
  apply seq_neul with (l' := []).
  constructor. apply negator0_neu.
  apply adder01_neu.
  apply neu_l_inv_exp.
  unfold exp_neu_prop. intros.
  simpl in *. lia.
  apply seq_neul with (l' := []).
  constructor. apply negator0_neu.
Qed.

Lemma modadder21_wt : forall aenv tenv n x y M c1 c2,
    no_equal_5 x y M c1 c2 -> Env.MapsTo (fst c1) Nor tenv -> Env.MapsTo (fst c2) Nor tenv -> 
    Env.MapsTo M Nor tenv -> Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> 
    well_typed_pexp aenv tenv (modadder21 n x y M c1 c2) tenv.
Proof.
  intros. unfold modadder21.
  unfold no_equal_5 in *.
  destruct H as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  apply pe_seq with (env' := tenv).
  apply pe_seq with (env' := tenv).
  apply pe_seq with (env' := tenv).
  apply pe_seq with (env' := tenv).
  Local Transparent adder01.
  unfold adder01.
  Local Opaque adder01.
  apply pe_seq with (env' := tenv).
  apply MAJseq_wt; try iner_p.
  apply UMAseq_wt; try iner_p.
  apply comparator01_wt; try iner_p.
  unfold no_equal. split. iner_p.
  split; iner_p.
  split; iner_p.
  split; iner_p.
  split; iner_p. destruct c1. destruct c2. iner_p.
  constructor. constructor. easy.
  apply pcu_nor. easy.
  apply subtractor01_fresh; try easy.
  unfold exp_neu. intros.
  apply subtractor01_neu.
  apply subtractor01_wt; try easy. iner_p.
  apply typed_inv_pexp.
  apply comparator01_wt; try easy.
  unfold no_equal. split. lia. split. iner_p. split. easy. split. easy. split. easy.
  destruct c1. destruct c2. iner_p.
Qed.

Lemma moddoubler01_wt: forall aenv tenv n x y c1 c2,
    no_equal x y c1 c2 -> Env.MapsTo (fst c1) Nor tenv -> Env.MapsTo (fst c2) Nor tenv -> 
    Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> 
    well_typed_pexp aenv tenv (moddoubler01 n x y c1 c2) tenv.
Proof.
  intros. unfold moddoubler01.
  unfold no_equal in *.
  destruct H as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  apply pe_seq with (env' := tenv).
  apply pe_seq with (env' := tenv).
  unfold doubler1. constructor. constructor. easy.
  constructor. constructor. easy.
  apply pe_seq with (env' := tenv).
  apply comparator01_wt; try easy.
  unfold no_equal. split. iner_p. easy.
  apply pcu_nor; try easy.
  apply subtractor01_fresh; try iner_p.
  unfold exp_neu. intros.
  apply subtractor01_neu.
  apply subtractor01_wt; try easy. lia.
Qed.

Lemma modsummer'_wt : forall i n aenv tenv M x y c1 s fc,
    i < n -> no_equal_5a x y M s c1 -> Env.MapsTo s Nor tenv -> Env.MapsTo (fst c1) Nor tenv -> 
    Env.MapsTo M Nor tenv -> Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> 
    well_typed_pexp aenv tenv (modsummer' i n M x y c1 s fc) tenv.
Proof.
  induction i;intros;simpl.
  constructor. constructor.
  apply pe_seq with (env' := tenv).
  apply pe_seq with (env' := tenv).
  apply IHi; try easy. lia.
  destruct (fc i).
  apply modadder21_wt; try easy.
  destruct H0 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  unfold no_equal_5 in *. split. lia. split. easy. split. easy.
  split. easy. split. easy. split. easy. split. easy. split. easy.
  split. easy. iner_p. constructor. constructor.
  apply moddoubler01_wt; try easy.
  unfold no_equal.
  destruct H0 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  split. iner_p. split. easy. split. easy. split. easy.
  split. easy. iner_p.
Qed.

Lemma modsummer_wt : forall n aenv tenv M x y c1 s fc,
    0 < n -> no_equal_5a x y M s c1 -> Env.MapsTo s Nor tenv -> Env.MapsTo (fst c1) Nor tenv -> 
    Env.MapsTo M Nor tenv -> Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> 
    well_typed_pexp aenv tenv (modsummer n M x y c1 s fc) tenv.
Proof.
  intros. unfold modsummer.
  apply modsummer'_wt; try easy. lia.
Qed.

Lemma modmult_half_wt : forall n aenv tenv M x y c1 s fc,
    0 < n -> no_equal_5a x y M s c1 -> Env.MapsTo s Nor tenv -> Env.MapsTo (fst c1) Nor tenv -> 
    Env.MapsTo M Nor tenv -> Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> 
    well_typed_pexp aenv tenv (modmult_half n M x y c1 s fc) tenv.
Proof.
  intros. unfold modmult_half.
  apply pe_seq with (env' := tenv).
  apply modsummer_wt; try easy.
  apply typed_inv_pexp.
  apply modsummer_wt; try easy.
Qed.

(* The correctness proof of the subtractor. *)
Lemma subtractor01_correct_fb : 
  forall n f x y c aenv tenv ,
    0 < n -> aenv x = n -> aenv y = n -> snd c < aenv (fst c) ->
    Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> Env.MapsTo (fst c) Nor tenv ->
    right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    x <> y -> x <> fst c -> y <> fst c ->
    exp_sem aenv (subtractor01 n x y c) f =
        (put_cus f y (sumfb (¬ (get_cua (f c))) (negatem n (get_cus n f x)) (get_cus n f y)) n).
Proof.
  intros.
  assert (nor_modes f x n).
  rewrite <- H0.
  apply type_nor_modes with (env := tenv); try easy.
  assert (nor_modes f y n).
  rewrite <- H1.
  apply type_nor_modes with (env := tenv); try easy.
  assert (nor_mode f c).
  apply type_nor_mode with (env := tenv) (aenv := aenv); try easy.
  unfold subtractor01. remember (X c) as negations. simpl.
  rewrite Heqnegations in *.
  rewrite x_nor_sem with (v := put_cu (f c) (¬ (get_cua (f c)))); try easy.
  rewrite negator0_correct with (n := n); try easy.
  rewrite adder01_correct_fb; try easy.
  rewrite put_cus_update_flip by iner_p.
  rewrite eupdate_index_eq.
  rewrite get_put_cu by easy.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite get_put_cus_cut_n.
  rewrite get_cus_put_neq by lia.
  rewrite get_cus_up by iner_p.
  rewrite get_cus_up by iner_p.
  rewrite put_cus_twice_neq by iner_p.
  assert ((exp_sem aenv (inv_exp (negator0 n x))
     (put_cus
        (put_cus (f [c |-> put_cu (f c) (¬ (get_cua (f c)))]) y
           (sumfb (¬ (get_cua (f c))) (cut_n (negatem n (get_cus n f x)) n)
              (get_cus n f y)) n) x (negatem n (get_cus n f x)) n))
       = (put_cus (f [c |-> put_cu (f c) (¬ (get_cua (f c)))]) y
           (sumfb (¬ (get_cua (f c))) (cut_n (negatem n (get_cus n f x)) n)
              (get_cus n f y)) n)).
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv); try easy.
  apply negator0_wt. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same ; try easy.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cu_same; try easy.
  apply right_mode_exp_up_same ; try easy.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cu_same; try easy.
  unfold nor_modes. intros. nor_mode_simpl. apply H13. easy.
  rewrite negator0_correct with (n := n); try easy.
  rewrite get_cus_put_neq by lia.
  rewrite get_cus_up by iner_p. easy.
  unfold nor_modes. intros. nor_mode_simpl. apply H12. easy.
  rewrite H15.
  rewrite put_cus_update_flip by iner_p.
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv); try easy.
  constructor. constructor. easy.
  apply right_mode_exp_put_cus_same. easy.
  apply qft_uniform_put_cus_same. easy. easy.
  apply qft_gt_put_cus_same. easy.
  easy.
  rewrite x_nor_sem with (v :=  put_cu (f c) (¬ (get_cua (f c)))); try easy.
  rewrite cut_n_eq. easy.
  intros.
  unfold negatem,get_cus.
  bdestruct (i <? n). lia. easy.
  destruct c. nor_mode_simpl.
  rewrite put_cus_neq_1 by iner_p. easy.
  unfold nor_modes. intros. nor_mode_simpl. apply H12. easy.
  unfold nor_modes. intros. nor_mode_simpl. apply H12. easy.
  unfold nor_modes. intros. nor_mode_simpl. apply H13. easy.
  unfold nor_mode in *. rewrite put_cus_neq_1 by iner_p.
  rewrite eupdate_index_eq.
  unfold put_cu.
  destruct (f c). easy. easy. easy.
  unfold nor_modes. intros. nor_mode_simpl. apply H12. easy.
Qed.


Lemma subtractor01_correct :
  forall tenv aenv n x y c1 v1 v2 f f' f'',
    0 < n -> n = aenv x -> n = aenv y -> snd c1 < aenv (fst c1) ->
    v1 < 2^n -> v2 < 2^n -> x <> y -> x <> fst c1 -> y <> fst c1 ->
    Env.MapsTo (fst c1) Nor tenv -> Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv ->
    right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f -> 
    f' = reg_push (reg_push (f[c1 |-> put_cu (f c1) false]) x v1 n) y v2 n ->
    f'' = reg_push (reg_push (f[c1 |-> put_cu (f c1) false]) x v1 n) y (v2 + 2^n - v1) n ->
    exp_sem aenv (subtractor01 n x y c1) f' = f''.
Proof.
  intros.
  unfold subtractor01. remember (X c1; negator0 n x) as negations. simpl.
  rewrite H14 in *. rewrite H15 in *. rewrite Heqnegations in *.
  clear H14. clear H15. clear Heqnegations.
  assert (nor_mode f c1) as V1. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_modes f x (aenv x)) as V3.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H0 in V3.
  assert (nor_modes f y (aenv y)) as V4.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H1 in V4.
  rewrite reg_push_twice_neq by iner_p.
  rewrite reg_push_update_flip by iner_p.
  destruct (f c1) eqn:eq2.
  rewrite negations_aux with (r:=r); (try lia; try easy).
  rewrite <- reg_push_update_flip by iner_p.
  rewrite reg_push_twice_neq by iner_p.
  assert (nval true r = put_cu (f c1) true).
  rewrite eq2. easy. rewrite H14. 
  Check adder01_correct_carry1.
  rewrite adder01_correct_carry1 with (S0 := f) (v1 := (2 ^ n - 1 - v1)) (v2:=v2)
       (S'' := reg_push (reg_push (f [c1 |-> put_cu (f c1) true])
              x (2 ^ n - 1 - v1) n) y ((2 ^ n - 1 - v1) + v2 + 1) n); try easy.
  rewrite reg_push_twice_neq by iner_p.
  rewrite reg_push_update_flip by iner_p.
  erewrite inv_pexp_reverse. unfold put_cu. easy.
  apply pe_seq with (env' := tenv).
  constructor. constructor. easy.
  apply negator0_wt. easy.
  unfold reg_push.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  assert (nval false r = put_cu (f c1) false).
  unfold put_cu. rewrite eq2. easy. rewrite H15.
  apply right_mode_exp_up_same ; try easy.
  unfold reg_push.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cus_same.
  assert (nval false r = put_cu (f c1) false).
  unfold put_cu. rewrite eq2. easy. rewrite H15.
  apply qft_uniform_put_cu_same; try easy.
  assert (nval false r = put_cu (f c1) false).
  unfold put_cu. rewrite eq2. easy. rewrite H15.
  apply right_mode_exp_up_same; try easy.
  apply right_mode_exp_put_cus_same.
  assert (nval false r = put_cu (f c1) false).
  unfold put_cu. rewrite eq2. easy. rewrite H15.
  apply right_mode_exp_up_same ; try easy.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cus_same.
  assert (nval false r = put_cu (f c1) false).
  unfold put_cu. rewrite eq2. easy. rewrite H15.
  apply qft_gt_put_cu_same. easy.
  unfold nor_modes. intros.
  assert (nval false r = put_cu (f c1) false).
  unfold put_cu. rewrite eq2. easy. rewrite H16.
  apply nor_mode_up. iner_p. apply V3. easy.
  assert (nval false r = put_cu (f c1) false).
  unfold put_cu. rewrite eq2. easy. rewrite H15.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq.
  apply nor_mode_up. iner_p. apply V4. easy.
  rewrite reg_push_twice_neq by iner_p.
  rewrite reg_push_update_flip by iner_p.
  rewrite negations_aux with (r:=r); (try lia; try easy).
  rewrite <- H14.
  assert ((2 ^ n - 1 - v1 + v2 + 1) = (v2 + 2 ^ n - v1)) by lia.
  rewrite H15. easy. iner_p.
  unfold nor_modes. intros.
  unfold reg_push. apply nor_mode_cus_eq. apply V3. easy. lia. iner_p.
  unfold nor_modes. intros.
  unfold reg_push. apply nor_mode_cus_eq. apply V3. easy.
  unfold nor_mode in V1. rewrite eq2 in V1. lia.
  unfold nor_mode in V1. rewrite eq2 in V1. lia.
Qed.

Local Opaque subtractor01.

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
    0 < n ->  n = aenv x -> n = aenv y -> snd c1 < aenv (fst c1) -> snd c2 < aenv (fst c2) ->
    v1 < 2^n -> v2 < 2^n -> no_equal x y c1 c2 -> Env.MapsTo (fst c2) Nor tenv -> Env.MapsTo (fst c1) Nor tenv -> 
    Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f -> right_mode_env aenv tenv f' ->
    get_r (f c1) = get_r (f' c1) -> get_r (f c2) = get_r (f' c2) ->
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
  unfold put_cu in *. unfold get_r in H15. unfold get_r in H16.
  assert (nor_mode f c1) as V1. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_mode f c2) as V2. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_modes f x (aenv x)) as V3.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H0 in V3.
  assert (nor_modes f y (aenv y)) as V4.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H1 in V4.
  assert (nor_mode f' c1) as V5. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_mode f' c2) as V6. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  unfold nor_mode in V1. unfold nor_mode in V2.
  destruct (f c1) eqn:eq2.  destruct (f c2) eqn:eq3.
  unfold nor_mode in V5. unfold nor_mode in V6.
  destruct (f' c1) eqn:eq4.  destruct (f' c2) eqn:eq5. subst.
  rewrite eq1. 1-14:easy.
Qed.

Lemma comparator01_sem_true :
  forall tenv aenv n x y c1 c2 v1 v2 f f',
    0 < n ->  n = aenv x -> n = aenv y -> snd c1 < aenv (fst c1) -> snd c2 < aenv (fst c2) ->
    v1 < 2^n -> v2 < 2^n -> no_equal x y c1 c2 -> Env.MapsTo (fst c2) Nor tenv -> Env.MapsTo (fst c1) Nor tenv -> 
    Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f -> right_mode_env aenv tenv f' ->
    get_r (f c1) = get_r (f' c1) -> get_r (f c2) = get_r (f' c2) ->
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
  unfold put_cu in *. unfold get_r in H15. unfold get_r in H16.
  assert (nor_mode f c1) as V1. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_mode f c2) as V2. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_modes f x (aenv x)) as V3.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H0 in V3.
  assert (nor_modes f y (aenv y)) as V4.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H1 in V4.
  assert (nor_mode f' c1) as V5. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_mode f' c2) as V6. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  unfold nor_mode in V1. unfold nor_mode in V2.
  destruct (f c1) eqn:eq2.  destruct (f c2) eqn:eq3.
  unfold nor_mode in V5. unfold nor_mode in V6.
  destruct (f' c1) eqn:eq4.  destruct (f' c2) eqn:eq5. subst.
  rewrite eq1. 1-14:easy.
Qed.

Lemma subtractor01_sem :
  forall tenv aenv n x y c1 v1 v2 f f',
    0 < n -> n = aenv x -> n = aenv y -> snd c1 < aenv (fst c1) ->
    v1 < 2^n -> v2 < 2^n -> x <> y -> x <> fst c1 -> y <> fst c1 ->
    Env.MapsTo (fst c1) Nor tenv -> Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv ->
    right_mode_env aenv tenv f -> right_mode_env aenv tenv f' ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f -> 
    get_r (f c1) = get_r (f' c1) ->
    exp_sem aenv (subtractor01 n x y c1) (reg_push (reg_push (f[c1 |-> put_cu (f' c1) false]) x v1 n) y v2 n) 
     = (reg_push (reg_push (f[c1 |-> put_cu (f' c1) false]) x v1 n) y (v2 + 2^n - v1) n).
Proof.
  intros.
  specialize (subtractor01_correct tenv aenv n x y c1 v1 v2 f
     (reg_push (reg_push (f [c1 |-> put_cu (f c1) false]) x v1 n) y v2 n)
     (reg_push (reg_push (f [c1 |-> put_cu (f c1) false]) x v1 n) y
        (v2 + 2 ^ n - v1) n) H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11) as eq1.
  unfold put_cu,get_r in *.
  assert (nor_mode f c1) as V1. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_mode f' c1) as V2. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_modes f x (aenv x)) as V3.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H0 in V3.
  assert (nor_modes f y (aenv y)) as V4.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H1 in V4.
  unfold nor_mode in V1. unfold nor_mode in V2.
  destruct (f c1) eqn:eq2. destruct (f' c1) eqn:eq4.
  subst. rewrite eq1. 1-5:easy.
  1-4:lia.
Qed.

(* The correctness statement of the modulo adder. *)
Lemma modadder21_correct :
  forall tenv aenv n x y M c1 c2 v1 v2 vM f,
    0 < n -> v1 < vM -> v2 < vM -> vM < 2^(n-1) -> no_equal_5 x y M c1 c2 ->
    n = aenv M -> n = aenv x -> n = aenv y -> snd c1 < aenv (fst c1) -> snd c2 < aenv (fst c2) ->
    Env.MapsTo (fst c1) Nor tenv -> Env.MapsTo (fst c2) Nor tenv -> 
    Env.MapsTo M Nor tenv -> Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> 
    right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    exp_sem aenv (modadder21 n x y M c1 c2) 
      (reg_push (reg_push (reg_push 
                 ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) false]) M vM n) y v2 n) x v1 n)
    = (reg_push (reg_push (reg_push 
                 ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) false]) M vM n) y v2 n) x ((v1 + v2) mod vM) n).
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
  remember (X c2) as csub02. simpl.
  rewrite Heqcsub01 in *. rewrite Heqcsub02 in *.
  clear Heqcsub01. clear Heqcsub02.
  unfold no_equal_5 in H3.
  destruct H3 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  assert (nor_mode f c1) as V1. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_mode f c2) as V2. 
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  assert (nor_modes f M (aenv M)) as V3.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H4 in V3.
  assert (nor_modes f x (aenv x)) as V4.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H5 in V4.
  assert (nor_modes f y (aenv y)) as V5.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite <- H6 in V5.
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
  unfold nor_mode in V2. destruct (f (c2, cp2)) eqn:eq1.
  assert ((¬ (¬ (vM <=? v2 + v1))) = (vM <=? v2 + v1)) by btauto. rewrite H3. easy. lia. lia.
  rewrite H3. clear H3. simpl.
  rewrite eupdate_index_eq. rewrite get_put_cu by easy.
  bdestruct (vM <=? v2 + v1). simpl.
  rewrite <- reg_push_update_flip by iner_p.
  rewrite <- reg_push_update_flip by iner_p.
  rewrite eupdate_twice_eq.
  rewrite eupdate_twice_neq by iner_p.
  rewrite subtractor01_sem with (tenv:= tenv) (aenv:=aenv); (try lia; try easy).
  erewrite inv_pexp_reverse.
  rewrite reg_push_update_flip with (x := M) by iner_p.
  rewrite reg_push_update_flip with (x := M) by iner_p.
  rewrite reg_push_twice_neq by iner_p.
  rewrite <- reg_push_update_flip with (x := y) by iner_p.
  rewrite <- reg_push_update_flip with (x := y) by iner_p.
  easy.
  apply comparator01_wt; try easy.
  unfold no_equal. split. lia. split. easy.
  split. easy. split. lia. split. lia. iner_p.
  apply H13. apply H12. easy. easy.
  repeat apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same_1; try easy.
  apply nor_mode_up ; try iner_p. apply nor_mode_cus_eq. easy.
  apply right_mode_exp_up_same_1. apply nor_mode_cus_eq. easy. easy.
  apply right_mode_exp_put_cus_same. easy.
  apply qft_uniform_put_cus_same.
  unfold reg_push.
  rewrite <- put_cus_update_flip; try iner_p.
  apply qft_uniform_put_cus_same.
  rewrite <- put_cus_update_flip; try iner_p.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cu_same_1; try easy.
  apply right_mode_exp_up_same_1; try easy.
  apply nor_mode_up. iner_p. easy.
  apply right_mode_exp_up_same. easy.
  apply right_mode_exp_up_same_1; try easy.
  apply nor_mode_cus_eq.
  apply nor_mode_up. iner_p. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same_1 ; try easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same_1 ; try easy.
  apply nor_mode_up. iner_p. apply nor_mode_cus_eq. easy.
  apply right_mode_exp_up_same_1; try easy.
  apply nor_mode_cus_eq. easy.
  apply right_mode_exp_put_cus_same. easy.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cu_same_1; try easy.
  apply qft_gt_put_cu_same_1; try easy.
  apply qft_gt_put_cus_same. easy. easy.
  unfold nor_modes. intros.
  apply nor_mode_up. iner_p.
  apply nor_mode_up. iner_p.
  apply nor_mode_cus_eq. apply V5. easy.
  unfold nor_modes. intros.
  nor_mode_simpl. apply V4. easy.
  rewrite comparator01_sem with (tenv := tenv) (aenv:=aenv); (try lia; try easy).
  rewrite <- reg_push_update_flip by iner_p.
  rewrite <- reg_push_update_flip by iner_p.
  rewrite reg_push_twice_neq with (x:=M) by iner_p.
  rewrite reg_push_update_flip by iner_p.
  rewrite reg_push_update_flip with (x:=y) by iner_p.
  rewrite eupdate_twice_neq by iner_p.
  clear H4 H5 H6 H7 H8 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 H9 H10 H11 H12 H13 H14 H15 H16 V1 V2 V3 V4 V5.
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
  apply right_mode_exp_put_cus_same. easy.
  apply qft_uniform_put_cus_same. easy. easy.
  apply qft_gt_put_cus_same. easy.
  unfold nor_modes. intros. nor_mode_simpl.
  apply V3. easy.
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  apply right_mode_exp_up_same_1; try easy.
  nor_mode_simpl.
  apply right_mode_exp_put_cus_same. easy.
  rewrite <- reg_push_update_flip by iner_p.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cu_same. easy.
  apply right_mode_exp_up_same; try easy.
  apply qft_gt_put_cu_same_1.
  apply qft_gt_put_cus_same. easy. easy. easy.
  rewrite eupdate_index_neq by iner_p.
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  erewrite inv_pexp_reverse.
  rewrite reg_push_update_flip with (x := M) by iner_p.
  rewrite reg_push_update_flip with (x := M) by iner_p.
  rewrite reg_push_twice_neq by iner_p.
  rewrite <- reg_push_update_flip with (x := y) by iner_p.
  rewrite <- reg_push_update_flip with (x := y) by iner_p.
  easy.
  apply comparator01_wt; try easy. unfold no_equal. split. lia.
  split. easy. split. easy. split. easy. split. easy. iner_p.
  apply H13. easy. easy. easy. 
  repeat apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same_1. nor_mode_simpl. easy.
  apply right_mode_exp_up_same_1. nor_mode_simpl. easy.
  apply right_mode_exp_put_cus_same. easy.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cus_same.
  rewrite <- reg_push_update_flip with (x := M) by iner_p.
  rewrite <- reg_push_update_flip with (x := M) by iner_p.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cu_same_1. easy. easy. easy.
  apply right_mode_exp_up_same_1. nor_mode_simpl. easy.
  apply right_mode_exp_up_same_1. nor_mode_simpl. easy. easy.
  apply right_mode_exp_up_same_1. nor_mode_simpl. easy.
  apply right_mode_exp_up_same_1. nor_mode_simpl. easy.
  apply right_mode_exp_put_cus_same. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same_1. nor_mode_simpl. easy.
  apply right_mode_exp_up_same_1. nor_mode_simpl. easy.
  apply right_mode_exp_put_cus_same. easy.
  repeat apply qft_gt_put_cus_same.
  apply qft_gt_put_cu_same_1; try easy.
  apply qft_gt_put_cu_same_1; try easy.
  apply qft_gt_put_cus_same. easy. easy.
  unfold nor_modes. intros. nor_mode_simpl. apply V5. easy.
  unfold nor_modes. intros. nor_mode_simpl. apply V4. easy.
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
  apply right_mode_exp_put_cus_same. easy.
  apply qft_uniform_put_cus_same. easy. easy.
  apply qft_gt_put_cus_same. easy. easy.
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  unfold no_equal. split. lia.
  split. easy. split. easy. split. easy. split. easy. iner_p.
  apply right_mode_exp_put_cus_same. easy.
  apply qft_uniform_put_cus_same. easy. easy.
  apply qft_gt_put_cus_same. easy. easy.
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  unfold reg_push. rewrite put_cus_neq by iner_p. easy.
  unfold nor_modes. intros. nor_mode_simpl. apply V5. lia.
  unfold nor_modes. intros. nor_mode_simpl. apply V4. lia.
  nor_mode_simpl.
  unfold reg_push. rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_neq. easy. iner_p.
Qed.

Lemma modadder21_sem :
  forall tenv aenv n x y M c1 c2 v1 v2 vM f f',
    0 < n -> v1 < vM -> v2 < vM -> vM < 2^(n-1) -> no_equal_5 x y M c1 c2 ->
    n = aenv M -> n = aenv x -> n = aenv y -> snd c1 < aenv (fst c1) -> snd c2 < aenv (fst c2) ->
    Env.MapsTo (fst c1) Nor tenv -> Env.MapsTo (fst c2) Nor tenv -> 
    Env.MapsTo M Nor tenv -> Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> 
    right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    f' = (reg_push (reg_push (reg_push 
                 ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) false]) M vM n) y v2 n) x v1 n) ->
    exp_sem aenv (modadder21 n x y M c1 c2) f'
    = (reg_push (reg_push (reg_push 
                 ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) false]) M vM n) y v2 n) x ((v1 + v2) mod vM) n).
Proof.
  intros.
  rewrite H17. rewrite modadder21_correct with (tenv := tenv); try easy.
Qed.

(* proof for doubler. *)
Lemma doubler_aux : 
   forall m n x f g, m <= n -> g n = false -> nor_modes f x (S n) ->
    get_cus (S m) (lshift' m n (put_cus f x g (S n)) x) x = cut_n (times_two_spec g) (S m).
Proof.
  induction m; intros; simpl.
  apply functional_extensionality.
  intros.
  bdestruct (x0 <? 1).
  rewrite get_cus_cua by lia.
  assert (x0 = 0) by lia.
  subst.
  rewrite eupdate_index_eq. unfold cut_n.
  bdestruct (0 <? 1).
  rewrite cus_get_eq. rewrite H0. unfold times_two_spec. bdestruct (0 =? 0). easy. lia.
  lia. easy. lia.
  unfold get_cus.
  bdestruct (x0 <? 1). lia.
  unfold cut_n. bdestruct (x0 <? 1). lia. easy.
  assert (m <= n) by lia.
  specialize (IHm n x f g H2 H0 H1).
  apply functional_extensionality.
  intros.
  bdestruct (x0 <? S (S m)).
  rewrite get_cus_cua.
  bdestruct (x0 =? S m). rewrite H4.
  rewrite eupdate_index_eq.
  rewrite cus_get_eq ; try easy.
  unfold cut_n.
  bdestruct (S m <? S (S m)).
  unfold times_two_spec.
  bdestruct (S m =? 0). lia.
  assert ((S m - 1) = m) by lia. rewrite H7. easy. lia. lia.
  rewrite eupdate_index_neq by iner_p.
  rewrite <- get_cus_cua with (n := S m).
  rewrite IHm.
  unfold cut_n.
  bdestruct (x0 <? S m). bdestruct (x0 <? S (S m)). easy.
  1-4:lia.
  unfold get_cus,cut_n.
  bdestruct (x0 <? S (S m)). lia. easy.
Qed.

Definition get_r_same f (x:var) (n:nat) := forall i j, i < n -> j < n -> get_r (f (x,i)) = get_r (f (x,j)).

Lemma lshift_get_r_same : forall n i size f x, n <= size -> i < S size -> get_r_same f x (S size) ->
         get_r (lshift' n size f x (x,i)) = get_r (f (x,i)).
Proof.
  induction n; intros;simpl.
  unfold get_r_same in H1.
  bdestruct (i =? 0). subst.
  rewrite eupdate_index_eq.
  specialize (H1 size 0).
  rewrite H1. easy. lia. lia.
  rewrite eupdate_index_neq. easy. iner_p.
  unfold get_r_same in H0.
  bdestruct (i =? S n). subst.
  rewrite eupdate_index_eq.
  specialize (H1 n (S n)).
  rewrite H1. easy. lia. lia.
  rewrite eupdate_index_neq.
  rewrite IHn. easy. lia. lia. easy. iner_p.
Qed.

Lemma doubler_correct: 
  forall n tenv aenv f x v,
    0 < n -> v < 2^(n-1) -> n = aenv x -> Env.MapsTo x Nor tenv ->
    right_mode_env aenv tenv f ->
    get_r_same f x n ->
    exp_sem aenv (doubler1 x) (reg_push f x v n) = (reg_push f x (2*v) n).
Proof.
  intros. simpl.
  unfold lshift,reg_push.
  rewrite <- H1.
  assert (nor_modes f x (aenv x)).
  apply type_nor_modes with (env := tenv); try easy.
  rewrite <- H1 in H5.
  remember (n-1) as q. assert (n = S q) by lia.
  assert (get_cus (S q) (lshift' q q (put_cus f x (nat2fb v) (S q)) x) x = cut_n (times_two_spec (nat2fb v)) (S q)).
  rewrite doubler_aux; try easy.
  rewrite Heqq in *.
  specialize (nat2fb_bound (n-1) v H0) as eq1.
  specialize (eq1 (n-1)).
  assert ((n-1) >= n - 1) by lia. apply eq1 in H7. easy.
  rewrite <- H6. easy.
  rewrite <- H6 in *. rewrite Heqq in *.
  rewrite times_two_correct in H7.
  rewrite cut_n_mod in H7.
  assert ((2 * v) < 2^n).
  rewrite H6. simpl. lia.
  rewrite Nat.mod_small in H7 by lia.
  replace (nat2fb (v + (v + 0))) with (nat2fb (2*v)) by easy.
  rewrite <- H7.
  apply functional_extensionality.
  intros.
  remember (lshift' (n - 1) (n - 1) (put_cus f x (nat2fb v) n) x) as g.
  unfold put_cus,get_cus.
  destruct x0. simpl. bdestruct (v0 =? x).
  bdestruct (n0 <? n). rewrite H9.
  unfold put_cu.
  assert (right_mode_env aenv tenv (exp_sem aenv (Lshift x) (put_cus f x (nat2fb v) n))).
  apply well_typed_right_mode_exp. constructor. easy.
  apply right_mode_exp_put_cus_same. easy.
  simpl in H11. unfold lshift in H11.
  rewrite <- H1 in H11.
  specialize (type_nor_modes (lshift' (n - 1) (n - 1)
          (put_cus f x (nat2fb v) n) x) aenv tenv x H2 H11) as eq2.
  rewrite <- Heqg in eq2. rewrite <- H1 in eq2.
  unfold nor_modes in H5,eq2.
  specialize (eq2 n0 H10).
  specialize (H5 n0 H10). unfold nor_mode in H4,eq2.
  destruct (f (x, n0)) eqn:eq1.
  assert ((@pair var nat x n0) = (@pair Env.key nat x n0)) by easy.
  rewrite H12 in *. rewrite eq1 in *.
  destruct (g (x, n0)) eqn:eq3.
  rewrite Heqg in eq3.
  assert (get_r (lshift' (n - 1) (n - 1) (put_cus f x (nat2fb v) n) x (x, n0) )
      = get_r (f (x, n0))).
  rewrite lshift_get_r_same.
  rewrite get_r_put_same. 1-2:easy. lia.
  unfold get_r_same. intros.
  unfold get_r_same in H4.
  rewrite <- H6 in *.
  specialize (H4 i j H13 H14).
  rewrite get_r_put_same.
  rewrite get_r_put_same. easy.
  rewrite eq3 in H13. rewrite eq1 in *. unfold get_r in *. subst. easy. easy. easy.
  unfold nor_mode in *.
  assert ((@pair var nat x n0) = (@pair Env.key nat x n0)) by easy.
  rewrite H12 in *.
  rewrite eq1 in *. easy.
  unfold nor_mode in *.
  assert ((@pair var nat x n0) = (@pair Env.key nat x n0)) by easy.
  rewrite H12 in *.
  rewrite eq1 in *. easy.
  subst.
  rewrite lshift'_gt by lia.
  rewrite put_cus_out by lia. easy.
  subst.
  rewrite lshift'_irrelevant by iner_p.
  rewrite put_cus_neq by iner_p. easy.
Qed.

(* The correctness statement and proof of the mod doubler.  *)
Lemma moddoubler01_correct :
  forall tenv aenv n x y c1 c2 xv M f,
    0 < n -> xv < M -> M < 2^(n-1) -> no_equal x y c1 c2 ->
    n = aenv x -> n = aenv y -> snd c1 < aenv (fst c1) -> snd c2 < aenv (fst c2) ->
    Env.MapsTo (fst c1) Nor tenv -> Env.MapsTo (fst c2) Nor tenv -> 
    Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> 
    right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    get_r_same f x n ->
    exp_sem aenv (moddoubler01 n x y c1 c2)
      (reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) false]) y M n) x xv n)
    = (reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) (M <=? 2 * xv)]) y M n) x ((2 * xv) mod M) n).
Proof.
  intros.
  unfold moddoubler01.
  unfold no_equal in H2.
  destruct H2 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite exp_sem_seq.
  rewrite exp_sem_seq.
  rewrite exp_sem_seq.
 rewrite doubler_correct with (tenv := tenv); try (easy); try lia.
 rewrite exp_sem_x.
 rewrite <- reg_push_update_flip; try (iner_p).
 rewrite <- reg_push_update_flip; try (iner_p).
 rewrite eupdate_twice_eq.
 assert (exchange
            (reg_push
               (reg_push
                  ((f [c1 |-> put_cu (f c1) false]) [c2
                   |-> put_cu (f c2) false]) y M n) x 
               (2 * xv) n c2)
        = put_cu (f c2) true).
 unfold exchange,reg_push.
 rewrite put_cus_neq_1 by iner_p.
 rewrite put_cus_neq_1 by iner_p.
 rewrite eupdate_index_eq.
 assert (nor_mode f c2).
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 unfold nor_mode,put_cu in *.
 destruct (f c2). easy. easy. easy.
 rewrite H2.
 rewrite comparator01_correct_true_1 with (tenv := tenv) (v1 := M) (v2 := 2*xv) (f' := f); try easy.
 simpl. rewrite eupdate_index_eq.
 rewrite get_put_cu.
 replace (xv + (xv + 0)) with (2 * xv) by easy.
 bdestruct ((M <=? 2 * xv)).
 rewrite <- reg_push_update_flip; try (iner_p).
 rewrite <- reg_push_update_flip; try (iner_p).
 rewrite eupdate_twice_eq.
 rewrite eupdate_twice_neq.
 rewrite subtractor01_sem with (tenv := tenv); try easy.
 replace (2 * xv + 2 ^ n - M) with (2 * xv - M + 2^n) by lia.
 rewrite reg_push_exceed.
 assert (2^n <> 0) by (apply Nat.pow_nonzero; easy).
 rewrite <- Nat.add_mod_idemp_r with (a := 2 * xv - M) by lia.
 rewrite Nat.mod_same by easy.
 rewrite plus_0_r.
 rewrite <- reg_push_exceed.
 rewrite Nat.mod_eq.
 assert (2*xv < 2 * M) by lia.
 assert (2*xv / M < 2) by (apply Nat.div_lt_upper_bound; lia).
 assert (1 <= 2*xv / M) by (apply Nat.div_le_lower_bound; lia).
 assert (2*xv / M = 1) by lia.
 rewrite H20.
 rewrite mult_1_r. easy. lia.
 assert (n = S (n-1)) by lia.
 rewrite H16. simpl. lia.
 assert (n = S (n-1)) by lia.
 rewrite H16. simpl. lia. lia.
 apply right_mode_up_nor; try easy.
 apply qft_uniform_put_cu_same; try easy.
 apply qft_gt_put_cu_same; try easy.
 destruct c1.
 rewrite eupdate_index_neq by iner_p. easy.
 destruct c1. iner_p.
 rewrite <- reg_push_update_flip; try (iner_p).
 rewrite <- reg_push_update_flip; try (iner_p).
 rewrite eupdate_twice_eq.
 rewrite Nat.mod_small by lia. easy.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 assert (n = S (n-1)) by lia.
 rewrite H15. simpl. lia.
 assert (n = S (n-1)) by lia.
 rewrite H15. simpl. lia.
 unfold no_equal. split. lia. split. easy. easy.
 unfold reg_push.
 apply right_mode_exp_put_cus_same.
 apply right_mode_exp_put_cus_same.
 apply right_mode_exp_up_same_1.
 nor_mode_simpl. destruct c1. iner_p.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 apply right_mode_exp_up_same; try easy.
 unfold reg_push.
 apply qft_uniform_put_cus_same.
 apply qft_uniform_put_cus_same.
 apply qft_uniform_put_cu_same_1; try easy.
 apply right_mode_exp_up_same_1.
 nor_mode_simpl. destruct c1. iner_p.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 apply right_mode_exp_up_same; try easy.
 apply right_mode_exp_put_cus_same.
 apply right_mode_exp_up_same_1.
 nor_mode_simpl. destruct c1. iner_p.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 apply right_mode_exp_up_same; try easy.
 apply qft_gt_put_cus_same.
 apply qft_gt_put_cus_same.
 apply qft_gt_put_cu_same_1.
 apply qft_gt_put_cu_same; try easy.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 rewrite H4.
 apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
 apply right_mode_exp_up_same_1.
 nor_mode_simpl. destruct c1. iner_p.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 apply right_mode_exp_up_same; try easy.
 rewrite H3.
 apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
 rewrite <- H3.
 apply right_mode_exp_put_cus_same.
 apply right_mode_exp_up_same_1.
 nor_mode_simpl. destruct c1. iner_p.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 apply right_mode_exp_up_same; try easy.
 unfold reg_push.
 rewrite get_cus_put_neq by lia.
 rewrite get_put_cus_cut_n.
 rewrite cut_n_mod.
 rewrite Nat.mod_small. easy.
 assert (n = S (n-1)) by lia.
 rewrite H15. simpl. lia.
 rewrite H4.
 apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
 apply right_mode_exp_up_same_1.
 nor_mode_simpl. destruct c1. iner_p.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 apply right_mode_exp_up_same; try easy.
 unfold reg_push.
 rewrite get_put_cus_cut_n.
 rewrite cut_n_mod.
 rewrite Nat.mod_small. easy.
 assert (n = S (n-1)) by lia.
 rewrite H15. simpl. lia.
 rewrite H3.
 apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
 rewrite <- H3.
 apply right_mode_exp_put_cus_same.
 apply right_mode_exp_up_same_1.
 nor_mode_simpl. destruct c1. iner_p.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 apply right_mode_exp_up_same; try easy.
 unfold reg_push.
 rewrite put_cus_neq_1 by iner_p.
 rewrite put_cus_neq_1 by iner_p.
 rewrite eupdate_index_neq.
 rewrite eupdate_index_eq.
 rewrite get_put_cu. easy.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 destruct c1. iner_p.
 unfold reg_push.
 rewrite put_cus_neq_1 by iner_p.
 rewrite put_cus_neq_1 by iner_p.
 rewrite eupdate_index_eq.
 rewrite get_put_cu; try iner_p. easy.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 unfold reg_push.
 rewrite put_cus_neq_1 by iner_p.
 rewrite put_cus_neq_1 by iner_p.
 rewrite eupdate_index_eq.
 rewrite get_r_put_cu_same. easy.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 unfold reg_push.
 apply right_mode_exp_put_cus_same.
 apply right_mode_exp_up_same_1.
 nor_mode_simpl. destruct c1. iner_p.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
 apply right_mode_exp_up_same; try easy.
 unfold get_r_same. intros.
 unfold reg_push.
 rewrite put_cus_neq_1 by iner_p.
 rewrite put_cus_neq_1 by iner_p.
 repeat rewrite eupdate_index_neq by iner_p.
 unfold get_r_same in H14.
 apply H14; try easy.
Qed.

Lemma moddoubler01_sem :
  forall tenv aenv n x y c1 c2 xv M f f',
    0 < n -> xv < M -> M < 2^(n-1) -> no_equal x y c1 c2 ->
    n = aenv x -> n = aenv y -> snd c1 < aenv (fst c1) -> snd c2 < aenv (fst c2) ->
    Env.MapsTo (fst c1) Nor tenv -> Env.MapsTo (fst c2) Nor tenv -> 
    Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> 
    right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    get_r_same f x n ->
    f' = (reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) false]) y M n) x xv n) ->
    exp_sem aenv (moddoubler01 n x y c1 c2) f'
    = (reg_push (reg_push ((f[c1 |-> put_cu (f c1) false])[c2 |-> put_cu (f c2) (M <=? 2 * xv)]) y M n) x ((2 * xv) mod M) n).
Proof.
  intros. rewrite H15. rewrite moddoubler01_correct with (tenv := tenv); try easy.
Qed.

Opaque modadder21 moddoubler01.


Lemma modsummer'_correct :
  forall i tenv aenv n x y M s c1 xv yv vM vC f,
    i < n -> 0 < n -> xv < vM -> yv < vM -> vC < vM -> vM < 2^(n-1) -> no_equal_5a x y M s c1 ->
    n = aenv M -> n = aenv x -> n = aenv y -> n = aenv s -> snd c1 < aenv (fst c1) ->
    Env.MapsTo s Nor tenv -> Env.MapsTo (fst c1) Nor tenv -> 
    Env.MapsTo M Nor tenv -> Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> 
    right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    get_r_same f x n ->
    exp_sem aenv (modsummer' i n M x y c1 s (nat2fb vC)) 
      (put_cus (reg_push (reg_push (reg_push 
                 ((f[c1 |-> put_cu (f c1) false])) M vM n) y yv n) x xv n) s allfalse n)
    = (put_cus (reg_push (reg_push (reg_push 
                 ((f[c1 |-> put_cu (f c1) false])) M vM n) 
              y (((bindecomp i vC) * xv + yv) mod vM) n) x (2^i * xv mod vM) n) s (hbf i vM xv) n).
Proof.
  intros. induction i.
  simpl.
  rewrite plus_0_r.
  rewrite Nat.mod_small by lia.
  rewrite Nat.mod_small by lia.
  assert ((hbf 0 vM xv) = allfalse).
  unfold hbf. 
  apply functional_extensionality.
  intros. bdestruct (x0 <? 0). lia. easy. rewrite H20. easy.
  simpl.
  unfold no_equal_5a in *.
  destruct H5 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  rewrite IHi; try lia.
  destruct (nat2fb vC i) eqn:eq1.
  rewrite modadder21_sem with (tenv := tenv) (v1 := ((bindecomp i vC * xv + yv) mod vM))
        (v2 := ((2 ^ i * xv) mod vM)) (vM := vM) (f := put_cus f s (hbf i vM xv) n); try easy.
  rewrite reg_push_twice_neq; try iner_p.
  rewrite reg_push_twice_neq with (y := y) ; try iner_p.
  rewrite reg_push_update_flip; try iner_p.
  rewrite reg_push_update_flip with (x := y); try iner_p.
  rewrite moddoubler01_sem with (tenv := tenv) (xv := ((2 ^ i * xv) mod vM))
          (M := vM) (f := (reg_push (put_cus f s (hbf i vM xv) n) y
             (((bindecomp i vC * xv + yv) mod vM + (2 ^ i * xv) mod vM) mod vM) n)); try easy.
  apply functional_extensionality.
  intros. destruct x0.
  unfold reg_push.
  bdestruct (v =? x). rewrite H5 in *.
  bdestruct (n0 <? n).
  rewrite put_cus_eq by easy.
  repeat rewrite put_cus_neq by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq by lia.
  rewrite put_cus_eq by easy.
  repeat rewrite put_cus_neq by lia.
  rewrite eupdate_index_neq by iner_p.
  simpl.
  rewrite plus_0_r. rewrite plus_0_r.
  rewrite <- Nat.add_mod by lia.
  rewrite  Nat.mul_add_distr_r. easy.
  rewrite put_cus_neq_2 by lia.
  repeat rewrite put_cus_neq by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq_2 by lia.
  rewrite eupdate_index_neq by iner_p. easy.
  rewrite put_cus_neq by lia.
  bdestruct (v =? M). rewrite H20 in *.
  bdestruct (n0 <? n).
  rewrite put_cus_eq by easy.
  repeat rewrite put_cus_neq by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq by lia.
  rewrite put_cus_eq by easy.
  rewrite eupdate_index_neq by iner_p. easy.
  rewrite put_cus_neq_2 by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq_2 by lia.
  rewrite eupdate_index_neq by iner_p. easy.
  rewrite put_cus_neq by lia.
  bdestruct (v =? s). rewrite H21 in *.
  bdestruct (n0 =? i). rewrite H22 in *.
  rewrite eupdate_index_eq.
  rewrite put_cus_neq by lia.
  rewrite put_cus_eq by lia.
  rewrite put_cu_twice_eq.
  rewrite put_cus_eq by lia.
  repeat rewrite put_cus_neq by lia.
  rewrite eupdate_index_neq by iner_p.
  unfold hbf.
  bdestruct (i <? S i). easy. lia.
  repeat rewrite eupdate_index_neq by iner_p.
  bdestruct (n0 <? n).
  rewrite put_cus_neq by lia.
  repeat rewrite put_cus_eq by lia.
  repeat rewrite put_cus_neq by lia.
  rewrite eupdate_index_neq by iner_p.
  unfold hbf.
  bdestruct (n0 <? i). bdestruct (n0 <? S i). easy. lia.
  bdestruct (n0 <? S i). lia. easy.
  repeat rewrite put_cus_neq_2 by lia.
  rewrite eupdate_index_neq by iner_p. easy.
  repeat rewrite put_cus_neq by lia.
  bdestruct (c1 ==? (v,n0)). rewrite H22 in *.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_eq.
  repeat rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_eq. easy.
  repeat rewrite eupdate_index_neq by iner_p.
  bdestruct (v =? y).
  bdestruct (n0 <? n). rewrite H23 in *.
  rewrite put_cus_eq.
  repeat rewrite put_cus_neq by iner_p.
  rewrite put_cus_eq.
  repeat rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_neq by iner_p.
  rewrite bindecomp_seq. rewrite eq1. simpl.
  rewrite plus_0_r.
  rewrite <- Nat.add_mod by lia.
  replace ((bindecomp i vC * xv + yv + 2 ^ i * xv)) with (((bindecomp i vC + 2 ^ i) * xv + yv)) by lia.
  easy. easy. easy. 
  repeat rewrite put_cus_neq_2 by lia.
  rewrite eupdate_index_neq by iner_p. easy.
  repeat rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_neq by iner_p. easy.
  apply Nat.mod_upper_bound. lia.
  unfold no_equal. split. easy. split. easy. split. iner_p. split. iner_p. split; iner_p.
  simpl. lia.
  unfold reg_push.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same. easy.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cus_same. easy. easy.
  apply right_mode_exp_put_cus_same. easy.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cus_same. easy.
  rewrite H9.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite H8.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  apply right_mode_exp_put_cus_same. easy.
  unfold get_r_same,reg_push. intros.
  repeat rewrite get_r_put_same. apply H19; try easy.
  unfold reg_push.
  apply functional_extensionality.
  intros. destruct x0.
  bdestruct (v =? x). rewrite H5 in *.
  bdestruct (n0 <? n).
  repeat rewrite put_cus_eq by lia.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p. easy.
  rewrite put_cus_neq_2 by lia.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq_2 by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq_2 by lia. easy.
  rewrite put_cus_neq by iner_p.
  bdestruct (v =? M). rewrite H20 in *.
  bdestruct (n0 <? n).
  rewrite put_cus_eq by easy.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq by iner_p.
  rewrite put_cus_eq by easy.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq by iner_p. easy.
  repeat rewrite put_cus_neq_2 by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq_2 by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq_2 by lia. easy.
  rewrite put_cus_neq by iner_p.
  bdestruct (v =? s). rewrite H21 in *.
  bdestruct (n0 =? i). rewrite H22 in *.
  rewrite eupdate_index_eq.
  rewrite put_cus_eq by lia.
  rewrite put_cu_twice_eq.
  repeat rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_eq.
  rewrite put_cus_eq by lia.
  rewrite put_cu_twice_eq. easy.
  bdestruct (n0 <? n).
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite put_cus_neq by iner_p.
  rewrite put_cus_eq by lia.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite put_cus_neq by iner_p.
  rewrite put_cus_eq by lia. easy.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq_2 by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq_2 by lia. easy.
  rewrite eupdate_index_neq by iner_p.
  bdestruct (c1 ==? (v,n0)). rewrite H22 in *.
  rewrite eupdate_index_eq.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_eq. easy.
  repeat rewrite eupdate_index_neq by iner_p.
  bdestruct (v =? y). rewrite H23 in *.
  bdestruct (n0 <? n).
  rewrite put_cus_eq by easy.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite put_cus_eq by easy.
  rewrite put_cus_neq by iner_p. easy.
  repeat rewrite put_cus_neq_2 by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq_2 by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  easy.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq by iner_p. easy.
  apply Nat.mod_upper_bound. lia.
  apply Nat.mod_upper_bound. lia.
  unfold no_equal_5. split. lia. split. easy. split. iner_p. split. iner_p.
  split. easy. split. easy. split. iner_p. split. easy. split. iner_p. iner_p.
  simpl. lia.
  unfold reg_push.
  apply right_mode_exp_put_cus_same. easy.
  apply qft_uniform_put_cus_same. easy. easy.
  apply qft_gt_put_cus_same. easy.
  rewrite H9.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  unfold reg_push.
  apply functional_extensionality.
  intros. destruct x0.
  bdestruct (v =? s). rewrite H5 in *.
  bdestruct (n0 =? i). rewrite H20 in *.
  rewrite put_cus_eq by lia.
  repeat rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by iner_p.
  rewrite put_cus_eq by lia.
  rewrite put_cu_twice_eq.
  unfold hbf. bdestruct (i <? i). lia. easy.
  bdestruct (n0 <? n).
  rewrite put_cus_eq by easy.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite put_cus_eq by lia. easy.
  repeat rewrite put_cus_neq_2 by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq_2 by lia. easy.
  rewrite put_cus_neq by iner_p.
  bdestruct (v =? x). rewrite H20 in *.
  bdestruct (n0 <? n).
  repeat rewrite put_cus_eq by lia.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p. 
  rewrite put_cus_eq by lia.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p. 
  repeat rewrite put_cus_neq by iner_p.
  easy.
  repeat rewrite put_cus_neq_2 by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite put_cus_neq_2 by lia. easy.
  rewrite put_cus_neq by iner_p.
  bdestruct (v =? y). rewrite H21 in *.
  bdestruct (n0 <? n).
  rewrite put_cus_eq by easy.
  repeat rewrite put_cus_neq by iner_p.
  rewrite put_cus_eq by easy.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite put_cus_neq by iner_p.
  easy.
  repeat rewrite put_cus_neq_2 by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq_2 by lia. easy.
  rewrite put_cus_neq by iner_p.
  bdestruct (v =? M). rewrite H22 in *.
  bdestruct (n0 <? n).
  rewrite put_cus_eq by easy.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq by iner_p.
  rewrite put_cus_eq by easy.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq by iner_p. easy.
  repeat rewrite put_cus_neq_2 by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq_2 by lia. easy.
  rewrite put_cus_neq by iner_p.
  bdestruct (c1 ==? (v,n0)). rewrite H23 in *.
  rewrite eupdate_index_eq.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_eq. easy.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite put_cus_neq by iner_p. easy.
  simpl.
  rewrite moddoubler01_sem with (tenv := tenv) (xv := ((2 ^ i * xv) mod vM))
          (M := vM) (f := (reg_push (put_cus f s (hbf i vM xv) n) y
             ((bindecomp i vC * xv + yv) mod vM) n)); try easy.
  apply functional_extensionality.
  intros. destruct x0.
  unfold reg_push.
  bdestruct (v =? x). rewrite H5 in *.
  bdestruct (n0 <? n).
  rewrite put_cus_eq by easy.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq by iner_p.
  rewrite put_cus_eq by easy.
  repeat rewrite put_cus_neq by lia.
  rewrite eupdate_index_neq by iner_p.
  simpl.
  rewrite plus_0_r. rewrite plus_0_r.
  rewrite <- Nat.add_mod by lia.
  rewrite  Nat.mul_add_distr_r. easy.
  repeat rewrite put_cus_neq_2 by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq_2 by lia.
  rewrite eupdate_index_neq by iner_p. easy.
  rewrite put_cus_neq by lia.
  bdestruct (v =? M). rewrite H20 in *.
  bdestruct (n0 <? n).
  rewrite put_cus_eq by easy.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq by iner_p.
  rewrite put_cus_eq by easy.
  rewrite eupdate_index_neq by iner_p. easy.
  repeat rewrite put_cus_neq_2 by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq_2 by lia.
  rewrite eupdate_index_neq by iner_p. easy.
  rewrite put_cus_neq by lia.
  bdestruct (v =? s). rewrite H21 in *.
  bdestruct (n0 =? i). rewrite H22 in *.
  rewrite eupdate_index_eq.
  repeat rewrite put_cus_neq by iner_p.
  rewrite put_cus_eq by lia.
  rewrite put_cu_twice_eq.
  rewrite put_cus_eq by lia.
  repeat rewrite put_cus_neq by lia.
  rewrite eupdate_index_neq by iner_p.
  unfold hbf.
  bdestruct (i <? S i). easy. lia.
  repeat rewrite eupdate_index_neq by iner_p.
  bdestruct (n0 <? n).
  rewrite put_cus_neq by lia.
  repeat rewrite put_cus_eq by lia.
  repeat rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_neq by iner_p.
  unfold hbf.
  bdestruct (n0 <? i). bdestruct (n0 <? S i). easy. lia.
  bdestruct (n0 <? S i). lia. easy.
  repeat rewrite put_cus_neq_2 by lia.
  rewrite eupdate_index_neq by iner_p. easy.
  repeat rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq by iner_p.
  bdestruct (c1 ==? (v,n0)). rewrite H22 in *.
  rewrite eupdate_index_eq.
  repeat rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_eq. easy.
  repeat rewrite eupdate_index_neq by iner_p.
  bdestruct (v =? y).
  bdestruct (n0 <? n). rewrite H23 in *.
  rewrite put_cus_eq.
  repeat rewrite put_cus_neq by iner_p.
  rewrite put_cus_eq.
  repeat rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_neq by iner_p.
  rewrite bindecomp_seq. rewrite eq1. simpl.
  rewrite plus_0_r. easy.
  easy. easy. 
  repeat rewrite put_cus_neq_2 by lia.
  rewrite eupdate_index_neq by iner_p. easy.
  repeat rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_neq by iner_p. easy.
  apply Nat.mod_upper_bound. lia.
  unfold no_equal. split. easy. split. easy. split. iner_p. split. iner_p. split; iner_p.
  simpl. lia.
  unfold reg_push.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same. easy.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cus_same. easy. easy.
  apply right_mode_exp_put_cus_same. easy.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cus_same. easy.
  rewrite H9.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  rewrite H8.
  apply type_nor_modes with (aenv := aenv) (env := tenv); try easy.
  apply right_mode_exp_put_cus_same. easy.
  unfold get_r_same. intros.
  unfold reg_push.
  repeat rewrite get_r_put_same. apply H19; try easy.
  apply functional_extensionality.
  intros. destruct x0.
  unfold reg_push.
  bdestruct (v =? s). rewrite H5 in *.
  bdestruct (n0 =? i). rewrite H20 in *.
  rewrite put_cus_eq by lia.
  repeat rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by iner_p.
  rewrite put_cus_eq by lia.
  rewrite put_cu_twice_eq.
  unfold hbf. bdestruct (i <? i). lia. easy.
  bdestruct (n0 <? n).
  rewrite put_cus_eq by easy.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq by iner_p.
  rewrite put_cus_eq by lia. easy.
  repeat rewrite put_cus_neq_2 by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq_2 by lia. easy.
  rewrite put_cus_neq by iner_p.
  bdestruct (v =? x). rewrite H20 in *.
  bdestruct (n0 <? n).
  repeat rewrite put_cus_eq by lia.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p. 
  repeat rewrite put_cus_neq by iner_p. easy.
  repeat rewrite put_cus_neq_2 by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq_2 by lia.
  easy.
  rewrite put_cus_neq by iner_p.
  bdestruct (v =? y). rewrite H21 in *.
  bdestruct (n0 <? n).
  rewrite put_cus_eq by easy.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite put_cus_eq by easy.
  repeat rewrite put_cus_neq by iner_p. easy.
  repeat rewrite put_cus_neq_2 by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq_2 by lia. easy.
  rewrite put_cus_neq by iner_p.
  bdestruct (v =? M). rewrite H22 in *.
  bdestruct (n0 <? n).
  rewrite put_cus_eq by easy.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq by iner_p.
  rewrite put_cus_eq by easy.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq by iner_p. easy.
  repeat rewrite put_cus_neq_2 by lia.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq_2 by lia. easy.
  rewrite put_cus_neq by iner_p.
  bdestruct (c1 ==? (v,n0)). rewrite H23 in *.
  rewrite eupdate_index_eq.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_eq. easy.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq by iner_p.
  repeat rewrite eupdate_index_neq by iner_p.
  repeat rewrite put_cus_neq by iner_p. easy.
Qed.


(* This is the correctness statement and proof of the C*x%M sum implementation. *)
Lemma modsummer_correct :
  forall tenv aenv n x y M s c1 xv yv vM vC f,
    0 < n -> xv < vM -> yv < vM -> vC < vM -> vM < 2^(n-1) -> no_equal_5a x y M s c1 ->
    n = aenv M -> n = aenv x -> n = aenv y -> n = aenv s -> snd c1 < aenv (fst c1) ->
    Env.MapsTo s Nor tenv -> Env.MapsTo (fst c1) Nor tenv -> 
    Env.MapsTo M Nor tenv -> Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> 
    right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    get_r_same f x n ->
    exp_sem aenv (modsummer n M x y c1 s vC) 
      (put_cus (reg_push (reg_push (reg_push 
                 ((f[c1 |-> put_cu (f c1) false])) M vM n) y yv n) x xv n) s allfalse n)
    = (put_cus (reg_push (reg_push (reg_push 
                 ((f[c1 |-> put_cu (f c1) false])) M vM n) 
              y ((vC * xv + yv) mod vM) n) x (2^(n-1) * xv mod vM) n) s (hbf (n-1) vM xv) n).
Proof.
  intros. unfold modsummer.
  rewrite modsummer'_correct with (tenv := tenv) ; try easy.
  rewrite bindecomp_spec.
  rewrite Nat.mod_small with (a := vC) by lia. easy. lia.
Qed.

Opaque modsummer.

Lemma modmult_half_correct :
  forall tenv aenv n x y M s c1 xv yv vM vC f,
    0 < n -> xv < vM -> yv < vM -> vC < vM -> vM < 2^(n-1) -> no_equal_5a x y M s c1 ->
    n = aenv M -> n = aenv x -> n = aenv y -> n = aenv s -> snd c1 < aenv (fst c1) ->
    Env.MapsTo s Nor tenv -> Env.MapsTo (fst c1) Nor tenv -> 
    Env.MapsTo M Nor tenv -> Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> 
    right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    get_r_same f x n ->
    exp_sem aenv (modmult_half n M x y c1 s vC) 
      (put_cus (reg_push (reg_push (reg_push 
                 ((f[c1 |-> put_cu (f c1) false])) M vM n) y yv n) x xv n) s allfalse n)
    = (put_cus (reg_push (reg_push (reg_push 
                 ((f[c1 |-> put_cu (f c1) false])) M vM n) 
              y ((vC * xv + yv) mod vM) n) x xv n) s allfalse n).
Proof.
  intros. unfold modmult_half. simpl.
  rewrite modsummer_correct with (tenv := tenv); try easy.
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv); try easy.
  apply modsummer_wt; try easy.
  unfold reg_push.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cu_same. easy.
  apply right_mode_exp_up_same. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cu_same. easy.
  unfold nor_modes. intros.
  unfold nor_mode.
  destruct H4 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  rewrite eupdate_index_neq by iner_p. 
  assert (nor_mode f (M,i)).
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  simpl. lia.
  apply H4.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq.
  destruct H4 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  apply nor_mode_up. iner_p.
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  simpl. lia.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  destruct H4 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  apply nor_mode_up. iner_p.
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  simpl. lia.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  destruct H4 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  apply nor_mode_up. iner_p.
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  simpl. lia.
  rewrite modsummer_correct with (tenv := tenv); try easy.
  rewrite mult_0_l.
  rewrite plus_0_l.
  rewrite Nat.mod_mod by lia. easy.
  apply Nat.mod_upper_bound. lia. lia.
Qed.

Opaque modmult_half.

Lemma modmult_full_correct :
  forall tenv aenv n x y M s c1 xv vM vC Cinv f,
    0 < n -> xv < vM -> vC < vM -> Cinv < vM -> vM < 2^(n-1) -> vC * Cinv mod vM = 1 ->
    no_equal_5a x y M s c1 -> n = aenv M -> n = aenv x -> n = aenv y -> n = aenv s -> snd c1 < aenv (fst c1) ->
    Env.MapsTo s Nor tenv -> Env.MapsTo (fst c1) Nor tenv -> 
    Env.MapsTo M Nor tenv -> Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> 
    right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    get_r_same f x n ->
    get_r_same f y n ->
    exp_sem aenv (modmult_full vC Cinv n M x y c1 s) 
      (put_cus (reg_push (put_cus (reg_push 
                 ((f[c1 |-> put_cu (f c1) false])) M vM n) y allfalse n) x xv n) s allfalse n)
    = (put_cus (put_cus (reg_push (reg_push 
                 ((f[c1 |-> put_cu (f c1) false])) M vM n) 
              y ((vC * xv) mod vM) n) x allfalse n) s allfalse n).
Proof.
  intros. unfold modmult_full. simpl.
  assert ((put_cus
              (reg_push (f [c1 |-> put_cu (f c1) false])
                 M vM n) y allfalse n)
     = (reg_push
              (reg_push (f [c1 |-> put_cu (f c1) false])
                 M vM n) y 0 n)).
  unfold reg_push.
  rewrite <- allfalse_0 with (n := n).
  assert ((cut_n allfalse n)  = allfalse).
  unfold cut_n.
  apply functional_extensionality.
  intros. bdestruct (x0 <? n). easy. easy.
  rewrite H21. easy. rewrite H21.
  rewrite modmult_half_correct with (tenv := tenv); try easy.
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv); try easy.
  apply modmult_half_wt; try easy.
  destruct H5 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  unfold no_equal_5a. repeat split; iner_p.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cu_same. easy.
  apply right_mode_exp_up_same. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cu_same. easy.
  unfold nor_modes. intros.
  destruct H5 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  apply nor_mode_up. iner_p.
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  simpl. lia.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq.
  destruct H5 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  apply nor_mode_up. iner_p.
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  simpl. lia.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  destruct H5 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  apply nor_mode_up. iner_p.
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  simpl. lia.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  destruct H5 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  apply nor_mode_up. iner_p.
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  simpl. lia.
  assert ((put_cus
        (reg_push
           (reg_push (f [c1 |-> put_cu (f c1) false]) M
              vM n) y ((vC * xv) mod vM) n) x allfalse n)
    = (reg_push
        (reg_push
           (reg_push (f [c1 |-> put_cu (f c1) false]) M
              vM n) y ((vC * xv) mod vM) n) x 0 n)).
  unfold reg_push.
  rewrite <- allfalse_0 with (n := n).
  assert ((cut_n allfalse n)  = allfalse).
  unfold cut_n.
  apply functional_extensionality.
  intros. bdestruct (x0 <? n). easy. easy.
  rewrite H22. easy. rewrite H22.
  destruct H5 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  rewrite reg_push_twice_neq with (x := y) (y := x) by iner_p.
  rewrite modmult_half_correct with (tenv := tenv); try easy.
  rewrite reg_push_twice_neq with (x := x) (y := y) by iner_p.
  rewrite plus_0_r.
  rewrite plus_0_r.
  rewrite Nat.mul_mod_idemp_r by lia.
  rewrite Nat.mul_assoc.
  rewrite (Nat.mul_mod (Cinv * vC)) by lia.
  rewrite (Nat.mul_comm Cinv).
  rewrite H4.
  rewrite Nat.mul_1_l.
  rewrite Nat.mod_mod by lia.
  rewrite (Nat.mod_small xv) by lia. easy.
  apply Nat.mod_upper_bound; lia. lia.
  unfold no_equal_5a. repeat split; iner_p. lia.
Qed.

Opaque modmult_full.

Lemma modmult_correct :
  forall tenv aenv n x y M s c1 xv vM vC Cinv f,
    0 < n -> xv < vM -> vC < vM -> Cinv < vM -> vM < 2^(n-1) -> vC * Cinv mod vM = 1 ->
    no_equal_5a x y M s c1 -> n = aenv M -> n = aenv x -> n = aenv y -> n = aenv s -> snd c1 < aenv (fst c1) ->
    Env.MapsTo s Nor tenv -> Env.MapsTo (fst c1) Nor tenv -> 
    Env.MapsTo M Nor tenv -> Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv -> 
    right_mode_env aenv tenv f -> qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    get_r_same f x n ->
    get_r_same f y n ->
    exp_sem aenv (modmult (nat2fb vM) vC Cinv n x y M s c1) 
      (put_cus (reg_push (put_cus (put_cus 
                 ((f[c1 |-> put_cu (f c1) false])) M allfalse n) y allfalse n) x xv n) s allfalse n)
    = (put_cus (put_cus (reg_push (put_cus 
                 ((f[c1 |-> put_cu (f c1) false])) M allfalse n) 
              y ((vC * xv) mod vM) n) x allfalse n) s allfalse n).
Proof.
  intros. unfold modmult. simpl.
  rewrite init_v_sem with (size := n) (tenv := tenv); try easy.
  destruct H5 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  rewrite put_cus_twice_neq by iner_p.
  unfold reg_push.
  rewrite put_cus_twice_neq with (x := x) (y := M) by iner_p.
  rewrite put_cus_twice_neq with (x := y) (y := M) by iner_p.
  rewrite put_cus_twice_eq.
  rewrite cut_n_mod.
  rewrite Nat.mod_small.
  replace ((put_cus
        (put_cus
           (put_cus
              (put_cus (f [c1 |-> put_cu (f c1) false]) M
                 (nat2fb vM) n) y allfalse n) x
           (nat2fb xv) n) s allfalse n))
    with (put_cus
          (reg_push (put_cus
              (reg_push (f [c1 |-> put_cu (f c1) false]) M vM n)
                    y allfalse n) x xv n) s allfalse n) by easy.
  rewrite modmult_full_correct with (tenv := tenv); try easy.
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv); try easy.
  apply well_typed_init_v; try easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cus_same.
  apply qft_uniform_put_cu_same. easy.
  apply right_mode_exp_up_same. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cus_same.
  apply qft_gt_put_cu_same. easy.
  unfold nor_modes. intros.
  apply nor_mode_up. iner_p.
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  simpl. lia.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq.
  apply nor_mode_up. iner_p.
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  simpl. lia.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  apply nor_mode_up. iner_p.
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  simpl. lia.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  apply nor_mode_cus_eq.
  apply nor_mode_up. iner_p.
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  simpl. lia.
  rewrite init_v_sem with (size := n) (tenv := tenv); try easy.
  unfold reg_push.
  rewrite put_cus_twice_neq with (x := s) (y := M) by iner_p.
  rewrite put_cus_twice_neq with (x := x) (y := M) by iner_p.
  rewrite put_cus_twice_neq with (x := y) (y := M) by iner_p.
  rewrite put_cus_twice_eq.
  rewrite cut_n_mod.
  rewrite Nat.mod_small.
  easy.
  assert (n = S (n - 1)) by lia.
  rewrite H5. simpl. lia.
  repeat rewrite get_cus_put_neq by iner_p.
  assert (allfalse = nat2fb 0).
  unfold nat2fb. simpl. easy.
  rewrite H5.
  rewrite get_cus_put_eq. easy.
  assert (n = S (n - 1)) by lia.
  rewrite H21. simpl. lia.
  unfold nor_modes. intros.
  apply nor_mode_up. iner_p.
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  simpl. lia.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy.
  assert (n = S (n - 1)) by lia.
  rewrite H5. simpl. lia.
  destruct H5 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 X10]]]]]]]]].
  unfold reg_push.
  repeat rewrite get_cus_put_neq by iner_p.
  assert (allfalse = nat2fb 0).
  unfold nat2fb. simpl. easy.
  rewrite H5.
  rewrite get_cus_put_eq. easy.
  assert (n = S (n - 1)) by lia.
  rewrite H21. simpl. lia.
  unfold nor_modes. intros.
  apply nor_mode_up. iner_p.
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  simpl. lia.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_put_cus_same.
  apply right_mode_exp_up_same. easy.
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
   (cl_nat_mult' size size x re c M).

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
Definition one_cu_cl_full_adder_i (c2:posi) (x:var) (re:var) (c1:posi) (n:nat) (i:nat) := 
  CU c2 (adder_i n x re c1 i).

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
   (cl_full_mult' size size x y re c).

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
            ( (clf_full_mult_quar size x y re ex c; inv_exp (clean_high_flt size size y ex))).


(* compare x <=? y 
Definition comparator02 n x y c1 c2 := (negator0 n x); highb01 n x y c1 c2; inv_exp (negator0 n x).
*)

(* x % M circuit. *)
Fixpoint cl_moder' i (n:nat) (x y ex:var) c1 (M:nat -> bool) := 
     match i with 0 => SKIP (x,0)
           | S j => init_v n y M ; X (ex,j) ; comparator01 n y x c1 (ex,j) ; 
                       CU (ex,j) (subtractor01 n y x c1); init_v n y M ; 
                       cl_moder' j n x y ex c1 (cut_n (div_two_spec M) n)
     end.
Definition cl_moder (n:nat) (x re y ex:var) c1 (M:nat) := 
    let i := findnum M n in 
         cl_moder' (S i) n x y ex c1 (nat2fb (2^i*M)) ; copyto x re n; inv_exp (cl_moder' (S i) n x y ex c1 (nat2fb (2^i*M))).

Definition vars_for_cl_moder' (size:nat) := 
  gen_vars size (x_var::(y_var::(z_var::(s_var::[])))).

Definition vars_for_cl_moder (size:nat) :=
  fun x => if x =? c_var then (size * 4,1,id_nat,id_nat) 
        else vars_for_cl_moder' size x.

Definition cl_moder_out (size:nat)  := 
   cl_moder size x_var y_var z_var s_var (c_var,0).

(* x / M circuit. *)
Definition cl_div (n:nat) (x re y ex:var) c1 (M:nat) := 
    let i := findnum M n in 
         cl_moder' (S i) n x y ex c1 (nat2fb (2^i*M)) ; copyto ex re n; inv_exp (cl_moder' (S i) n x y ex c1 (nat2fb (2^i*M))).

Definition vars_for_cl_div' (size:nat) := 
  gen_vars size (x_var::(y_var::(z_var::(s_var::[])))).

Definition vars_for_cl_div (size:nat) :=
  fun x => if x =? c_var then (size * 4,1,id_nat,id_nat) 
        else vars_for_cl_div' size x.

Definition cl_div_out (size:nat) := 
   cl_div size x_var y_var z_var s_var (c_var,0).


(* x = (x % M, x / M) mod value is in x, and ex stores div results. *)
Definition cl_div_mod (n:nat) (x y ex:var) c1 (M:nat) :=
   let i := findnum M n in cl_moder' (S i) n x y ex c1 (nat2fb (2^i*M)).

Definition vars_for_cl_div_mod' (size:nat) := 
  gen_vars size (x_var::(y_var::(z_var::([])))).

Definition vars_for_cl_div_mod (size:nat) :=
  fun x => if x =? s_var then (size * 3,1,id_nat,id_nat) 
        else vars_for_cl_div_mod' size x.

Definition cl_div_mod_out (size:nat) := 
   cl_div_mod size x_var y_var z_var (s_var,0).









