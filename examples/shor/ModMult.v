Require Import QuantumLib.VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat.
Require Export RCIR.

Local Open Scope bccom_scope.
Local Open Scope nat_scope.

(* 
  This file contains an implementation and proof of correctness for the modular
  multiplier circuit used in Shor's algorithm.
  
  The modular multiplier circuit computes ((C * x) % M) where C and M are integer
  constants and x is an integer variable.

  The main definition in this file is (modmult_rev M C Cinv n). M and C are the 
  constants in the spec above, Cinv is C's inverse modulo M, and n is the number 
  of bits in M.

  The final correctness property proved is:

  Lemma modmult_rev_correct : forall n x M C Cinv,
    1 < M < 2^n ->
    x < M -> C < M -> Cinv < M ->
    C * Cinv mod M = 1 ->
    bcexec (modmult_rev M C Cinv n) (fb_push_n n (fbrev n (nat2fb x)) allfalse) = 
      (fb_push_n n (fbrev n (nat2fb (C * x mod M))) allfalse).

  i.e. evaluating the output circuit on input [rev x][00...0] produces 
  [rev ((C * x) % M)][00...0] where (rev X) outputs the binary form of integer
  X in reverse. 
*)


(* Some preliminaries defining (nat -> bool) <-> Pos conversion.
   
   TODO: this file should reuse the nat_to_funbool function in SQIR/VectorStates.v
   instead of defining nat2fb. *)

(* push bool b to position 0 of f; shift all other values right *)
Definition fb_push b f : nat -> bool :=
  fun x => match x with
        | O => b
        | S n => f n
        end.

(* n repetitions of fb_push. *)
Definition fb_push_n n f g : nat -> bool :=
  fun i => if (i <? n) then f i else g (i - n).

Definition allfalse := fun (_ : nat) => false.

(* compile a positive to a bool function. *)
Fixpoint pos2fb p : nat -> bool :=
  match p with
  | xH => fb_push true allfalse
  | xI p' => fb_push true (pos2fb p')
  | xO p' => fb_push false (pos2fb p')
  end.

(* compile a nat to a bool function. *)
Definition N2fb n : nat -> bool :=
  match n with
  | 0%N => allfalse
  | Npos p => pos2fb p
  end.

Definition nat2fb n := N2fb (N.of_nat n).

(*********** Definitions ***********)

(* This is the number of ancilla qubits ("scratch space") needed for the
   modmult_rev circuit. n is the number of bits in the modulus M. *)
Definition modmult_rev_anc n := 3 * n + 11.

(* MAJ takes the old carry value ci, bits ai and bi, and returns ci ⊕ ai, bi ⊕ ai, 
   and a new carry value, which is defined as (ai && bi) ⊕ (bi && ci) ⊕ (ai && ci). *)
Definition MAJ a b c := bccnot c b ; bccnot c a ; bcccnot a b c.
   
(* UMA takes the result of MAJ, and produces three ci, si, and ai where si 
   represents the i-th bit of a + b *)
Definition UMA a b c := bcccnot a b c ; bccnot c a ; bccnot a b.

(* The following defines n-bit MAJ and UMA circuits. 
   MAJ;UMA transforms [x][y] to [x][(x+y) % 2^n] *)
Fixpoint MAJseq' i n c0 : bccom :=
  match i with
  | 0 => MAJ c0 (2 + n) 2
  | S i' => MAJseq' i' n c0; MAJ (2 + i') (2 + n + i) (2 + i)
  end.
Definition MAJseq n := MAJseq' (n - 1) n 0.

Fixpoint UMAseq' i n c0 : bccom :=
  match i with
  | 0 => UMA c0 (2 + n) 2
  | S i' => UMA (2 + i') (2 + n + i) (2 + i); UMAseq' i' n c0
  end.
Definition UMAseq n := UMAseq' (n - 1) n 0.

Definition adder01 n : bccom := MAJseq n; UMAseq n.

(* swapper02 swaps [x][y][z] to be [z][y][x]. *)
Fixpoint swapper02' i n :=
  match i with
  | 0 => bcskip
  | S i' => swapper02' i' n; bcswap (2 + i') (2 + n + n + i')
  end.
Definition swapper02 n := swapper02' n n.

(* The following will negate the first input value in the state 00[x][y][z],
   producing 00[-x][y][z]. *)
Fixpoint negator0' i : bccom :=
  match i with
  | 0 => bcskip
  | S i' => negator0' i'; bcx (2 + i')
  end.
Definition negator0 n := negator0' n.

(* To determine if x < y, we need to compute x - y and check the high bit of the
   result. If the high_bit is zero, then means that x >= y; otherwise x < y. *)
Definition highb01 n : bccom := MAJseq n; bccnot (1 + n) 1; bcinv (MAJseq n).

(* Implementation of a comparator, using highb01. The high bit stores the boolean
   result of x - y < 0.  *)
Definition comparator01 n :=
  (bcx 0; negator0 n); highb01 n; bcinv (bcx 0; negator0 n).

(* Implementation of a subtractor. On input [x][y], it produces [x][y + 2^n - x]. *)
Definition subtractor01 n := 
  (bcx 0; negator0 n); adder01 n; bcinv (bcx 0; negator0 n).

(* The implementation of a modulo adder. On input [M][x][y], it produces 
   [M][x+y % M][y]. The modulo operation is not reversible - it will flip the 
   high-bit to be the comparator factor. To return the high-bit to zero, we use 
   the inverse circuit of the comparator. *)
Definition modadder21 n := 
  swapper02 n; adder01 n; swapper02 n; 
  comparator01 n; (bygatectrl 1 (subtractor01 n); bcx 1); 
  swapper02 n; bcinv (comparator01 n); swapper02 n.

(* swapper12 swaps [x][y][z] to be [x][z][y]. *)
Fixpoint swapper12' i n :=
  match i with
  | 0 => bcskip
  | S i' => swapper12' i' n; bcswap (2 + n + i') (2 + n + n + i')
  end.
Definition swapper12 n := swapper12' n n.

(* Here we implement a doubler circuit based on the binary shift operation. *)
Fixpoint doubler1' i n :=
  match i with
  | 0 => bcskip
  | S i' => bcswap (n + i') (n + i); doubler1' i' n
  end.
Definition doubler1 n := doubler1' (n - 1) (2 + n).

(* Another version of the mod adder only for computing [x][M] -> [2*x % M][M]. *)
Definition moddoubler01 n := doubler1 n; comparator01 n; bygatectrl 1 (subtractor01 n).

(* Alternate version of the modulo adder to do addition [y][x] -> [y][x+y mod M]. *)
Definition modadder12 n := swapper12 n; modadder21 n; swapper12 n.

(* The following implements a modulo adder for all bit positions in C.
   For every bit in C, it:
   1. doubles the factor (originally 2^(i-1)* x %M, now 2^i * x %M)
   2. adds the result to the sum of C*x%M based on whether the ith bit of C is zero *)
Fixpoint modsummer' i n (fC : nat -> bool) :=
  match i with
  | 0 => if (fC 0) then modadder12 n else bcskip
  | S i' => modsummer' i' n fC; moddoubler01 n; 
          bcswap 1 (2 + n + n + n + i);
        (if (fC i) then modadder12 n else bcskip)
  end.
Definition modsummer n C := modsummer' (n - 1) n (nat2fb C).

(* modsummer + cleanup of high bits *)
Definition modmult_half n C := modsummer n C; (bcinv (modsummer n 0)).

(* On input [M][x][00..0], modmult_full produces [M][C*x mod M][00..0]. The 
   strategy is to run modmult_half on C (producing [M][x][C*x mod M]), then swap 
   the values of x and C*x%M (producing [M][C*x mod M][x]), and finally run 
   the inverse of modmult_half using C's inverse (producing [M][C*x mod M][00..0]). *)
Definition modmult_full C Cinv n := 
  modmult_half n C; swapper12 n; bcinv (modmult_half n Cinv).

(* The following performs clean-up of the final state. It prepares the two high-bits
   (two zero bits) and empty positions for storing M. It then inserts the value
   M using genM0. *)
Fixpoint swapperh1' j n :=
  match j with
  | 0 => bcskip
  | S j' => swapperh1' j' n; bcswap j' (2 + n + j')
  end.
Definition swapperh1 n := swapperh1' n n.

Fixpoint genM0' i (f : nat -> bool) : bccom :=
  match i with
  | 0 => bcskip
  | S i' => genM0' i' f; if (f i') then bcx (2 + i') else bcskip
  end.
Definition genM0 M n := genM0' n (nat2fb M).

Definition modmult M C Cinv n := 
  swapperh1 n; genM0 M n; modmult_full C Cinv n; bcinv (swapperh1 n; genM0 M n).

Definition safe_swap a b := if a =? b then bcskip else bcswap a b.
Fixpoint reverser' i n :=
  match i with
  | 0 => safe_swap 0 (n - 1)
  | S i' => reverser' i' n; safe_swap i (n - 1 - i)
  end.
Definition reverser n := reverser' ((n - 1) / 2) n.
  
Definition modmult_rev M C Cinv n := 
  bcinv (reverser n); modmult M C Cinv (S (S n)); reverser n.


(*********** Proofs ***********)

Definition add_c b x y :=
  match b with
  | false => Pos.add x y
  | true => Pos.add_carry x y
  end.

(* reg_push is the encapsulation of fb_push_n. *)
Definition reg_push (x : nat) (n : nat) (f : nat -> bool) := fb_push_n n (nat2fb x) f.

(* The following three lemmas show that the relationship between
   the bool function before and after the application of fb_push/fb_push_n
   in different bit positions. *)
Lemma fb_push_right:
  forall n b f, 0 < n -> fb_push b f n = f (n-1).
Proof.
  intros. induction n. lia.
  simpl. assert ((n - 0) = n) by lia.
  rewrite H0. reflexivity.
Qed.

Lemma fb_push_n_left :
  forall n x f g,
    x < n -> fb_push_n n f g x = f x.
Proof.
  intros. unfold fb_push_n. rewrite <- Nat.ltb_lt in H. rewrite H. easy.
Qed.

Lemma fb_push_n_right :
  forall n x f g,
    n <= x -> fb_push_n n f g x = g (x - n).
Proof.
  intros. unfold fb_push_n. rewrite <- Nat.ltb_ge in H. rewrite H. easy.
Qed.

Notation "'[' x ']_' n f" := (reg_push x n f) (at level 15, n at level 9, right associativity).
Notation "b ` f" := (fb_push b f) (at level 20, right associativity).

(* The lemma shows that the reg_push of a number x that has n qubit is essentially
   the same as turning the number to a bool function. *)
Lemma reg_push_inv:
  forall x n f a, a < n -> (reg_push x n f) a = (nat2fb x) a.
Proof.
  intros.
  unfold nat2fb,N2fb,reg_push,fb_push_n.
  destruct x.
  simpl.
  bdestruct (a <? n).
  unfold nat2fb.
  simpl. reflexivity.
  lia.
  bdestruct (a <? n).
  unfold nat2fb.
  simpl.
  reflexivity.
  lia.
Qed.

Lemma MAJ_eWF :
  forall a b c,
    a <> b -> b <> c -> a <> c ->
    eWF (MAJ c b a).
Proof.
  intros. unfold MAJ. constructor. constructor. 1-2 : apply bccnot_eWF; easy. apply bcccnot_eWF; lia.
Qed.

Lemma MAJ_eWT :
  forall a b c dim,
    a <> b -> b <> c -> a <> c ->
    a < dim -> b < dim -> c < dim ->
    eWT dim (MAJ c b a).
Proof.
  intros. unfold MAJ. constructor. constructor. 1-2 : apply bccnot_eWT; easy. apply bcccnot_eWT; lia.
Qed.

Definition majb a b c := (a && b) ⊕ (b && c) ⊕ (a && c).

Lemma MAJ_correct :
  forall a b c f,
    a <> b -> b <> c -> a <> c ->
    bcexec (MAJ c b a) f = ((f[a |-> majb (f a) (f b) (f c)])
                              [b |-> (f b ⊕ f a)])[c |-> (f c ⊕ f a)].
Proof.
  intros ? ? ? ? Hab' Hbc' Hac'. apply functional_extensionality; intro i. simpl.
  unfold update, majb. bnauto.
Qed.

Lemma UMA_correct_partial :
  forall a b c f' fa fb fc,
    a <> b -> b <> c -> a <> c ->
    f' a = majb fa fb fc ->
    f' b = (fb ⊕ fa) -> f' c = (fc ⊕ fa) ->
    bcexec (UMA c b a) f' = ((f'[a |-> fa])[b |-> fa ⊕ fb ⊕ fc])[c |-> fc].
Proof.
  unfold majb. intros. apply functional_extensionality; intro i. simpl.
  unfold update. bnauto_expand (f' a :: f' b :: f' c :: (List.nil)).
Qed.

Lemma MAJseq'_eWF :
  forall i n,
    0 < n ->
    eWF (MAJseq' i n 0).
Proof.
  induction i; intros. simpl. apply MAJ_eWF; lia.
  simpl. constructor. apply IHi; easy. apply MAJ_eWF; lia.
Qed.

Lemma MAJseq'_eWT :
  forall i n dim,
    0 < n -> i < n -> (S (S (n + i))) < dim ->
    eWT dim (MAJseq' i n 0).
Proof.
  induction i; intros. simpl. apply MAJ_eWT; lia.
  simpl. constructor. apply IHi.
  1 - 3: lia. 
  apply MAJ_eWT.
  1 - 6 : lia.
Qed.

Lemma MAJ_efresh:
  forall a b c,
    a <> b -> b <> c -> a <> c
    -> a <> 1 -> b <> 1 -> c <> 1 ->
    efresh 1 (MAJ c b a).
Proof.
  intros. unfold MAJ.
  repeat apply efresh_seq.
  unfold bccnot.
  constructor. lia.
  constructor. lia. 
  unfold bccnot.
  constructor. lia.
  constructor. lia. 
  unfold bcccnot.
  constructor. lia.
  constructor. lia. 
  constructor. lia. 
Qed.

Lemma MAJseq'_efresh_1 :
  forall i n,
    0 < n ->
    efresh 1 (MAJseq' i n 0).
Proof.
  induction i; intros. simpl.
  apply MAJ_efresh.
  1 - 6: lia.
  simpl.
  constructor.
  apply IHi.
  lia.
  apply MAJ_efresh.
  1 - 6 : lia.
Qed.

Lemma UMA_efresh:
  forall a b c,
    a <> b -> b <> c -> a <> c
    -> a <> 1 -> b <> 1 -> c <> 1 ->
    efresh 1 (UMA c b a).
Proof.
  intros. unfold UMA.
  repeat apply efresh_seq.
  unfold bcccnot.
  constructor. lia.
  constructor. lia. 
  constructor. lia. 
  unfold bccnot.
  constructor. lia.
  constructor. lia. 
  unfold bcccnot.
  constructor. lia.
  constructor. lia. 
Qed.

Lemma UMAseq'_efresh :
  forall i n,
    0 < n ->
    efresh 1 (UMAseq' i n 0).
Proof.
  induction i; intros. simpl.
  apply UMA_efresh.
  1 - 6: lia.
  simpl.
  constructor.
  apply UMA_efresh.
  1 - 6 : lia.
  apply IHi.
  lia.
Qed.

Lemma UMA_eWF:
  forall a b c,
    a <> b -> b <> c -> a <> c ->
    eWF (UMA c b a).
Proof.
  intros.
  unfold UMA.
  repeat apply eWF_seq.
  apply bcccnot_eWF.
  1 - 3 : lia.
  apply bccnot_eWF.
  apply H1.
  apply bccnot_eWF.
  lia.
Qed.

Lemma UMA_eWT:
  forall a b c dim,
    a <> b -> b <> c -> a <> c ->
    a < dim -> b < dim -> c < dim ->
    eWT dim (UMA c b a).
Proof.
  intros.
  unfold UMA.
  repeat constructor.
  1 - 12 : lia.
Qed.

Lemma UMAseq'_eWF: forall i n, 0 < n -> eWF (UMAseq' i n 0).
Proof.
  intros. induction i.
  simpl.
  apply UMA_eWF.
  1 -3 : lia.
  simpl.
  apply eWF_seq.
  apply UMA_eWF.
  1 - 3: lia.
  apply IHi.
Qed.

Lemma UMAseq'_eWT: forall i n dim, 0 < n 
           -> (S (S (n + i))) < dim -> eWT dim (UMAseq' i n 0).
Proof.
  intros. induction i.
  simpl.
  apply UMA_eWT.
  1 - 6 : lia.
  simpl.
  constructor.
  apply UMA_eWT.
  1 - 6: lia.
  apply IHi.
  lia. 
Qed.

Lemma adder01_eWF: forall n, 0 < n -> eWF (adder01 n).
Proof.
 intros. unfold adder01, MAJseq, UMAseq.
 apply eWF_seq. apply MAJseq'_eWF.
 assumption.
 apply UMAseq'_eWF.
 assumption.
Qed.

Lemma adder01_eWT: forall n dim, 0 < n -> (S (S (n + n))) < dim -> eWT dim (adder01 n).
Proof.
 intros. unfold adder01, MAJseq, UMAseq.
 constructor. apply MAJseq'_eWT.
 assumption. lia. lia.
 apply UMAseq'_eWT.
 lia. lia.
Qed.

Lemma adder01_efresh: forall n, 0 < n -> efresh 1 (adder01 n).
Proof.
 intros. unfold adder01, MAJseq, UMAseq.
 constructor. apply MAJseq'_efresh_1.
 assumption.
 apply UMAseq'_efresh.
 assumption.
Qed.

(* Here we defined the specification of carry value for each bit. *)
Fixpoint carry b n f g :=
  match n with
  | 0 => b
  | S n' => let c := carry b n' f g in
           let a := f n' in
           let b := g n' in
           (a && b) ⊕ (b && c) ⊕ (a && c)
  end.

Lemma carry_sym :
  forall b n f g,
    carry b n f g = carry b n g f.
Proof.
  intros. induction n. reflexivity.
  simpl. rewrite IHn. btauto.
Qed.

Lemma carry_false_0_l: forall n f, 
    carry false n allfalse f = false.
Proof.
  unfold allfalse.
  induction n.
  simpl.
  reflexivity.
  intros. simpl.
  rewrite IHn. rewrite andb_false_r.
  reflexivity.
Qed.

Lemma carry_false_0_r: forall n f, 
    carry false n f allfalse = false.
Proof.
  unfold allfalse.
  induction n.
  simpl.
  reflexivity.
  intros. simpl.
  rewrite IHn. rewrite andb_false_r.
  reflexivity.
Qed.

Lemma carry_fbpush :
  forall n a ax ay fx fy,
    carry a (S n) (fb_push ax fx) (fb_push ay fy) = carry (majb a ax ay) n fx fy.
Proof.
  induction n; intros.
  simpl. unfold majb. btauto.
  remember (S n) as Sn. simpl. rewrite IHn. unfold fb_push. subst.
  simpl. easy.
Qed.

Lemma carry_succ :
  forall m p,
    carry true m (pos2fb p) allfalse = pos2fb (Pos.succ p) m ⊕ (pos2fb p) m.
Proof.
  induction m; intros. simpl. destruct p; reflexivity.
  replace allfalse with (fb_push false allfalse).
  2:{ unfold fb_push, allfalse. apply functional_extensionality. intros. destruct x; reflexivity.
  }
  Local Opaque fb_push carry.
  destruct p; simpl.
  rewrite carry_fbpush; unfold majb; simpl. rewrite IHm. reflexivity.
  rewrite carry_fbpush; unfold majb; simpl. rewrite carry_false_0_r. Local Transparent fb_push. simpl. btauto.
  rewrite carry_fbpush; unfold majb; simpl. Local Transparent carry. destruct m; reflexivity.
Qed.

Lemma carry_succ' :
  forall m p,
    carry true m allfalse (pos2fb p) = pos2fb (Pos.succ p) m ⊕ (pos2fb p) m.
Proof.
  intros. rewrite carry_sym. apply carry_succ.
Qed.

Lemma carry_succ0 :
  forall m, carry true m allfalse allfalse = pos2fb xH m.
Proof.
  induction m. easy. 
  replace allfalse with (fb_push false allfalse).
  2:{ unfold fb_push, allfalse. apply functional_extensionality. intros. destruct x; reflexivity.
  }
  rewrite carry_fbpush. unfold majb. simpl. rewrite carry_false_0_l. easy.
Qed.

Lemma carry_add_pos_eq :
  forall m b p q,
    carry b m (pos2fb p) (pos2fb q) ⊕ (pos2fb p) m ⊕ (pos2fb q) m = pos2fb (add_c b p q) m.
Proof.
  induction m; intros. simpl. destruct p, q, b; reflexivity.
  Local Opaque carry.
  destruct p, q, b; simpl; rewrite carry_fbpush; 
    try (rewrite IHm; reflexivity);
    try (unfold majb; simpl; 
         try rewrite carry_succ; try rewrite carry_succ'; 
         try rewrite carry_succ0; try rewrite carry_false_0_l;
         try rewrite carry_false_0_r;
         unfold allfalse; try btauto; try (destruct m; reflexivity)).
Qed.

Lemma carry_add_eq_carry0 :
  forall m x y,
    carry false m (N2fb x) (N2fb y) ⊕ (N2fb x) m ⊕ (N2fb y) m = (N2fb (x + y)) m.
Proof.
  intros.
  destruct x as [|p]; destruct y as [|q]; simpl; unfold allfalse.
  rewrite carry_false_0_l. easy.
  rewrite carry_false_0_l. btauto.
  rewrite carry_false_0_r. btauto.
  apply carry_add_pos_eq.
Qed.

Lemma carry_add_eq_carry1 :
  forall m x y,
    carry true m (N2fb x) (N2fb y) ⊕ (N2fb x) m ⊕ (N2fb y) m = (N2fb (x + y + 1)) m.
Proof.
  intros. 
  destruct x as [|p]; destruct y as [|q]; simpl; unfold allfalse.
  rewrite carry_succ0. destruct m; easy.
  rewrite carry_succ'. replace (q + 1)%positive with (Pos.succ q) by lia. btauto.
  rewrite carry_succ. replace (p + 1)%positive with (Pos.succ p) by lia. btauto.
  rewrite carry_add_pos_eq. unfold add_c. rewrite Pos.add_carry_spec. replace (p + q + 1)%positive with (Pos.succ (p + q)) by lia. easy.
Qed.

Lemma MAJseq'_efresh :
  forall i n j,
    0 < n ->
    j = 1   \/   2 + i < j < 2 + n   \/  2 + n + i < j ->
    efresh j (MAJseq' i n 0).
Proof.
  induction i; intros. simpl. repeat (try constructor; try lia).
  simpl. repeat (try constructor; try apply IHi; try lia).
Qed.

Definition fbxor f g := fun (i : nat) => f i ⊕ g i.

Definition msma i b f g := fun (x : nat) => if (x <? i) then 
        (carry b (S x) f g ⊕ (f (S x))) else (if (x =? i) then carry b (S x) f g else f x).

Definition msmb i (b : bool) f g := fun (x : nat) => if (x <=? i) then (f x ⊕ g x) else g x.

Definition msmc i b f g := fun (x : nat) => if (x <=? i) then (f x ⊕ g x) else (carry b x f g ⊕ f x ⊕ g x).

Definition sumfb b f g := fun (x : nat) => carry b x f g ⊕ f x ⊕ g x.

Ltac fb_push_n_simpl := repeat (try rewrite fb_push_n_left by lia; try rewrite fb_push_n_right by lia).
Ltac update_simpl := repeat (try rewrite update_index_neq by lia); try rewrite update_index_eq by lia.

Ltac BreakIfExpression :=
  match goal with
  | [ |- context[if ?X <? ?Y then _ else _] ] => bdestruct (X <? Y); try lia
  | [ |- context[if ?X <=? ?Y then _ else _] ] => bdestruct (X <=? Y); try lia
  | [ |- context[if ?X =? ?Y then _ else _] ] => bdestruct (X =? Y); try lia
  end.

Ltac IfExpSimpl := repeat BreakIfExpression.

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

Local Opaque MAJ.
Lemma MAJseq'_correct :
  forall i n c f g h b1,
    0 < n -> i < n ->
    bcexec (MAJseq' i n 0) (c ` b1 ` fb_push_n n f (fb_push_n n g h)) = 
           (c ⊕ (f 0)) ` b1 ` fb_push_n n (msma i c f g) (fb_push_n n (msmb i c f g) h).
Proof.
  induction i; intros.
  - simpl. rewrite MAJ_correct by lia. simpl.
    fb_push_n_simpl. replace (n - n) with 0 by lia.
    apply functional_extensionality. intros.
    bdestruct (x =? 0). subst. simpl. update_simpl. easy.
    bdestruct (x =? 2 + n). subst. simpl. update_simpl. fb_push_n_simpl. replace (n - n) with 0 by lia. unfold msmb. bnauto.
    bdestruct (x =? 2). subst. simpl. update_simpl. fb_push_n_simpl. unfold msma. bnauto.
    update_simpl.
    destruct x. easy. simpl. destruct x. easy. simpl.
    bdestruct (x <? n). fb_push_n_simpl. unfold msma. bnauto.
    fb_push_n_simpl. symmetry. fb_push_n_simpl.
    bdestruct (x <? n + n). fb_push_n_simpl. unfold msmb. IfExpSimpl. easy.
    fb_push_n_simpl. easy.
  - simpl. rewrite IHi by lia. rewrite MAJ_correct by lia. simpl.
    fb_push_n_simpl. replace (n + S i - n) with (S i) by lia.
    apply functional_extensionality. intros.
    bdestruct (x =? 2 + i). subst. simpl. update_simpl. fb_push_n_simpl. apply msm_eq1 with (n := n). easy.
    bdestruct (x =? 2 + n + (1 + i)). subst. simpl. update_simpl. fb_push_n_simpl. replace (n + S i - n) with (S i) by lia. apply msm_eq2 with (n := n). easy.
    bdestruct (x =? 3 + i). subst. simpl. update_simpl. fb_push_n_simpl. apply msm_eq3 with (n := n). easy.
    update_simpl.
    destruct x. easy. destruct x. easy. simpl.
    bdestruct (x <? n). fb_push_n_simpl. unfold msma. IfExpSimpl. easy. easy.
    fb_push_n_simpl. symmetry. fb_push_n_simpl.
    bdestruct (x <? n + n). fb_push_n_simpl. unfold msmb. IfExpSimpl. easy. easy.
    fb_push_n_simpl. easy.
Qed.

Local Opaque UMA.
Local Transparent carry.
Lemma UMAseq'_correct :
  forall i n c f g h b1,
    0 < n -> i < n ->
    bcexec (UMAseq' i n 0) ((c ⊕ (f 0)) ` b1 ` fb_push_n n (msma i c f g) (fb_push_n n (msmc i c f g) h))
 = c ` b1 ` fb_push_n n f (fb_push_n n (sumfb c f g) h).
Proof.
  induction i; intros.
  - simpl. rewrite UMA_correct_partial with (fa := f 0) (fb := g 0) (fc := carry c 0 f g). 2-4 : lia.
    apply functional_extensionality. intros.
    bdestruct (x =? 0). subst. simpl. update_simpl. easy.
    bdestruct (x =? 2 + n). subst. simpl. update_simpl. fb_push_n_simpl. replace (n - n) with 0 by lia. unfold sumfb. IfExpSimpl. simpl. btauto.
    bdestruct (x =? 2). subst. simpl. update_simpl. fb_push_n_simpl. easy.
    update_simpl.
    destruct x. easy. simpl. destruct x. easy. simpl.
    bdestruct (x <? n). fb_push_n_simpl. unfold msma. IfExpSimpl. easy.
    fb_push_n_simpl. symmetry. fb_push_n_simpl.
    bdestruct (x <? n + n). fb_push_n_simpl. unfold msmc, sumfb. IfExpSimpl. easy.
    fb_push_n_simpl. easy.
    simpl. fb_push_n_simpl. unfold msma. IfExpSimpl. simpl. unfold majb. simpl. btauto.
    simpl. fb_push_n_simpl. replace (n - n) with 0 by lia. unfold msmc. IfExpSimpl. btauto.
    simpl. easy.
  - simpl.
    replace (bcexec (UMA (S (S i)) (S (S (n + S i))) (S (S (S i)))) ((c ⊕ f 0) ` b1 ` fb_push_n n (msma (S i) c f g) (fb_push_n n (msmc (S i) c f g) h))) with (((c ⊕ f 0) ` b1 ` fb_push_n n (msma i c f g) (fb_push_n n (msmc i c f g) h))).
    2:{ rewrite UMA_correct_partial with (fa := f (S i)) (fb := g (S i)) (fc := carry c (S i) f g). 2-4 : lia.
        apply functional_extensionality. intros.
        bdestruct (x =? 2 + i). subst. simpl. update_simpl. fb_push_n_simpl. unfold msma. IfExpSimpl. easy.
        bdestruct (x =? 2 + n + (1 + i)). subst. simpl. update_simpl. fb_push_n_simpl. replace (n + S i - n) with (S i) by lia. unfold msmc. IfExpSimpl. simpl. btauto.
        bdestruct (x =? 3 + i). subst. simpl. update_simpl. simpl. fb_push_n_simpl. unfold msma. IfExpSimpl. easy.
        update_simpl.
        destruct x. easy. simpl. destruct x. easy. simpl.
        bdestruct (x <? n). fb_push_n_simpl. unfold msma. IfExpSimpl. easy. easy.
        fb_push_n_simpl. symmetry. fb_push_n_simpl.
        bdestruct (x <? n + n). fb_push_n_simpl. unfold msmc, sumfb. IfExpSimpl. easy. easy.
        fb_push_n_simpl. easy.
        simpl. fb_push_n_simpl. unfold msma. IfExpSimpl. simpl. unfold majb. btauto.
        simpl. fb_push_n_simpl. replace (n + S i - n) with (S i) by lia. unfold msmc. IfExpSimpl. btauto.
        simpl. fb_push_n_simpl. unfold msma. IfExpSimpl. easy.
    } 
    rewrite IHi by lia. easy.
Qed.
Local Opaque carry.

Lemma adder01_correct_fb :
  forall n c f g h b1,
    0 < n ->
    bcexec (adder01 n) (c ` b1 ` fb_push_n n f (fb_push_n n g h)) = c ` b1 ` fb_push_n n f (fb_push_n n (sumfb c f g) h).
Proof.
  intros. unfold adder01. simpl. unfold MAJseq, UMAseq. rewrite MAJseq'_correct by lia.
  replace (fb_push_n n (msmb (n - 1) c f g) h ) with (fb_push_n n (msmc (n - 1) c f g) h).
  2:{ apply functional_extensionality. intros.
      bdestruct (x <? n). fb_push_n_simpl. unfold msmc, msmb. IfExpSimpl. easy.
      fb_push_n_simpl. easy.
  }
  apply UMAseq'_correct; lia.
Qed.

Lemma sumfb_correct_carry0 :
  forall x y,
    sumfb false (nat2fb x) (nat2fb y) = nat2fb (x + y).
Proof.
  intros. unfold nat2fb. rewrite Nnat.Nat2N.inj_add.
  apply functional_extensionality. intros. unfold sumfb. rewrite carry_add_eq_carry0. easy.
Qed.

Lemma sumfb_correct_carry1 :
  forall x y,
    sumfb true (nat2fb x) (nat2fb y) = nat2fb (x + y + 1).
Proof.
  intros. unfold nat2fb. do 2 rewrite Nnat.Nat2N.inj_add.
  apply functional_extensionality. intros. unfold sumfb. rewrite carry_add_eq_carry1. easy.
Qed.

Lemma sumfb_correct_N_carry0 :
  forall x y,
    sumfb false (N2fb x) (N2fb y) = N2fb (x + y).
Proof.
  intros. apply functional_extensionality. intros. unfold sumfb. rewrite carry_add_eq_carry0. easy.
Qed.

Lemma pos2fb_Postestbit :
  forall n i,
    (pos2fb n) i = Pos.testbit n (N.of_nat i).
Proof.
  induction n; intros.
  - destruct i; simpl. easy. rewrite IHn. destruct i; simpl. easy. rewrite Pos.pred_N_succ. easy.
  - destruct i; simpl. easy. rewrite IHn. destruct i; simpl. easy. rewrite Pos.pred_N_succ. easy.
  - destruct i; simpl. easy. easy.
Qed.

Lemma N2fb_Ntestbit :
  forall n i,
    (N2fb n) i = N.testbit n (N.of_nat i).
Proof.
  intros. destruct n. easy.
  simpl. apply pos2fb_Postestbit.
Qed.

Lemma Z2N_Nat2Z_Nat2N :
  forall x,
    Z.to_N (Z.of_nat x) = N.of_nat x.
Proof.
  destruct x; easy.
Qed.

Lemma Nofnat_mod :
  forall x y,
    y <> 0 ->
    N.of_nat (x mod y) = ((N.of_nat x) mod (N.of_nat y))%N.
Proof.
  intros. specialize (Zdiv.mod_Zmod x y H) as G.
  repeat rewrite <- Z2N_Nat2Z_Nat2N. rewrite G. rewrite Z2N.inj_mod; lia.
Qed.

Lemma Nofnat_pow :
  forall x y,
    N.of_nat (x ^ y) = ((N.of_nat x) ^ (N.of_nat y))%N.
Proof.
  intros. induction y. easy.
  Local Opaque N.pow. replace (N.of_nat (S y)) with ((N.of_nat y) + 1)%N by lia.
 simpl. rewrite N.pow_add_r. rewrite N.pow_1_r. rewrite Nnat.Nat2N.inj_mul. rewrite IHy. lia.
Qed.

Lemma reg_push_exceed :
  forall n x f,
    [x]_n f = [x mod 2^n]_n f.
Proof.
  intros. unfold reg_push. unfold nat2fb.
  apply functional_extensionality; intro i.
  bdestruct (i <? n). fb_push_n_simpl. rewrite Nofnat_mod. 2: apply Nat.pow_nonzero; lia.
  rewrite Nofnat_pow. simpl.
  do 2 rewrite N2fb_Ntestbit. rewrite N.mod_pow2_bits_low. easy. lia.
  fb_push_n_simpl. easy.
Qed.

(* The following two lemmas show the correctness of the adder implementation based on MAJ;UMA circuit. 
   The usage of the adder is based on the carry0 lemma. *)
Lemma adder01_correct_carry0 :
  forall n x y f b1,
    0 < n ->
    bcexec (adder01 n) (false ` b1 ` [x]_n [y]_n f) = (false ` b1 ` [x]_n [x + y]_n f).
Proof.
  intros. unfold reg_push. rewrite adder01_correct_fb by easy. rewrite sumfb_correct_carry0. easy.
Qed.

Lemma adder01_correct_carry1 :
  forall n x y f b1,
    0 < n ->
    bcexec (adder01 n) (true ` b1 ` [x]_n [y]_n f) = (true` b1 ` [x]_n [x + y + 1]_n f).
Proof.
  intros. unfold reg_push. rewrite adder01_correct_fb by easy. rewrite sumfb_correct_carry1. easy.
Qed.

Opaque adder01.

Lemma swapper02'_eWF: forall i n, eWF (swapper02' i n).
Proof.
 intros. induction i.
 simpl. apply eWF_skip.
 simpl. apply eWF_seq.
 apply IHi. apply bcswap_eWF.
Qed.

Lemma swapper02'_eWT: forall i n dim, 
  n > 0 -> (2 + n + n + i) < dim -> eWT dim (swapper02' i n).
Proof.
 intros. induction i.
 simpl. constructor.
 lia. simpl. constructor.
 apply IHi. lia. apply bcswap_eWT.
 all: lia.
Qed.

Lemma swapper02_eWF: forall n, eWF (swapper02 n).
Proof.
 intros. unfold swapper02. apply swapper02'_eWF.
Qed.

Lemma swapper02_eWT: forall n dim, 
  n > 0 -> (2 + n + n + n) < dim -> eWT dim (swapper02 n).
Proof.
 intros. unfold swapper02. apply swapper02'_eWT; lia.
Qed.

Definition swapma i (f g : nat -> bool) := fun x => if (x <? i) then g x else f x.
Definition swapmb i (f g : nat -> bool) := fun x => if (x <? i) then f x else g x.

Lemma swapma_gtn_invariant :
  forall n f g h,
    fb_push_n n (swapma n f g) h = fb_push_n n g h.
Proof.
  intros. apply functional_extensionality; intro.
  bdestruct (x <? n). fb_push_n_simpl. unfold swapma. IfExpSimpl. easy.
  fb_push_n_simpl. easy.
Qed.

Lemma swapmb_gtn_invariant :
  forall n f g h,
    fb_push_n n (swapmb n f g) h = fb_push_n n f h.
Proof.
  intros. apply functional_extensionality; intro.
  bdestruct (x <? n). fb_push_n_simpl. unfold swapmb. IfExpSimpl. easy.
  fb_push_n_simpl. easy.
Qed.

Lemma swapper02'_correct :
  forall i n f g h u b1 b2,
    0 < n ->
    i <= n ->
    bcexec (swapper02' i n) (b1 ` b2 ` fb_push_n n f (fb_push_n n g (fb_push_n n h u))) 
= b1 ` b2 ` fb_push_n n (swapma i f h) (fb_push_n n g (fb_push_n n (swapmb i f h) u)).
Proof.
  induction i; intros.
  - simpl.
    replace (swapma 0 f h) with f by (apply functional_extensionality; intro; IfExpSimpl; easy).
    replace (swapmb 0 f h) with h by (apply functional_extensionality; intro; IfExpSimpl; easy).
    easy.
  - simpl. rewrite IHi by lia.
    apply functional_extensionality; intro. 
    unfold update.
    bdestruct (x =? S (S i)). subst. simpl. fb_push_n_simpl. unfold swapma, swapmb. IfExpSimpl. apply f_equal. lia.
    bdestruct (x =? S (S (n + n + i))). subst. simpl. fb_push_n_simpl. unfold swapma, swapmb. IfExpSimpl. apply f_equal. lia.
    destruct x. easy. simpl. destruct x. easy. simpl.
    bdestruct (x <? n). fb_push_n_simpl. unfold swapma. IfExpSimpl; easy.
    bdestruct (x <? n + n). fb_push_n_simpl. easy.
    bdestruct (x <? n + n + n). fb_push_n_simpl. unfold swapmb. IfExpSimpl; easy.
    fb_push_n_simpl. easy.
Qed.

Lemma swapper02_correct :
  forall n x y z f b0 b1,
    0 < n ->
    bcexec (swapper02 n) (b0 ` b1 ` [x]_n [y]_n [z]_n f) = b0 ` b1 ` [z]_n [y]_n [x]_n f.
Proof.
  intros. unfold reg_push, swapper02. rewrite swapper02'_correct by lia.
  rewrite swapma_gtn_invariant. rewrite swapmb_gtn_invariant. easy.
Qed.

Opaque swapper02.

Lemma negator0'_eWF :
  forall i, eWF (negator0' i).
Proof.
  induction i. simpl. constructor. simpl. constructor. easy. constructor.
Qed.

Lemma negator0'_eWT :
  forall i dim, 2 + i < dim -> eWT dim (negator0' i).
Proof.
  intros.
  induction i. simpl. constructor. lia.
  simpl. constructor.
  apply IHi. lia. constructor. lia.
Qed.

Lemma negator0_eWF :
  forall n, eWF (negator0 n).
Proof.
  intros. unfold negator0. apply negator0'_eWF.
Qed.

Lemma negator0_eWT :
  forall n dim, 2 + n < dim -> eWT dim (negator0 n).
Proof.
  intros. unfold negator0. apply negator0'_eWT. lia.
Qed.

Lemma negator0'_efresh :
  forall i, efresh 1 (negator0' i).
Proof.
  induction i. simpl. constructor. simpl. constructor. easy. constructor. lia.
Qed.

Lemma negator0_efresh :
  forall n, efresh 1 (negator0 n).
Proof.
  intros. unfold negator0. apply negator0'_efresh.
Qed.

Definition negatem i (f : nat -> bool) := fun (x : nat) => if (x <? i) then ¬ (f x) else f x.

Lemma negator0'_correct :
  forall i n f g b1 b2,
    0 < n ->
    i <= n ->
    bcexec (negator0' i) (b1 ` b2 ` fb_push_n n f g) = b1 ` b2 ` fb_push_n n (negatem i f) g.
Proof.
  induction i; intros.
  - simpl. replace (negatem 0 f) with f by (apply functional_extensionality; intro; IfExpSimpl; easy).
    easy.
  - simpl. rewrite IHi by lia. apply functional_extensionality; intro.
    bdestruct (x =? 2 + i). subst. simpl. update_simpl. fb_push_n_simpl. unfold negatem. IfExpSimpl. easy.
    update_simpl. destruct x. easy. simpl. destruct x. easy. simpl.
    bdestruct (x <? n). fb_push_n_simpl. unfold negatem. IfExpSimpl; easy.
    fb_push_n_simpl. easy.
Qed.

Lemma negatem_Nlnot :
  forall (n : nat) (x : N) i,
    negatem n (N2fb x) i = N.testbit (N.lnot x (N.of_nat n)) (N.of_nat i).
Proof.
  intros. unfold negatem. rewrite N2fb_Ntestbit. symmetry.
  bdestruct (i <? n). apply N.lnot_spec_low. lia.
  apply N.lnot_spec_high. lia.
Qed.

Lemma negatem_arith :
  forall n x,
    x < 2^n ->
    negatem n (nat2fb x) = nat2fb (2^n - 1 - x).
Proof.
  intros. unfold nat2fb. apply functional_extensionality; intro i.
  rewrite negatem_Nlnot. rewrite N2fb_Ntestbit.
  do 2 rewrite Nnat.Nat2N.inj_sub. rewrite Nofnat_pow. simpl.
  bdestruct (x =? 0). subst. simpl. rewrite N.ones_equiv. rewrite N.pred_sub. rewrite N.sub_0_r. easy.
  rewrite N.lnot_sub_low. rewrite N.ones_equiv. rewrite N.pred_sub. easy.
  apply N.log2_lt_pow2. assert (0 < x) by lia. lia.
  replace 2%N with (N.of_nat 2) by lia. rewrite <- Nofnat_pow. lia.
Qed.

(* The correctness represents the actual effect of flip all bits for the number x.
   The effect is to make the x number positions to store the value  2^n - 1 - x. *)
Lemma negator0_correct :
  forall n x f b0 b1,
    0 < n ->
    x < 2^n ->
    bcexec (negator0 n) (b0 ` b1 ` [x]_n f) = b0 ` b1 ` [2^n - 1 - x]_n f.
Proof.
  intros. unfold negator0. unfold reg_push. rewrite negator0'_correct by lia. rewrite negatem_arith; easy.
Qed.

Opaque negator0.

Local Opaque bccnot.
Lemma highb01_eWF :
  forall n,
    0 < n ->
    eWF (highb01 n).
Proof.
  intros. unfold highb01. constructor. constructor. unfold MAJseq. apply MAJseq'_eWF. easy.
  apply bccnot_eWF. lia. apply eWF_bcinv. unfold MAJseq. apply MAJseq'_eWF. easy.
Qed.

Lemma highb01_eWT :
  forall n dim,
    0 < n ->
    S (S (S (n + n))) < dim ->
    eWT dim (highb01 n).
Proof.
  intros. unfold highb01. constructor. constructor. unfold MAJseq. apply MAJseq'_eWT; lia.
  apply bccnot_eWT; lia. unfold MAJseq. apply bcinv_eWT. apply MAJseq'_eWT; lia.
Qed.

Local Opaque bccnot.
Lemma highb01_correct :
  forall n b f g h,
    0 < n ->
    bcexec (highb01 n) (b ` false ` fb_push_n n f (fb_push_n n g h))
             = b ` (carry b n f g) ` fb_push_n n f (fb_push_n n g h).
Proof.
  intros. unfold highb01. simpl. unfold MAJseq. rewrite MAJseq'_correct by lia.
  assert (forall u b0, bcexec (bccnot (S n) 1) (b0 ` false ` u) = b0 ` (u (n - 1)) ` u).
  { intros. rewrite bccnot_correct by lia. apply functional_extensionality; intro.
    bdestruct (x =? 1). subst. update_simpl. Local Opaque xorb. simpl.
    destruct n eqn:E. lia. simpl. rewrite Nat.sub_0_r. btauto.
    update_simpl. destruct x. easy. destruct x. lia. easy.
  }
  rewrite H0. fb_push_n_simpl.
  erewrite bcinv_reverse. 3: apply MAJseq'_correct; lia.
  unfold msma. IfExpSimpl. replace (S (n - 1)) with n by lia. easy.
  apply MAJseq'_eWF. easy.
Qed.

Opaque highb01.

Lemma comparator01_eWF :
  forall n,
    0 < n ->
    eWF (comparator01 n).
Proof.
  intros. unfold comparator01. repeat constructor. apply negator0_eWF. 
  apply highb01_eWF. easy. apply eWF_bcinv. apply negator0_eWF.
Qed.

Lemma comparator01_eWT :
  forall n dim,
    0 < n -> S (S (S (n + n))) < dim ->
    eWT dim (comparator01 n).
Proof.
  intros. unfold comparator01. constructor.
  constructor.  constructor. constructor. lia.
  apply negator0_eWT. lia. 
  apply highb01_eWT. easy. easy.
  simpl. constructor. apply bcinv_eWT. apply negator0_eWT.
  lia.  constructor. lia.
Qed.

Lemma negations_aux :
  forall n x f b,
    0 < n ->
    x < 2^n ->
    bcexec (bcx 0; negator0 n) (false ` b ` [x]_n f) = true ` b ` [2^n - 1 - x]_n f.
Proof.
  intros. simpl.
  assert ((false ` b ` [x ]_ n f) [0 |-> true] = true ` b ` [x]_n f).
  { apply functional_extensionality; intro i. destruct i; update_simpl; easy.
  }
  rewrite H1. apply negator0_correct; easy.
Qed.

Lemma pow2_predn :
  forall n x,
    x < 2^(n-1) -> x < 2^n.
Proof.
  intros. destruct n. simpl in *. lia.
  simpl in *. rewrite Nat.sub_0_r in H. lia.
Qed.

Lemma Ntestbit_lt_pow2n :
  forall x n,
    (x < 2^n)%N ->
    N.testbit x n = false.
Proof.
  intros. apply N.mod_small in H. rewrite <- H. apply N.mod_pow2_bits_high. lia.
Qed.

Lemma Ntestbit_in_pow2n_pow2Sn :
  forall x n,
    (2^n <= x < 2^(N.succ n))%N ->
    N.testbit x n = true.
Proof.
  intros. assert (N.log2 x = n) by (apply N.log2_unique; lia).
  rewrite <- H0. apply N.bit_log2.
  assert (2^n <> 0)%N by (apply N.pow_nonzero; easy).
  lia.
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

(* The correctness of comparator. We can see that the comparator will finally
   produce no changes to the positions storing values x and y, 
   but the high-bit will be a boolean predicate of(x <=? y). *)
Lemma comparator01_correct :
  forall n x y f,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    bcexec (comparator01 n) (false ` false ` [x]_n [y]_n f) = (false ` (x <=? y) ` [x]_n [y]_n f).
Proof.
  intros. specialize (pow2_predn n x H0) as G0. specialize (pow2_predn n y H1) as G1.
  unfold comparator01. remember (bcx 0; negator0 n) as negations. simpl. subst.
  rewrite negations_aux by easy. unfold reg_push. rewrite highb01_correct by easy.
  erewrite bcinv_reverse. 3: apply negations_aux; easy. rewrite carry_leb_equiv by easy. easy.
  constructor. constructor. apply negator0_eWF.
Qed.

Opaque comparator01.

Lemma subtractor01_efresh:
   forall n, 0 < n -> efresh 1 (subtractor01 n).
Proof.
  intros.
  unfold subtractor01.
  constructor. constructor.
  constructor. constructor.
  lia.
  apply negator0_efresh.
  apply adder01_efresh.
  assumption.
  apply efresh_bcinv.
  constructor. constructor.
  lia.
  apply negator0_efresh.
Qed.

Lemma subtractor01_eWF:
   forall n, 0 < n -> eWF (subtractor01 n).
Proof.
  intros.
  unfold subtractor01.
  constructor. constructor.
  constructor. constructor.
  apply negator0_eWF.
  apply adder01_eWF.
  assumption.
  apply eWF_bcinv.
  constructor. constructor.
  apply negator0_eWF.
Qed.

Lemma subtractor01_eWT:
   forall n dim, 0 < n -> S (S (S (n + n))) < dim -> eWT dim (subtractor01 n).
Proof.
  intros.
  unfold subtractor01.
  constructor. constructor.
  constructor. constructor. lia.
  apply negator0_eWT. lia.
  apply adder01_eWT.
  assumption. lia.
  simpl. constructor.
  apply bcinv_eWT. 
  apply negator0_eWT. lia.
  constructor. lia.
Qed.

(* The correctness proof of the subtractor. *)
Lemma subtractor01_correct :
  forall n x y b1 f,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    bcexec (subtractor01 n) (false ` b1 ` [x]_n [y]_n f) = (false ` b1 ` [x]_n [y + 2^n - x]_n f).
Proof.
  intros. specialize (pow2_predn n x H0) as G0. specialize (pow2_predn n y H1) as G1.
  unfold subtractor01. remember (bcx 0; negator0 n) as negations. simpl. subst.
  rewrite negations_aux by easy. rewrite adder01_correct_carry1 by easy.
  erewrite bcinv_reverse. 3: apply negations_aux; easy.
  replace (2^n) with (2^(n-1) + 2^(n-1)).
  replace (2 ^ (n - 1) + 2 ^ (n - 1) - 1 - x + y + 1) with (y + (2 ^ (n - 1) + 2 ^ (n - 1)) - x) by lia.
  easy. destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
  constructor. constructor. apply negator0_eWF.
Qed.

Opaque subtractor01.

Lemma modadder21_eWF:
 forall n, 0 < n -> eWF (modadder21 n).
Proof.
  intros. unfold modadder21.
  constructor.  constructor.
  constructor.  constructor.
  constructor.  constructor.
  constructor. 
  apply swapper02_eWF.
  apply adder01_eWF.
  assumption.
  apply swapper02_eWF.
  apply comparator01_eWF.
  assumption.
  constructor.
  apply eWF_bygatectrl.
  constructor.
  apply subtractor01_efresh.
  lia.
  apply subtractor01_eWF.
  lia.
  constructor. 
  apply swapper02_eWF.
  apply eWF_bcinv. 
  apply comparator01_eWF.
  lia.   apply swapper02_eWF.
Qed.

Lemma modadder21_eWT:
 forall n dim, 0 < n -> 2 + n + n + n < dim -> eWT dim (modadder21 n).
Proof.
  intros. unfold modadder21.
  constructor.  constructor.
  constructor.  constructor.
  constructor.  constructor.
  constructor. 
  apply swapper02_eWT; lia.
  apply adder01_eWT.
  assumption. lia.
  apply swapper02_eWT; lia.
  apply comparator01_eWT; lia.
  constructor.
  apply eWT_bygatectrl.
  constructor. lia.
  apply subtractor01_efresh.
  lia.
  apply subtractor01_eWT.
  lia. lia.
  constructor. lia. 
  apply swapper02_eWT;lia.
  apply bcinv_eWT.
  apply comparator01_eWT; lia.
  apply swapper02_eWT;lia.
Qed.

Lemma mod_sum_lt :
  forall x y M,
    x < M ->
    y < M ->
    (x + y) mod M < x <-> x + y >= M.
Proof.
  intros. split; intros.
  - assert ((x + y) mod M < x + y) by lia.
    rewrite Nat.div_mod with (y := M) in H2 by lia.
    assert (0 < (x + y) / M) by nia.
    rewrite Nat.div_str_pos_iff in H3 by lia. lia.
  - rewrite Nat.mod_eq by lia.
    assert (1 <= (x + y) / M < 2).
    { split.
      apply Nat.div_le_lower_bound; lia.
      apply Nat.div_lt_upper_bound; lia.
    }
    replace (M * ((x + y) / M)) with M by nia.
    lia.
Qed.

Lemma mod_sum_lt_bool :
  forall x y M,
    x < M ->
    y < M ->
    ¬ (M <=? x + y) = (x <=? (x + y) mod M).
Proof.
  intros. bdestruct (M <=? x + y); bdestruct (x <=? (x + y) mod M); try easy.
  assert ((x + y) mod M < x) by (apply mod_sum_lt; lia). lia.
  assert (x + y >= M) by (apply mod_sum_lt; lia). lia.
Qed.

(* The correctness statement of the modulo adder. *)
Lemma modadder21_correct :
  forall n x y M f,
    1 < n ->
    x < M ->
    y < M ->
    M < 2^(n-2) ->
    bcexec (modadder21 n) (false ` false ` [M]_n [y]_n [x]_n f) = false ` false ` [M]_n [(x + y) mod M]_n [x]_n  f.
Proof.
  intros.
  assert (M < 2^(n-1)).
  { apply pow2_predn. replace (n - 1 - 1) with (n - 2) by lia. easy.
  }
  assert (x + y < 2^(n-1)).
  { replace (2^(n-1)) with (2^(n-2) + 2^(n-2)). lia.
    destruct n. lia. destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
  }
  unfold modadder21. remember (bygatectrl 1 (subtractor01 n); bcx 1) as csub01. simpl. subst.
  rewrite swapper02_correct by lia. rewrite adder01_correct_carry0 by lia.
  rewrite swapper02_correct by lia. rewrite comparator01_correct by lia.
  replace (bcexec (bygatectrl 1 (subtractor01 n); bcx 1)
      (false ` (M <=? x + y) ` [M ]_ n [x + y ]_ n [x ]_ n f))
              with (false ` ¬ (M <=? x + y) ` [M ]_ n [(x + y) mod M]_ n [x ]_ n f). 
  2:{ simpl.
      rewrite bygatectrl_correct by (apply subtractor01_efresh; lia).
      simpl.
      bdestruct (M <=? x + y).
      - rewrite subtractor01_correct by lia.
        replace (x + y + 2^n - M) with (x + y - M + 2^n) by lia.
        rewrite reg_push_exceed with (x := x + y - M + 2 ^ n).
        assert (2^n <> 0) by (apply Nat.pow_nonzero; easy).
        rewrite <- Nat.add_mod_idemp_r with (a := x + y - M) by easy.
        rewrite Nat.mod_same by easy.
        rewrite Nat.add_0_r. rewrite <- reg_push_exceed.
        rewrite Nat.mod_eq by lia.
        assert (x + y < 2 * M) by lia.
        assert ((x + y) / M < 2) by (apply Nat.div_lt_upper_bound; lia).
        assert (1 <= (x + y) / M) by (apply Nat.div_le_lower_bound; lia).
        assert ((x + y) / M = 1) by lia.
        replace (x + y - M * ((x + y) / M)) with (x + y - M) by lia.
        apply functional_extensionality; intro i.
        destruct i. easy. destruct i. simpl. update_simpl. easy. update_simpl. easy.
      - rewrite Nat.mod_small by lia. 
        apply functional_extensionality; intro i.
        destruct i. easy. destruct i. simpl. update_simpl. easy. update_simpl. easy.
  }
  rewrite swapper02_correct by lia. erewrite bcinv_reverse.
  3:{ assert ((x + y) mod M < M) by (apply Nat.mod_upper_bound; lia).
      rewrite mod_sum_lt_bool by easy. rewrite comparator01_correct. reflexivity.
      1-3 : lia.
  }
  rewrite swapper02_correct by lia. easy.
  apply comparator01_eWF. lia.
Qed.

Opaque modadder21.

Lemma swapper12'_eWF:
  forall i n, eWF (swapper12' i n).
Proof.
  intros.
  induction i.
  simpl.
  apply eWF_skip.
  simpl. apply eWF_seq.
  apply IHi. apply bcswap_eWF.
Qed.

Lemma swapper12'_eWT:
  forall i n dim, n > 0 -> (2 + n + n + i) < dim -> eWT dim (swapper12' i n).
Proof.
  intros.
  induction i.
  simpl. constructor. lia.
  simpl. constructor.
  apply IHi. lia. apply bcswap_eWT; lia.
Qed.

Lemma swapper12_eWF:
  forall n, eWF (swapper12 n).
Proof.
 intros. unfold swapper12. apply swapper12'_eWF.
Qed.

Lemma swapper12_eWT:
  forall n dim, n > 0 -> (2 + n + n + n) < dim -> eWT dim (swapper12 n).
Proof.
 intros. unfold swapper12. apply swapper12'_eWT; lia.
Qed.

Lemma swapper12'_correct :
  forall i n f g h u b1 b2,
    0 < n ->
    i <= n ->
    bcexec (swapper12' i n) (b1 ` b2 ` fb_push_n n f (fb_push_n n g (fb_push_n n h u)))
                 = b1 ` b2 ` fb_push_n n f (fb_push_n n (swapma i g h) (fb_push_n n (swapmb i g h) u)).
Proof.
  induction i; intros.
  - simpl.
    replace (swapma 0 f h) with f by (apply functional_extensionality; intro; IfExpSimpl; easy).
    replace (swapmb 0 f h) with h by (apply functional_extensionality; intro; IfExpSimpl; easy).
    easy.
  - simpl. rewrite IHi by lia.
    apply functional_extensionality; intro.
    unfold update.
    bdestruct (x =? S (S (n + i))). subst. simpl. fb_push_n_simpl. 
    unfold swapma, swapmb. IfExpSimpl. replace (n + n + i - n - n) with (n + i - n) by lia. easy.
    bdestruct (x =? S (S (n + n + i))). subst. simpl. fb_push_n_simpl. 
    unfold swapma, swapmb. IfExpSimpl. replace (n + n + i - n - n) with (n + i - n) by lia. easy.
    destruct x. easy. simpl. destruct x. easy. simpl.
    bdestruct (x <? n). fb_push_n_simpl. easy. 
    bdestruct (x <? n + n). fb_push_n_simpl. unfold swapma. IfExpSimpl; easy.
    bdestruct (x <? n + n + n). fb_push_n_simpl. unfold swapmb. IfExpSimpl; easy.
    fb_push_n_simpl. easy.
Qed.

Lemma swapper12_correct :
  forall n x y z f b0 b1,
    0 < n ->
    bcexec (swapper12 n) (b0 ` b1 ` [x]_n [y]_n [z]_n f) = b0 ` b1 ` [x]_n [z]_n [y]_n f.
Proof.
  intros. unfold reg_push, swapper12. rewrite swapper12'_correct by lia.
  rewrite swapma_gtn_invariant. rewrite swapmb_gtn_invariant. easy.
Qed.

Opaque swapper12.

Definition double_prop x n (f:nat -> bool) :=
         fun i => if i <? n then f i
                   else if i =? n then f (n + x)
                   else if (n <? i) && (i <=? n + x) then f (i-1) else f i.


Lemma doubler1'_eWF :
  forall i n, eWF (doubler1' i n).
Proof.
  intros.
  induction i.
  simpl. constructor. 
  simpl. constructor. 
  apply bcswap_eWF.
  apply IHi.  
Qed.

Lemma doubler1'_eWT :
  forall i n dim, (n + i) < dim -> eWT dim (doubler1' i n).
Proof.
  intros.
  induction i.
  simpl. constructor. 
  simpl. lia. 
  simpl. constructor. 
  apply bcswap_eWT; lia.
  apply IHi. lia.  
Qed.

Lemma doubler1_eWF :
  forall n, eWF (doubler1 n).
Proof.
  intros. unfold doubler1. apply doubler1'_eWF.
Qed.

Lemma doubler1_eWT :
  forall n dim, 0 < n -> (n + n + 1) < dim -> eWT dim (doubler1 n).
Proof.
  intros. unfold doubler1. apply doubler1'_eWT; lia.
Qed.

Lemma N_inj_pow: forall n, (N.of_nat (2 ^ n) = 2 ^ (N.of_nat n))%N.
Proof.
  intros.
 induction n.
 simpl. rewrite N.pow_0_r.
 reflexivity.
 simpl.
 assert (N.pos (Pos.of_succ_nat n) = N.succ (N.of_nat n)) by lia.
 rewrite H.
 rewrite N.pow_succ_r.
 rewrite <- IHn. lia. lia.
Qed.

(* This lemma says that if x is a value less than 2^(n-1), then the highest bit of
   the n-bit cell is zero. *)
Lemma reg_push_high_bit_zero:
   forall n x f, 
    0 < n -> x < 2^(n-1) -> ([x]_n f) (n - 1) = false.
Proof.
  intros. unfold reg_push. unfold nat2fb.
  fb_push_n_simpl.
  rewrite N2fb_Ntestbit.
  rewrite Ntestbit_lt_pow2n.
  reflexivity.
  apply N2Z.inj_lt.
  assert (N.of_nat ( 2 ^ (n - 1)) = (2 ^ N.of_nat (n - 1)))%N.
  rewrite N_inj_pow.
  reflexivity.
  rewrite <- H1.
  rewrite nat_N_Z.
  rewrite nat_N_Z.
  apply Nat2Z.inj_lt.
  assumption.
Qed.

(* This is a generalized case of the above lemma. *)
Lemma reg_push_high_bit_gen_zero:
   forall i m n x f,
    0 < n -> i <= m < n -> x < 2^i -> ([x]_n f) m = false.
Proof.
  intros. unfold reg_push. unfold nat2fb.
  fb_push_n_simpl.
  rewrite N2fb_Ntestbit.
  rewrite Ntestbit_lt_pow2n.
  reflexivity.
  apply N2Z.inj_lt.
  assert (N.of_nat ( 2 ^ m) = (2 ^ N.of_nat m))%N.
  rewrite N_inj_pow.
  reflexivity.
  rewrite <- H2.
  rewrite nat_N_Z.
  rewrite nat_N_Z.
  apply Nat2Z.inj_lt.
  assert (2 ^ i <= 2 ^ m).
  apply Nat.pow_le_mono_r.
  1 - 3 : lia.
Qed.

(* This is a generalized case of the above lemma in terms of making the case for
   any value x located in any places in a bool function. *)
Lemma reg_push_high_bit_gen_zero_1:
  forall i m n x y f b0 b1,
    0 < n -> i <= m < n ->
    y < 2^i -> (b0 ` b1 ` [x]_n [y]_n f) (2 + n + m) = false.
Proof.
  intros.
  rewrite fb_push_right by lia. rewrite fb_push_right by lia.
  assert (([x ]_ n [y ]_ n f) (2 + n + m - 1 - 1)
         = ([y ]_ n f) ((2 + n + m - 1 - 1) - n)).
  unfold reg_push.
  rewrite fb_push_n_right.
  reflexivity.
  lia.
  rewrite H2.
  assert ((2 + n + m - 1 - 1 - n) = m) by lia.
  rewrite H3.
  rewrite (reg_push_high_bit_gen_zero i).
  reflexivity.
  1 - 3 : assumption.
Qed.

Lemma bcswap_same: forall a b f, f a = f b -> bcexec (bcswap a b) f = f.
Proof.
  intros.
  rewrite bcswap_correct.
  apply functional_extensionality; intros.
  bdestruct (x =? a).
  rewrite <- H. rewrite H0.
  reflexivity.
  bdestruct (x =? b).
  rewrite H. rewrite H1.
  reflexivity.
  reflexivity.
Qed.

Lemma bcswap_neq :
  forall a b c f, a <> c -> b <> c -> bcexec (bcswap a b) f c = f c.
Proof.
  intros.
  rewrite bcswap_correct.
  IfExpSimpl.
  reflexivity.
Qed.

Definition times_two_spec (f:nat -> bool) :=  fun i => if i =? 0 then false else f (i-1).

(* Showing the times_two spec is correct. *)

Lemma nat2fb_even_0:
  forall x, nat2fb (2 * x) 0 = false.
Proof.
  intros.
  unfold nat2fb.
  rewrite Nat2N.inj_double.
  unfold N.double.
  destruct (N.of_nat x).
  unfold N2fb,allfalse.
  reflexivity.
  unfold N2fb.
  simpl.
  reflexivity.
Qed.

Lemma pos2fb_times_two_eq:
  forall p x, x <> 0 -> pos2fb p (x - 1) = pos2fb p~0 x.
Proof.
  intros.
  induction p.
  simpl.
  assert ((false ` true ` pos2fb p) x = (true ` pos2fb p) (x - 1)).
  rewrite fb_push_right.
  reflexivity. lia.
  rewrite H0.
  reflexivity.
  simpl.
  rewrite (fb_push_right x).
  reflexivity. lia.
  simpl.
  rewrite (fb_push_right x).
  reflexivity. lia.
Qed.

Lemma times_two_correct:
   forall n x, 0 < n -> x < 2^(n-1)
         -> (times_two_spec (nat2fb x)) = (nat2fb (2*x)).
Proof.
  intros.
  unfold times_two_spec.
  apply functional_extensionality; intros.
  unfold nat2fb.
  bdestruct (x0 =? 0).
  rewrite H1.
  specialize (nat2fb_even_0 x) as H2.
  unfold nat2fb in H2.
  rewrite H2.
  reflexivity.
  rewrite Nat2N.inj_double.
  unfold N.double,N2fb.
  destruct (N.of_nat x).
  unfold allfalse.
  reflexivity.
  rewrite pos2fb_times_two_eq.
  reflexivity. lia.
Qed.

Lemma doubler1_correct_aux :
  forall i n f, bcexec (doubler1' i n) f = double_prop i n f.
Proof.
  intros i.
  induction i.
  unfold double_prop.
  simpl.
  intros.
  apply functional_extensionality; intros.
  bdestruct (x <? n).
  reflexivity.
  bdestruct (x =? n).
  rewrite H0.
  rewrite Nat.add_0_r.
  reflexivity.
  bdestruct (n <? x).
  bdestruct (x <=? n + 0).
  lia.
  simpl.
  reflexivity.
  simpl. reflexivity.
  intros.
  simpl.
  rewrite IHi.
  unfold double_prop.
  apply functional_extensionality; intros.
  IfExpSimpl.
  rewrite 2 update_index_neq by lia.
  reflexivity.
  unfold update.
  IfExpSimpl.
  reflexivity.
  bdestruct (n <? x).
  bdestruct ((x <=? n + i)).
  simpl.
  unfold update.
  bdestruct (x - 1 =? n + i). lia.
  bdestruct (x - 1 =? n + S i).
  lia.
  bdestruct (x <=? n + S i).
  reflexivity.
  lia.
  simpl.
  unfold update.
  bdestruct (x =? n + i).
  lia.
  bdestruct (x =? n + S i).
  bdestruct (x <=? n + S i). subst.
  assert (n + S i - 1 = n + i) by lia.
  rewrite H4. reflexivity.
  lia.
  bdestruct (x <=? n + S i). lia.
  reflexivity.
  simpl.
  assert (x = n) by lia.
  unfold update.
  bdestruct (x =? n + i).
  lia.
  bdestruct (x =? n + S i). 
  lia.
  reflexivity.
Qed.

(* This is the correctness statement and proof of the doubler. *)
Lemma doubler1_correct :
  forall n x y f b0 b1,
    0 < n ->
    y < 2^(n - 1) ->
    bcexec (doubler1 n) (b0 ` b1 ` [x]_n [y]_n f) = b0 ` b1 ` [x]_n [2 * y]_n f.
Proof.
  intros.
  unfold doubler1.
  rewrite doubler1_correct_aux; try lia.
  apply functional_extensionality; intros.
  unfold double_prop.
  bdestruct (x0 <? 2 + n).
  destruct x0. simpl. reflexivity.
  rewrite fb_push_right by lia.
  rewrite (fb_push_right (S x0)) by lia.
  assert ((S x0 - 1) = x0) by lia.
  rewrite H2.
  destruct x0. simpl. reflexivity.
  rewrite fb_push_right by lia.
  rewrite (fb_push_right (S x0)) by lia.
  assert ((S x0 - 1) = x0) by lia.
  rewrite H3.
  rewrite reg_push_inv by lia.
  rewrite reg_push_inv by lia.
  reflexivity.
  bdestruct (x0 =? 2 + n).
  rewrite H2.
  repeat rewrite fb_push_right by lia.
  assert (([x ]_ n [y ]_ n f) (2 + n + (n - 1) - 1 - 1)
            = ([y ]_ n f) ((2 + n + (n - 1) - 1 - 1) - n)).
  unfold reg_push.
  rewrite fb_push_n_right by lia.
  reflexivity.
  rewrite H3.
  assert (([x ]_ n [2 * y ]_ n f) (2 + n - 1 - 1) 
          = ([2 * y ]_ n f) (2 + n - 1 - 1 - n)).
  unfold reg_push.
  rewrite fb_push_n_right by lia.
  reflexivity.
  rewrite H4.
  assert ((2 + n + (n - 1) - 1 - 1 - n) = n - 1) by lia.
  rewrite H5.
  rewrite reg_push_high_bit_zero by lia.
  assert ( (2 + n - 1 - 1 - n) = 0) by lia.
  rewrite H6.
  rewrite reg_push_inv by lia.
  rewrite nat2fb_even_0.
  reflexivity.
  bdestruct ((2 + n <? x0)).
  bdestruct ((x0 <=? 2 + n + (n - 1))).
  simpl.
  repeat rewrite fb_push_right by lia.
  assert (([x ]_ n [y ]_ n f) (x0 - 1 - 1 - 1)
       = ([y ]_ n f) (x0 - 1 - 1 - 1 - n)).
  unfold reg_push.
  rewrite fb_push_n_right by lia.
  reflexivity.
  assert (([x ]_ n [y + (y + 0) ]_ n f) (x0 - 1 - 1)
        = ([y + (y + 0) ]_ n f) (x0 - 1 - 1 - n)).
  unfold reg_push.
  rewrite fb_push_n_right by lia.
  reflexivity.
  rewrite H5. rewrite H6.
  assert (y + (y + 0) = 2 * y) by lia.
  rewrite H7.
  remember (x0 - (2 + n)) as y0.
  assert ((x0 - 1 - 1 - 1 - n) = y0 - 1) by lia.
  assert ((x0 - 1 - 1 - n) = y0) by lia.
  rewrite H8. rewrite H9.
  repeat rewrite reg_push_inv by lia.
  rewrite <- (times_two_correct n).
  unfold times_two_spec.
  bdestruct (y0 =? 0).
  lia.
  reflexivity.
  1 - 2 : lia.
  simpl.
  repeat rewrite fb_push_right by lia.
  unfold reg_push.
  repeat rewrite fb_push_n_right by lia.
  reflexivity.
  lia.
Qed.

Opaque doubler1.

Lemma moddoubler01_eWF :
  forall n, 0 < n -> eWF (moddoubler01 n).
Proof.
  intros.
  unfold moddoubler01.
  constructor. constructor.
  apply doubler1_eWF. 
  apply comparator01_eWF.
  lia.
  apply eWF_bygatectrl.
  constructor. 
  apply subtractor01_efresh.
  lia. 
  apply subtractor01_eWF.
  lia. 
Qed.

Lemma moddoubler01_eWT :
  forall n dim, 0 < n -> (n + n + 3) < dim -> eWT dim (moddoubler01 n).
Proof.
  intros.
  unfold moddoubler01.
  constructor. constructor.
  apply doubler1_eWT; lia. 
  apply comparator01_eWT;lia.
  apply eWT_bygatectrl.
  constructor. lia. 
  apply subtractor01_efresh.
  lia. 
  apply subtractor01_eWT;lia.
Qed.

(* The correctness statement and proof of the mod doubler.  *)
Lemma moddoubler01_correct :
  forall n M x f,
    1 < n ->
    x < M ->
    M < 2^(n - 2) ->
    bcexec (moddoubler01 n) (false ` false ` [M]_n [x]_n f) = false ` (M <=? 2 * x) ` [M]_n [2 * x mod M]_n f.
Proof.
  intros.
  assert (M < 2^(n-1)).
  { apply pow2_predn. replace (n - 1 - 1) with (n - 2) by lia. easy.
  }
  assert (x + x < 2^(n-1)).
  { replace (2^(n-1)) with (2^(n-2) + 2^(n-2)). lia.
    destruct n. lia. destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
  }
 unfold moddoubler01.
 rewrite bcseq_correct.
 rewrite bcseq_correct.
 rewrite doubler1_correct; try lia.
 rewrite comparator01_correct; try lia.
 simpl.
 rewrite bygatectrl_correct by (apply subtractor01_efresh; lia).
 simpl.
 bdestruct (M <=? x + (x + 0)).
  - rewrite subtractor01_correct; try lia.
    replace (x + (x + 0) + 2 ^ n - M) with (x + (x + 0) - M + 2^n) by lia.
    rewrite reg_push_exceed with (x := (x + (x + 0) - M + 2^n)).
    assert (2^n <> 0) by (apply Nat.pow_nonzero; easy).
    rewrite <- Nat.add_mod_idemp_r with (a := x + (x + 0) - M) by easy.
    rewrite Nat.mod_same by easy.
    rewrite Nat.add_0_r. rewrite <- reg_push_exceed.
    rewrite Nat.add_0_r. rewrite Nat.add_0_r in H4.
    rewrite Nat.mod_eq by lia.
    assert (x + x < 2 * M) by lia.
    assert ((x + x) / M < 2) by (apply Nat.div_lt_upper_bound; lia).
    assert (1 <= (x + x) / M) by (apply Nat.div_le_lower_bound; lia).
    assert ((x + x) / M = 1) by lia.
    replace (x + x - M * ((x + x) / M)) with (x + x - M) by lia.
    reflexivity.
  - rewrite Nat.mod_small by lia. 
    reflexivity.
Qed.

Opaque moddoubler01.

Lemma modadder12_eWF :
  forall n, 0 < n -> eWF (modadder12 n).
Proof.
  intros.
  unfold modadder12.
  apply eWF_seq.
  apply eWF_seq.
  apply swapper12_eWF.
  apply modadder21_eWF.
  lia. 
  apply swapper12_eWF.
Qed.

Lemma modadder12_eWT :
  forall n dim, 0 < n -> 2 + n + n + n < dim -> eWT dim (modadder12 n).
Proof.
  intros.
  unfold modadder12.
  constructor. constructor. 
  apply swapper12_eWT;lia.
  apply modadder21_eWT;lia.
  apply swapper12_eWT;lia.
Qed.

(* The correctness statement and proof of the second mod adder. *)
Lemma modadder12_correct :
  forall n x y M f,
    1 < n ->
    x < M ->
    y < M ->
    M < 2^(n-2) ->
    bcexec (modadder12 n) (false ` false ` [M]_n [x]_n [y]_n f) = false ` false ` [M]_n [x]_n [(x + y) mod M]_n f.
Proof.
 intros.
 unfold modadder12.
 rewrite bcseq_correct.
 rewrite bcseq_correct.
 rewrite swapper12_correct by lia.
 rewrite modadder21_correct; try lia.
 rewrite swapper12_correct by lia.
 reflexivity.
Qed.

Opaque modadder12.

Lemma modsummer'_eWF :
  forall i n f, 0 < n -> eWF (modsummer' i n f).
Proof.
  intros.
  induction i.
  simpl.
  destruct (f 0).
  apply modadder12_eWF.
  lia. 
  constructor. 
  simpl.
  constructor. constructor. constructor.  
  apply IHi.
  apply moddoubler01_eWF.
  lia. 
  apply bcswap_eWF.
  destruct (f (S i)).
  apply modadder12_eWF.
  lia. constructor. 
Qed.

Lemma modsummer'_eWT :
  forall i n f dim, 0 < n ->
       (2 + n + n + n + i) < dim -> eWT dim (modsummer' i n f).
Proof.
  intros.
  induction i.
  simpl.
  destruct (f 0).
  apply modadder12_eWT;lia. 
  constructor. lia. 
  simpl.
  constructor. constructor. constructor.  
  apply IHi. lia.
  apply moddoubler01_eWT;lia.
  apply bcswap_eWT;lia.
  destruct (f (S i)).
  apply modadder12_eWT;lia.
  constructor. lia. 
Qed.

Lemma modsummer_eWF :
  forall n C, 0 < n ->  eWF (modsummer n C).
Proof.
  intros. unfold modsummer. 
  apply modsummer'_eWF.
  lia.
Qed. 

Lemma modsummer_eWT :
  forall n C dim, 0 < n -> (2 + n + n + n + n) < dim -> eWT dim (modsummer n C).
Proof.
  intros. unfold modsummer. 
  apply modsummer'_eWT;lia.
Qed. 

Definition hbf n M x := fun (i : nat) =>
                          if (i =? 0) then false
                          else if (i <=? n)
                               then (M <=? 2 * ((2^(i-1) * x) mod M)) else false.
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

Local Opaque Nat.mul.
Lemma modsummer'_correct :
  forall i n x y M C,
    i < n ->
    1 < n ->
    x < M ->
    y < M ->
    C < M ->
    M < 2^(n-2) ->
    bcexec (modsummer' i n (nat2fb C)) (false ` false ` [M]_n [x]_n [y]_n allfalse)
          = false ` false ` [M]_n [2^i * x mod M]_n
                     [((bindecomp (i+1) C) * x + y) mod M]_n (hbf i M x).
Proof.
  intros.
  induction i.
  simpl.
  unfold nat2fb.
  assert ((fun i : nat =>
     if i =? 0
     then false
     else
      if i <=? 0
      then M <=? (2 * ((2 ^ (i - 1) * x) mod M))
      else false)
              = (fun _ : nat => false)).
  apply functional_extensionality.
  intros. bdestruct (x0 =? 0). reflexivity.
  bdestruct (x0 <=? 0).
  lia. reflexivity.
  destruct (N2fb (N.of_nat C) 0) eqn:eq.
  rewrite N2fb_Ntestbit in eq.
  unfold hbf,allfalse.
  rewrite H5.
  rewrite bindecomp_spec.
  apply nat_is_odd_testbit in eq.
  apply Nat.odd_spec in eq.
  assert (2 ^ 1 = 2) by easy.
  rewrite H6.
  assert (0 <= C) by lia.
  assert (0 < 2) by lia.
  specialize (Nat.mod_bound_pos C 2 H7 H8) as eq1.
  assert (C mod 2 = 0 \/ C mod 2 = 1) by lia.
  destruct H9.
  unfold Nat.Odd in eq.
  destruct eq.
  rewrite H10 in H9.
  assert (2 * x0 + 1 = 1 + x0 * 2) by lia.
  rewrite H11 in H9.
  rewrite Nat.mod_add in H9.
  easy. lia.
  rewrite H9.
  rewrite Nat.mul_1_l.
  apply Nat.mod_small_iff in H1 as eq2.
  rewrite eq2.
  rewrite modadder12_correct.
  reflexivity.
  1 - 4 : assumption.
  lia.
  rewrite N2fb_Ntestbit in eq.
  apply nat_is_even_testbit in eq.
  apply Nat.even_spec in eq.
  unfold Nat.Even in eq.
  destruct eq.
  rewrite bindecomp_spec.
  assert (2 ^ 1 = 2) by easy.
  rewrite H7.
  assert (2 * x0 = x0 * 2) by lia.
  rewrite H8 in H6.
  rewrite H6.
  rewrite Nat.mod_mul.
  simpl.
  apply Nat.mod_small_iff in H1 as eq1.
  apply Nat.mod_small_iff in H2 as eq2.
  rewrite mult_1_l, mult_0_l, plus_0_l.
  rewrite eq1. rewrite eq2.
  unfold hbf,allfalse. simpl. rewrite H5.
  reflexivity.
  1 - 3 : lia.
  simpl.
  rewrite IHi.
  rewrite moddoubler01_correct.
  assert (forall i n M x y z u, 
        bcexec (bcswap 1 (S (S (n + n + n + S i)))) 
            (false ` (M <=? 2 * ((2 ^ i * x) mod M))
                    ` [y]_n [z]_n [u]_n (hbf i M x))
         = (false ` false
                    ` [y]_n [z]_n [u]_n (hbf (S i) M x))).
  { intros.
    rewrite bcswap_correct.
    apply functional_extensionality.
    intros.
    bdestruct (x1 =? 1).
    rewrite fb_push_right by lia.
    rewrite fb_push_right by lia.
    rewrite H5. simpl.
    unfold reg_push.
    rewrite fb_push_n_right by lia.
    rewrite fb_push_n_right by lia.
    rewrite fb_push_n_right by lia.
    assert ((n0 + n0 + n0 + S i0 - 0 - n0 - n0 - n0) = S i0) by lia.
    rewrite H6.
    unfold hbf.
    bdestruct (S i0 =? 0).
    lia.
    bdestruct (S i0 <=? i0).
    lia.
    reflexivity.
    bdestruct (x1 =? S (S (n0 + n0 + n0 + S i0))).
    simpl.
    rewrite H6.
    rewrite fb_push_right by lia.
    rewrite fb_push_right by lia.
    unfold reg_push.
    rewrite fb_push_n_right by lia.
    rewrite fb_push_n_right by lia.
    rewrite fb_push_n_right by lia.
    assert ((S (S (n0 + n0 + n0 + S i0)) - 1 - 1 - n0 - n0 - n0) = S i0) by lia.
    rewrite H7.
    unfold hbf.
    bdestruct (S i0 =? 0).
    lia.
    bdestruct (S i0 <=? S i0).
    assert ((S i0 - 1) = i0) by lia.
    rewrite H10.
    simpl. reflexivity.
    lia.
    bdestruct (x1 =? 0).
    subst. simpl.
    reflexivity.
    bdestruct (2 <=? x1).
    rewrite fb_push_right by lia.
    rewrite fb_push_right by lia.  
    rewrite fb_push_right by lia.
    rewrite fb_push_right by lia.  
    unfold reg_push.
    unfold fb_push_n.
    bdestruct (x1 - 1 - 1 <? n0).
    reflexivity.
    bdestruct ( x1 - 1 - 1 - n0 <? n0).
    reflexivity.
    bdestruct (x1 - 1 - 1 - n0 - n0 <? n0).
    reflexivity.
    unfold hbf.
    bdestruct (x1 - 1 - 1 - n0 - n0 - n0 =? 0).
    reflexivity.
    bdestruct (x1 - 1 - 1 - n0 - n0 - n0 <=? i0).
    bdestruct (x1 - 1 - 1 - n0 - n0 - n0 <=? S i0).
    reflexivity. lia.
    bdestruct (x1 - 1 - 1 - n0 - n0 - n0 <=? S i0).
    lia.
    reflexivity.
    lia.
   }
  simpl in H5.
  rewrite H5.
  destruct (nat2fb C (S i)) eqn:eq.
  rewrite modadder12_correct.
  rewrite Nat.mul_mod_idemp_r.
  rewrite <- Nat.add_mod.
  rewrite bindecomp_seq.
  replace (S i) with (i + 1) in eq by lia.
  rewrite eq.
  simpl.
  replace (2 * (2 ^ i * x)) with (2 * 2 ^ i * x) by lia.
  rewrite <- pow_two_succ_l.
  replace (2 * 2 ^ i * x + (bindecomp (i + 1) C * x + y)) 
    with ((bindecomp (i + 1) C + 1 * (2 ^ i * 2)) * x + y) by lia.
  reflexivity.
  1 - 3 : lia.
  apply Nat.mod_bound_pos. lia. lia.
  apply Nat.mod_bound_pos. lia. lia.
  assumption.
  simpl.
  rewrite Nat.mul_mod_idemp_r.
  rewrite bindecomp_seq.
  replace (S i) with (i + 1) in eq by lia.
  rewrite eq.
  simpl.
  replace (2 * (2 ^ i * x)) with (2 * 2 ^ i * x) by lia.
  rewrite <- pow_two_succ_l.
  replace (bindecomp (i + 1) C * x + y)
    with ((bindecomp (i + 1) C + 0 * (2 ^ i * 2)) * x + y) by lia.
  reflexivity.
  1 - 2 : lia.
  apply Nat.mod_bound_pos. lia. lia.
  lia. lia.
Qed.

(* This is the correctness statement and proof of the C*x%M sum implementation. *)
Lemma modsummer_correct :
  forall n x y M C,
    1 < n ->
    x < M ->
    y < M ->
    C < M ->
    M < 2^(n-2) ->
    bcexec (modsummer n C) (false ` false ` [M]_n [x]_n [y]_n allfalse)
        = false ` false ` [M]_n [2^(n-1) * x mod M]_n [(C * x + y) mod M]_n (hbf (n-1) M x).
Proof.
  intros.
  unfold modsummer.
  rewrite modsummer'_correct.
  assert ((n - 1 + 1) = n) by lia.
  rewrite H4.
  rewrite bindecomp_spec.
  assert (C mod 2 ^ n = C).
  rewrite Nat.mod_small.
  reflexivity.
  assert (n = S (S (n - 2))) by lia.
  rewrite H5. simpl.
  lia.
  rewrite H5.
  reflexivity.
  lia.
  1 - 5: assumption.
Qed.

Opaque modsummer.

Lemma modmult_half_eWF:
  forall n C, 0 < n -> eWF (modmult_half n C).
Proof.
 intros.
 unfold modmult_half.
 constructor.
 apply modsummer_eWF.
 lia. 
 apply eWF_bcinv.
 apply modsummer_eWF.
 lia. 
Qed.

Lemma modmult_half_eWT:
  forall n C dim, 0 < n -> (2 + n + n + n + n) < dim -> eWT dim (modmult_half n C).
Proof.
 intros.
 unfold modmult_half.
 constructor.
 apply modsummer_eWT;lia.
 apply bcinv_eWT.
 apply modsummer_eWT;lia.
Qed.

Lemma modmult_half_correct :
  forall n x M C,
    1 < n ->
    x < M ->
    C < M ->
    M < 2^(n-2) ->
    bcexec (modmult_half n C) (false ` false ` [M]_n [x]_n allfalse)
               = false ` false ` [M]_n [x]_n [C * x mod M]_n allfalse.
Proof.
  intros.
  assert (false ` false ` [M]_n [x]_n allfalse 
           = false ` false ` [M]_n [x]_n [0]_n allfalse).
  unfold fb_push, reg_push, fb_push_n.
  apply functional_extensionality.
  intros.
  destruct x0.
  reflexivity.
  destruct x0.
  reflexivity.
  IfExpSimpl.
  1 - 4: reflexivity.
  rewrite H3.
  unfold modmult_half.
  simpl.
  rewrite modsummer_correct by lia.
  apply (bcinv_reverse (modsummer n 0) (false ` false ` [M ]_ n [x ]_ n [(C * x) mod M ]_ n allfalse)).
  2: {
   rewrite modsummer_correct.
   rewrite Nat.mul_0_l.
   rewrite Nat.add_0_l.
   rewrite Nat.add_0_r.
   rewrite Nat.mod_mod.
   reflexivity.
   1 - 3: lia.
   apply Nat.mod_upper_bound.
   1 - 3: lia.
  }
 apply modsummer_eWF.
 lia. 
Qed.

Opaque modmult_half.

Lemma modmult_full_eWT:
    forall n C Cinv dim, 0 < n -> (2 + n + n + n + n) < dim -> eWT dim ((modmult_full C Cinv n)).
Proof.
  intros. unfold modmult_full.
  constructor. constructor.
  apply modmult_half_eWT;lia.
  apply swapper12_eWT;lia.
  apply bcinv_eWT.
  apply modmult_half_eWT;lia.
Qed.

Lemma modmult_full_correct :
  forall n x M C Cinv,
    1 < n ->
    x < M ->
    C < M ->
    Cinv < M -> 
    C * Cinv mod M = 1 ->
    M < 2^(n-2) ->
    bcexec (modmult_full C Cinv n) (false ` false ` [M]_n [x]_n allfalse) 
           = false ` false ` [M]_n [C * x mod M]_n allfalse.
Proof.
  intros.
  unfold modmult_full.
  simpl.
  rewrite modmult_half_correct by lia.
  rewrite swapper12_correct by lia.
  apply (bcinv_reverse (modmult_half n Cinv) (false ` false ` [M ]_ n [(C * x) mod M ]_ n allfalse)).
  apply modmult_half_eWF. lia.
  rewrite modmult_half_correct; try lia.
  rewrite Nat.mul_mod_idemp_r.
  rewrite Nat.mul_assoc.
  rewrite (Nat.mul_mod (Cinv * C)).
  rewrite (Nat.mul_comm Cinv).
  rewrite H3.
  rewrite Nat.mul_1_l.
  rewrite Nat.mod_mod.
  rewrite (Nat.mod_small x) by lia.
  reflexivity.
  1 - 3 : lia.
  apply Nat.mod_upper_bound. lia.
Qed.

Opaque modmult_full.

Lemma swapperh1'_eWF :
  forall i n, eWF (swapperh1' i n).
Proof.
  induction i; intros. simpl. constructor. 
  simpl. constructor. 
  apply IHi. apply bcswap_eWF. 
Qed.

Lemma swapperh1'_eWT :
  forall i n dim, 2 + n + i < dim -> eWT dim (swapperh1' i n).
Proof.
  induction i; intros. simpl. constructor. lia.
  simpl. constructor. 
  apply IHi. lia. apply bcswap_eWT; lia.
Qed.

Lemma swapperh1_eWF :
  forall n, eWF (swapperh1 n).
Proof.
  intros. unfold swapperh1. apply swapperh1'_eWF.
Qed.

Definition swaph1m i n f := fun x => if (x <? i) then false else if (x <? n)
                       then f x else if (x <? 2 + n) then false else if (x <? 2 + n + i) then f (x - 2 - n) else false.

Lemma swapperh1'_correct :
  forall i n f,
    0 < n ->
    i <= n ->
    bcexec (swapperh1' i n) (fb_push_n n f allfalse) = swaph1m i n f.
Proof.
  induction i; intros. simpl. apply functional_extensionality; intro x.
   unfold swaph1m. bdestruct (x <? n). fb_push_n_simpl. IfExpSimpl. easy. fb_push_n_simpl. IfExpSimpl. easy. easy.
  simpl. rewrite IHi by lia. unfold update. apply functional_extensionality; intro x.
  unfold swaph1m. IfExpSimpl; try easy. subst. apply f_equal. lia.
Qed.
  
Lemma swapperh1_correct :
  forall n x,
    0 < n ->
    bcexec (swapperh1 n) ([x]_n allfalse) = false ` false ` (fb_push_n n allfalse ([x]_n allfalse)).
Proof.
  intros. unfold swapperh1, reg_push. rewrite swapperh1'_correct by lia. unfold swaph1m. apply functional_extensionality; intro i.
  bdestruct (i <? n). destruct i. easy. destruct i. easy. simpl. fb_push_n_simpl. easy.
  bdestruct (i =? n). subst. simpl. IfExpSimpl. destruct n. easy. destruct n. easy. simpl. fb_push_n_simpl. easy.
  bdestruct (i =? S n). subst. simpl. IfExpSimpl. destruct n. easy. simpl. fb_push_n_simpl. easy.
  bdestruct (i <? 2 + n + n). IfExpSimpl. destruct i. lia. destruct i. lia. simpl. fb_push_n_simpl. rewrite Nat.sub_0_r. easy.
  IfExpSimpl. destruct i. lia. destruct i. lia. simpl. fb_push_n_simpl. easy.
Qed.

Definition genM0m i f := fun x => if (x <? i) then f x else false.

Lemma genM0'_eWF :
  forall i f, eWF (genM0' i f).
Proof.
  induction i; intros. simpl. constructor. 
  simpl. constructor. 
  apply IHi. destruct (f i). constructor. constructor.
Qed.

Lemma genM0'_eWT :
  forall i f dim, 2 + i < dim -> eWT dim (genM0' i f).
Proof.
  induction i; intros. simpl. constructor. lia.
  simpl. constructor.
  apply IHi. lia.
  destruct (f i).
  constructor. lia.
  constructor. lia.
Qed.

Lemma genM0_eWF :
  forall M n, eWF (genM0 M n).
Proof.
  intros. unfold genM0. apply genM0'_eWF.
Qed.

Lemma genM0'_correct :
  forall i n f g b0 b1,
    0 < n ->
    i <= n ->
    bcexec (genM0' i f) (b0 ` b1 ` (fb_push_n n allfalse g)) = b0 ` b1 ` (fb_push_n n (genM0m i f)) g.
Proof.
  induction i; intros; simpl; apply functional_extensionality; intro x.
  - destruct x. easy. destruct x. easy. simpl.
    bdestruct (x <? n). fb_push_n_simpl. unfold genM0m. IfExpSimpl. easy.
    fb_push_n_simpl. easy.
  - rewrite IHi by lia. destruct (f i) eqn:E. simpl.
    bdestruct (x =? 2 + i). subst. update_simpl. simpl. fb_push_n_simpl. unfold genM0m. IfExpSimpl. rewrite E. easy.
    update_simpl. destruct x. easy. destruct x. easy. simpl.
    bdestruct (x <? n). fb_push_n_simpl. unfold genM0m. IfExpSimpl; easy.
    fb_push_n_simpl. easy.
    simpl. destruct x. easy. destruct x. easy. simpl.
    bdestruct (x <? n). fb_push_n_simpl. unfold genM0m. IfExpSimpl. easy. replace x with i by lia. rewrite E. easy. try easy.
    fb_push_n_simpl. easy.
Qed.

Lemma genM0_correct :
  forall n M f b0 b1,
    0 < n ->
    bcexec (genM0 M n) (b0 ` b1 ` (fb_push_n n allfalse f)) = b0 ` b1 ` [M]_n f.
Proof.
  intros. unfold genM0. rewrite genM0'_correct by lia. apply functional_extensionality; intro x.
  destruct x. easy. destruct x. easy.  simpl.
  unfold reg_push. bdestruct (x <? n); fb_push_n_simpl.
  unfold genM0m. IfExpSimpl; easy.
  easy.
Qed.

Lemma modmult_eWT :
  forall M C Cinv n dim, 0 < n -> (2 + n + n + n + n) < dim -> eWT dim (modmult M C Cinv n).
Proof.
  unfold modmult,swapperh1,genM0.
  constructor.   constructor.
  constructor.
  apply swapperh1'_eWT. lia.
  apply genM0'_eWT. lia.
  apply modmult_full_eWT; lia.
  simpl. constructor.
  apply bcinv_eWT. apply genM0'_eWT. lia.
  apply bcinv_eWT. apply swapperh1'_eWT. lia.
Qed.

Lemma modmult_correct :
  forall n x M C Cinv,
    1 < n ->
    x < M ->
    C < M ->
    Cinv < M ->
    C * Cinv mod M = 1 ->
    M < 2^(n-2) ->
    bcexec (modmult M C Cinv n) ([x]_n allfalse) = [C * x mod M]_n allfalse.
Proof.
  intros. unfold modmult. remember (swapperh1 n; genM0 M n) as p.
  assert (forall y, bcexec p ([y]_n allfalse) = false ` false ` [M]_n [y]_n allfalse).
  { rewrite Heqp. intros. simpl. rewrite swapperh1_correct by lia.
    rewrite genM0_correct by lia. easy.
  }
  simpl. rewrite H5. rewrite modmult_full_correct by lia. erewrite bcinv_reverse.
  3: apply H5.
  easy. subst. constructor. apply swapperh1_eWF. apply genM0'_eWF.
Qed.

Opaque modmult.

Definition fbrev' i n (f : nat -> bool) := fun (x : nat) => 
            if (x <=? i) then f (n - 1 - x) else if (x <? n - 1 - i) 
                         then f x else if (x <? n) then f (n - 1 - x) else f x.
Definition fbrev n (f : nat -> bool) := fun (x : nat) => if (x <? n) then f (n - 1 - x) else f x.

Lemma safe_swap_correct :
  forall x y f,
    bcexec (safe_swap x y) f = bcexec (bcswap x y) f.
Proof.
  intros. apply functional_extensionality; intro i. unfold safe_swap.
  simpl. unfold update.
  bdestruct (x =? y); simpl. bnauto.
  unfold update. reflexivity.
Qed.

Lemma reverser'_correct :
  forall i n f g,
    0 < n ->
    i <= (n - 1) / 2 ->
    bcexec (reverser' i n) (fb_push_n n f g) = fb_push_n n (fbrev' i n f) g.
Proof.
  induction i; intros.
  - simpl. rewrite safe_swap_correct. 
    simpl. unfold update.
    apply functional_extensionality; intro. unfold fbrev'.
    bdestruct (x =? 0). subst. fb_push_n_simpl. IfExpSimpl; apply f_equal; lia.
    bdestruct (x =? n - 1). subst. fb_push_n_simpl. IfExpSimpl. apply f_equal. lia.
    bdestruct (x <? n). fb_push_n_simpl. IfExpSimpl. easy.
    fb_push_n_simpl. easy.
  - assert ((n - 1) / 2 < n) by (apply Nat.div_lt_upper_bound; lia).
    simpl. rewrite IHi by lia. 
    rewrite safe_swap_correct. 
    simpl. unfold update.
    apply functional_extensionality; intro. unfold fbrev'.
    assert (2 * ((n - 1) / 2) <= n - 1) by (apply Nat.mul_div_le; easy).
    bdestruct (x =? S i). subst. fb_push_n_simpl. IfExpSimpl; easy.
    bdestruct (x =? n - 1 - S i). subst. fb_push_n_simpl. IfExpSimpl. apply f_equal. lia.
    bdestruct (x <? n). fb_push_n_simpl. IfExpSimpl; easy.
    fb_push_n_simpl. easy.
Qed.

Lemma fbrev'_fbrev :
  forall n f,
    0 < n ->
    fbrev n f = fbrev' ((n - 1) / 2) n f.
Proof.
  intros. unfold fbrev, fbrev'. apply functional_extensionality; intro.
  assert ((n - 1) / 2 < n) by (apply Nat.div_lt_upper_bound; lia).
  assert (2 * ((n - 1) / 2) <= n - 1) by (apply Nat.mul_div_le; easy).
  assert (n - 1 - (n - 1) / 2 <= (n - 1) / 2 + 1).
  { assert (n - 1 <= 2 * ((n - 1) / 2) + 1).
    { assert (2 <> 0) by easy.
      specialize (Nat.mul_succ_div_gt (n - 1) 2 H2) as G.
      lia.
    }
    lia.
  }
  IfExpSimpl; easy.
Qed.

Lemma reverser_correct :
  forall n f g,
    0 < n ->
    bcexec (reverser n) (fb_push_n n f g) = fb_push_n n (fbrev n f) g.
Proof.
  intros. unfold reverser. rewrite reverser'_correct by lia. rewrite fbrev'_fbrev by easy. easy.
Qed.

Lemma safe_swap_eWF :
  forall x y, eWF (safe_swap x y).
Proof. intros. unfold safe_swap. destruct (x =? y); constructor. Qed.

Lemma reverser'_eWF :
  forall i n, eWF (reverser' i n).
Proof.
  induction i; intros. simpl. apply safe_swap_eWF.
  simpl. constructor. apply IHi. apply safe_swap_eWF.
Qed.

Lemma reverser'_eWT :
  forall i n dim, n + i < dim -> eWT dim (reverser' i n).
Proof.
  induction i; intros. simpl. 
  unfold safe_swap. bdestruct (0 =? n - 1); constructor; lia.
  simpl. constructor. apply IHi. lia. 
  unfold safe_swap. bdestruct (S i =? n - 1 - S i); constructor; lia.
Qed.

Lemma reverser_eWF :
  forall n, eWF (reverser n).
Proof.
  intros. unfold reverser. apply reverser'_eWF.
Qed.

Lemma reverser_eWT :
  forall n dim, 0 < n -> n + n < dim -> eWT dim (reverser n).
Proof.
  intros. unfold reverser. apply reverser'_eWT.
  assert ((n - 1) / 2 < n).
  apply Nat.div_lt_upper_bound.
  lia. lia. lia.
Qed.

Opaque reverser.

Lemma fbrev_involutive :
  forall n f,
    fbrev n (fbrev n f) = f.
Proof.
  intros. unfold fbrev. apply functional_extensionality; intro x. IfExpSimpl; apply f_equal; lia.
Qed.

Lemma fbrev_Sn :
  forall n x f,
    fb_push_n (S n) (fbrev (S n) (nat2fb x)) f = fb_push_n n (fbrev n (nat2fb (x / 2))) ((x mod 2 =? 1) ` f).
Proof.
  intros. apply functional_extensionality; intro i.
  bdestruct (i <? n). fb_push_n_simpl. unfold fbrev. IfExpSimpl. unfold nat2fb. do 2 rewrite N2fb_Ntestbit.
   do 2 rewrite <- Nattestbit_Ntestbit.
   replace (S n - 1 - i) with (S (n - 1 - i)) by lia.
   symmetry. apply Nat.div2_bits.
   bdestruct (i =? n). subst. fb_push_n_simpl. replace (n - n) with 0 by lia. 
   unfold fbrev. IfExpSimpl. unfold nat2fb. rewrite N2fb_Ntestbit.
   rewrite <- Nattestbit_Ntestbit. replace (S n - 1 - n) with 0 by lia. rewrite Nat.bit0_eqb. easy.
  fb_push_n_simpl. destruct (i - n) eqn:E. lia. replace (i - S n) with n0 by lia. easy.
Qed.

Lemma f_to_vec_num :
  forall n x f,
    f_to_vec n (fb_push_n n (fbrev n (nat2fb x)) f) = basis_vector (2^n) (x mod (2^n)).
Proof.
  induction n; intros. simpl in *. replace 1 with (2^0) by easy. rewrite <- kron_n_0_is_0_vector. easy.
  simpl. replace (2 ^ n + (2 ^ n + 0)) with (2 * (2^n)) by lia.
  assert (2^n <> 0) by (apply Nat.pow_nonzero; easy).
  rewrite Nat.mod_mul_r by lia.
  rewrite fbrev_Sn. rewrite IHn. fb_push_n_simpl. replace (n - n) with 0 by lia.
  remember ((x / 2) mod 2^n) as y.
  assert (y < 2 ^ n) by (subst; apply Nat.mod_upper_bound; easy).
  replace (((x mod 2 =? 1) ` f) 0) with (x mod 2 =? 1) by easy.
  destruct (x mod 2) eqn:E.
  - replace (0 + 2 * y) with (2 * y) by lia.
    rewrite <- (basis_vector_append_0 (2^n) y); easy.
  - assert (x mod 2 < 2) by (apply Nat.mod_upper_bound; easy).
    replace (S n0) with 1 by lia.
    replace (1 + 2 * y) with (2 * y + 1) by lia.
    rewrite <- (basis_vector_append_1 (2^n) y); easy.
Qed.

Local Transparent Nat.mul.
Lemma f_to_vec_num_with_anc :
  forall anc n x,
    f_to_vec (n + anc) (fb_push_n n (fbrev n (nat2fb x)) allfalse) = basis_vector (2^n) (x mod (2^n)) ⊗ (basis_vector (2^anc) 0).
Proof.
  induction anc; intros. rewrite Nat.add_0_r. rewrite <- kron_n_0_is_0_vector. simpl. rewrite kron_1_r. apply f_to_vec_num.
  replace (n + S anc) with (S (n + anc)) by lia. simpl. fb_push_n_simpl. simpl. rewrite IHanc.
  replace (basis_vector (2 ^ anc + (2 ^ anc + 0)) 0) with (basis_vector (2 * 2^anc) (2 * 0)) by easy.
  assert (2^anc <> 0) by (apply Nat.pow_nonzero; easy).
  rewrite <- (basis_vector_append_0 (2^anc) 0) by lia.
  restore_dims. rewrite kron_assoc. easy.
  apply basis_vector_WF. apply Nat.mod_upper_bound. apply Nat.pow_nonzero; easy.
  apply basis_vector_WF. lia.
  apply WF_qubit0.
Qed.

Lemma basis_vector_inc_from_anc :
  forall n x,
    x < 2^n ->
    [x]_n allfalse = [x]_(S n) allfalse.
Proof.
  intros. apply functional_extensionality; intro i. unfold reg_push.
  bdestruct (i <? n). fb_push_n_simpl. easy.
  bdestruct (i =? n). subst. fb_push_n_simpl. unfold nat2fb. rewrite N2fb_Ntestbit. rewrite <- Nattestbit_Ntestbit. rewrite Nat.testbit_eqb.
  replace (x / 2^n) with 0 by (symmetry; apply Nat.div_small; easy). easy.
  fb_push_n_simpl. easy.
Qed.

Lemma modmult_rev_correct :
  forall n x M C Cinv,
    M > 1 -> M < 2^n ->
    x < M -> C < M -> Cinv < M ->
    C * Cinv mod M = 1 ->
    bcexec (modmult_rev M C Cinv n) (fb_push_n n (fbrev n (nat2fb x)) allfalse) = (fb_push_n n (fbrev n (nat2fb (C * x mod M))) allfalse).
Proof.
  intros.
  assert (0 < n) by (destruct n; simpl in *; lia).
  assert (2^n <> 0) by (apply Nat.pow_nonzero; easy).
  assert ((C * x) mod M < M) by (apply Nat.mod_upper_bound; lia).
  assert (M < 2^(S n)) by (simpl; lia).
  assert (M < 2^(S (S n))) by (simpl; lia).
  assert (M < 2 ^ (S (S n) - 2)) by (replace (S (S n) - 2) with n by lia; easy).
  unfold modmult_rev. simpl. erewrite bcinv_reverse.
  3: rewrite reverser_correct by lia; reflexivity.
  2: apply reverser_eWF.
  replace (fb_push_n n (nat2fb x) allfalse) with ([x]_n allfalse) by easy.
  do 2 rewrite basis_vector_inc_from_anc by lia.
  rewrite modmult_correct by lia.
  do 2 rewrite <- basis_vector_inc_from_anc by lia.
  apply reverser_correct. easy.
Qed.

Lemma modmult_rev_eWT :
  forall n M C Cinv,
    0 < n ->
    eWT (n + (modmult_rev_anc n)) (modmult_rev M C Cinv n).
Proof.
  intros.
  unfold modmult_rev,modmult_rev_anc.
  constructor.   constructor.
  apply bcinv_eWT. apply reverser_eWT; lia.
  apply modmult_eWT; lia.
  apply  reverser_eWT; lia.
Qed.

Opaque modmult_rev.
