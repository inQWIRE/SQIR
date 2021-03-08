Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat.
Require Export RCIR.

Local Open Scope bccom_scope.
Local Open Scope nat_scope.

(* 
  This doc contains the implementation and correctness proof of the modular multiplier
  for the Shor's algorithm.
  
  Modular multiplier finishes the computation of the formula C*x %M, where C and M are two
  integer constants, and x is a integer variable. 

  The high level picuture of the implementation is to take each bit of the binary format of C,
  and then do the two consecutive steps on a three (n+1) qubits math representation as [x][M][y].
  At i-th iteration, the x stores the current computation result for the formula C*x %M up to i-th bit.
  M is the contant value for M, and [y] stores the computation result of 2^i * x % M.
  The first step is to compute the 2^i * x % M based on the old value of 2^(i-1)*x % M. 
  The second step is to add the 2^i*x %M value to the C*x%M if i-th bit of C is not zero. 
*)

(* This is the extra qubits needed for the algorithm presented in the doc. 
   The extra qubit requirement is O(n) in our implementation. *)
Definition modmult_rev_anc n := 3 * n + 11.

(* fb_push is to take a qubit and then push it to the zero position 
        in the bool function representation of a number. *)
Definition fb_push b f : nat -> bool :=
  fun x => match x with
        | O => b
        | S n => f n
        end.

Definition allfalse := fun (_ : nat) => false.

(* fb_push_n is the n repeatation of fb_push. *)
Definition fb_push_n n f g : nat -> bool :=
  fun i => if (i <? n) then f i else g (i - n).

(* A function to compile positive to a bool function. *)
Fixpoint pos2fb p : nat -> bool :=
  match p with
  | xH => fb_push true allfalse
  | xI p' => fb_push true (pos2fb p')
  | xO p' => fb_push false (pos2fb p')
  end.

(* A function to compile N to a bool function. *)
Definition N2fb n : nat -> bool :=
  match n with
  | 0%N => allfalse
  | Npos p => pos2fb p
  end.

Definition add_c b x y :=
  match b with
  | false => Pos.add x y
  | true => Pos.add_carry x y
  end.

(* A function to compile a natural number to a bool function. *)
Definition nat2fb n := N2fb (N.of_nat n).

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


(* Single bit MAJ and UMA circuit implementations. 
   MAJ circuit takes the carry value ci before the computation,
   and two bits ai and bi in two numbers, and the returns three things:
    ci ⊕ ai, bi ⊕ ai and the carry value of next bit.
   The carry value is defined as: (ai && bi) ⊕ (bi && ci) ⊕ (ai && ci)
   UMA takes the result of MAJ, and produces three things:
   ci, si and ai. si represents the i-th bit computation value of a + b *)
Definition majb a b c := (a && b) ⊕ (b && c) ⊕ (a && c).

Definition MAJ a b c := bccnot c b ; bccnot c a ; bcccnot a b c.
Definition UMA a b c := bcccnot a b c ; bccnot c a ; bccnot a b.


(* The implementation of a new constant adder. *)
Definition single_carry (i:nat) (c:nat) (M:nat -> bool) := if M 0 then bccnot i c else bcskip.

(* for anything that is ge 2. *)
Fixpoint half_carry (n:nat) (i:nat) (j:nat) (M : nat -> bool) := 
    match n with 0 => (if M 1 then bccnot (i+1) j ; bcx j else bcskip) ; (if M 0 then bcccnot i (i+1) j else bccnot (i+1) j)
              | S m => (if M (n+1) then bccnot (i+(n+1)) (j+n) ; bcx (j+n) else bcskip); bcccnot (j+m) (i+(n+1)) (j+n);
                               half_carry m i j M; bcccnot (j+m) (i+(n+1)) (j+n)
    end.

Definition acarry (n:nat) (i:nat) (j:nat) (c:nat) (M:nat -> bool) := 
        if n <? 2 then bcskip else if n =? 2 then single_carry i c M 
                    else bccnot (j+n) c; half_carry n i j M;bccnot (j+n) c;half_carry n i j M.

Fixpoint add_carry (n:nat) (i:nat) (j:nat) (c:nat) (M:nat -> bool) :=
        match n with 0 | S 0 => bcskip
                  | S m => acarry n i j c M ; bccnot c (i+n); acarry n i j c M ; add_carry m i j c M
        end.

Fixpoint add_const (n:nat) (i:nat) (M:nat -> bool) :=
     match n with 0 => bcskip
                | S m => if M m then bcx (i+m) else bcskip ; add_const m i M
     end.


(* n is the number of qubits, i is the start position for the variable to add,
                         j is the start position of n dirty bit, and c is the position for the carry bit. *)
Definition new_adder (n:nat) (i:nat) (j:nat) (c:nat) (M:nat -> bool) := add_carry n i j c M ; add_const n i M.

(* The following will do the negation of the first input value in the qubit sequence 00[x][y][z].
   THe actual effect is to make the sequence to be 00[-x][y][z]. *)
Fixpoint negator0' (j:nat) i : bccom :=
  match i with
  | 0 => bcx (j + i)
  | S i' => negator0' j i'; bcx (j + i)
  end.
Definition negator0 j n := negator0' j n.

Definition negatem i (f : nat -> bool) := fun (x : nat) => if (x <? i) then ¬ (f x) else f x.


(* The following implements an comparator. 
   THe first step is to adjust the adder circuit above to be
    MAJ;high_bit_manipulate;UMA.
    This is based on a binary number circuit observation that:
    To compare if x < y, we just need to do x - y, and see the high bit of the binary
    format of x - y. If the high_bit is zero, that means that x >= y;
    otherwise x < y. *)
Definition highb01 (n:nat) (i:nat) (j:nat) (M:nat -> bool) : bccom := acarry n i j 0 M; bccnot (1 + n) 1; bcinv (acarry n i j 0 M).


(* The actual comparator implementation. 
    We first flip the x positions, then use the high-bit comparator above. 
    Then, we use an inverse circuit of flipping x positions to turn the
    low bits back to store the value x.
    The actual implementation in the comparator is to do (x' + y)' as x - y,
    and then, the high-bit actually stores the boolean result of x - y < 0.  *)
Definition comparator01 n i j M := (negator0 i n); highb01 n i j M; bcinv (negator0 i n).


(* The implementation of a subtractor. It takes two values [x][y], and the produces
    the result of [x][y + 2^n - x]. *)
Definition substractor01 n i j M := (negator0 i n); new_adder n i j 0 M; bcinv (negator0 i n).


(*still need rippler adder. *)
Fixpoint UMAseq' n i j c0 : bccom :=
  match n with
  | 0 => UMA c0 j i
  | S m => UMA (i + m) (j + n) (i + m); UMAseq' m i j c0
  end.
Definition UMAseq n i j := UMAseq' n i j 0.

Fixpoint MAJseq' n i j c0 : bccom :=
  match n with
  | 0 => MAJ c0 i j
  | S m => MAJseq' m i j c0; MAJ (j + m) (i + n) (j + n)
  end.
Definition MAJseq n i j := MAJseq' n i j 0.

Definition adder01 n i j: bccom := MAJseq n i j; UMAseq n i j.


(* The implementation of a modulo adder. It takes [M][x][y], and then produces the result of [M][x+y % M][y]. 
   The modulo operation is not reversible. It will flip the high-bit to be the comparator factor.
   To flip the high-bit to zero, we use the inverse circuit of the comparator in the modulo adder to
   flip the high-bit back to zero.*)
Definition modadder21 n i j M := adder01 n i j ; comparator01 n i j M;
             (bccont 1 (substractor01 n i j M); bcx 1); bcinv (comparator01 n i j M).

(* Here we implement the doubler circuit based on binary shift operation.
   It assumes an n-1 value x that live in a cell of n-bits (so the high-bit must be zero). 
   Then, we shift one position, so that the value looks like 2*x in a n-bit cell. *)
Fixpoint doubler1' i n :=
  match i with
  | 0 => bcskip
  | S i' => bcswap (n + i') (n + i); doubler1' i' n
  end.
Definition doubler1 n j := doubler1' n j.

Definition double_prop x n (f:nat -> bool) :=
         fun i => if i <? n then f i
                   else if i =? n then f (n + x)
                   else if (n <? i) && (i <=? n + x) then f (i-1) else f i.


Definition times_two_spec (f:nat -> bool) :=  fun i => if i =? 0 then false else f (i-1).


(* Another version of the mod adder only for computing [x][M] -> [2*x % M][M].
   This version will mark the high-bit, and the high-bit is not clearable.
   However, eventually, we will clean all high-bit
   by using a inverse circuit of the whole implementation.
   We will use bcinv circuit to clean the high-bit. Hopefully this will work. *)
Definition moddoubler01 n i j M := doubler1 n j; comparator01 n j i M; bccont 1 (substractor01 n j i M); bcinv(comparator01 n j i M).


(* The following implements the modulo adder for all bit positions in the
   binary boolean function of C. 
   For every bit in C, we do the two items:
   we first to double the factor (originally 2^(i-1) * x %M, now 2^i * x %M).
   Then, we see if we need to add the factor result to the sum of C*x%M
   based on if the i-th bit of C is zero or not. *)
Fixpoint modsummer' x n i j (M:nat -> bool) (fC : nat -> bool) :=
  match x with
  | 0 => if (fC 0) then modadder21 n i j M else bcskip
  | S x' => modsummer' x' n i j M fC; moddoubler01 n i j M; 
        (if (fC x) then modadder21 n i j M else bcskip)
  end.
Definition modsummer n i j M C := modsummer' n n i j (nat2fb M) (nat2fb C).


Definition hbf n M x := fun (i : nat) =>
                          if (i =? 0) then false
                          else if (i <=? n)
                               then (M <=? 2 * ((2^(i-1) * x) mod M)) else false.
Fixpoint natsum n (f : nat -> nat) :=
  match n with
  | 0 => 0
  | S n' => f n' + natsum n' f
  end.
     

Definition bindecomp n x := natsum n (fun i => Nat.b2n ((nat2fb x) i) * 2^i).


(* This is the final clean-up step of the mod multiplier to do C*x %M. 
    Here, modmult_half will first clean up all high bits.  *)
Definition modmult_half n i j M C := modsummer n i j M C; (bcinv (modsummer n i j M 0)).

(* The modmult_full circuit will take [M][x] bits and produce [M][C*x mod M].
   The key concept is to first compute modmult_half on C, and get [M][x][C*x mod M], 
   We then swap the valuex of x and C*x%M, and get [M][C*x mod M][x],
   and then we do an inverse circuit on the modmult_half on the inverse value of C.
   THe final step will turn the result to be [M][C*x mod M] and remove [x]. *)

Definition modmult_full M C Cinv n := modmult_half n 2 (2+n) M C; bcinv (modmult_half n 2 (2+n) M Cinv).

(* The following is to do the final clean-up of the final clean-up.
   It prepares the two high-bits (two zero bits), and then prepare the empty positions for storing value M. 
   Then, it will insert the value M by using a circuit genM0 for the constant M. *)
Fixpoint swapperh1' j n :=
  match j with
  | 0 => bcskip
  | S j' => swapperh1' j' n; bcswap j' (2 + n + j')
  end.
Definition swapperh1 n := swapperh1' n n.

Definition modmult M C Cinv n := modmult_full M C Cinv n.


Fixpoint reverser' i n :=
  match i with
  | 0 => bcswap 0 (n - 1)
  | S i' => reverser' i' n; bcswap i (n - 1 - i)
  end.
Definition reverser n := reverser' ((n - 1) / 2) n.

Definition fbrev' i n (f : nat -> bool) := fun (x : nat) => 
            if (x <=? i) then f (n - 1 - x) else if (x <? n - 1 - i) 
                         then f x else if (x <? n) then f (n - 1 - x) else f x.
Definition fbrev n (f : nat -> bool) := fun (x : nat) => if (x <? n) then f (n - 1 - x) else f x.

Definition modmult_rev M C Cinv n := bcinv (reverser n); modmult M C Cinv (S (S n)); reverser n.

