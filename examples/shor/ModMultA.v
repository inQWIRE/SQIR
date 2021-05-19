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
Definition modmult_rev_anc n := 2 * n + 3.

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

(* fb update. *)
Definition fb_up x n f g : nat -> bool := 
  fun i => if (i <? x) then g i else if (i <? x + n) then f (i-x) else g i.

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
Definition reg_push (x : nat) (i:nat) (n : nat) (f : nat -> bool) := fb_up i n (nat2fb x) f.

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

Lemma fb_up_left :
  forall i x n f g,
    i < x -> fb_up x n f g i = g i.
Proof.
  intros. unfold fb_up. rewrite <- Nat.ltb_lt in H. rewrite H. easy.
Qed.

Lemma fb_up_mid :
  forall i x n f g,
    x <= i < x + n -> fb_up x n f g i = f (i-x).
Proof.
  intros. unfold fb_up. 
  bdestruct (i <? x). lia.
  bdestruct (i <? x + n). reflexivity.
  lia.
Qed.

Lemma fb_up_right :
  forall i x n f g,
    x + n <= i -> fb_up x n f g i = g i.
Proof.
  intros. unfold fb_up. 
  rewrite <- Nat.ltb_ge in H. rewrite H.
  bdestruct (i <? x).  easy. easy.
Qed.

Lemma fb_push_n_right :
  forall n x f g,
    n <= x -> fb_push_n n f g x = g (x - n).
Proof.
  intros. unfold fb_push_n. rewrite <- Nat.ltb_ge in H. rewrite H. easy.
Qed.

(*Notation "'[' x ']_' n '@' i f" := (reg_push x i n f) (at level 15, n at level 9, i at level 10, right associativity).*)
Notation "b ` f" := (fb_push b f) (at level 20, right associativity).

(* The lemma shows that the reg_push of a number x that has n qubit is essentially
   the same as turning the number to a bool function. *)
Lemma reg_push_inv:
  forall x n f a, a < n -> (reg_push x 0 n f) a = (nat2fb x) a.
Proof.
  intros.
  unfold nat2fb,N2fb,reg_push,fb_up.
  destruct x.
  simpl.
  bdestruct (a <? n).
  unfold nat2fb.
  simpl. reflexivity.
  lia.
  bdestruct (a <? 0). lia.
  bdestruct (a <? 0 + n). simpl in H1.
  unfold nat2fb.
  simpl.
  assert ((a - 0) = a) by lia. rewrite H2.
  easy.
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

Lemma MAJ_correct :
  forall a b c f,
    a <> b -> b <> c -> a <> c ->
    bcexec (MAJ c b a) f = ((f[a |-> majb (f a) (f b) (f c)])
                              [b |-> (f b ⊕ f a)])[c |-> (f c ⊕ f a)].
(*Admitted. 
(* The following proof works, but too slow. Admitted when debugging. *)*)
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
(* Admitted.
(* The following proof works, but too slow. Admitted when debugging. *) *)
Proof.
  unfold majb. intros. apply functional_extensionality; intro i. simpl.
  unfold update. bnauto_expand (f' a :: f' b :: f' c :: (List.nil)).
Qed.

(* The following defines n-bits MAJ and UMA circuit. 
   Eventually, MAJ;UMA circuit takes [y][x] and produce [(x+y) % 2 ^ n][x] *)
Fixpoint MAJseq' n i j c0 : bccom :=
  match n with
  | 0 => MAJ c0 i j
  | S m => MAJseq' m i j c0; MAJ (j + m) (i + n) (j + n)
  end.
Definition MAJseq n i j := MAJseq' (n-1) i j 0.

Definition not_in x i n := forall j ,  i <= j < i+ n -> x <> j.

Definition not_overlap i j n := forall x y, i <= x < i + n -> j <= y < j + n -> x <> y.

Lemma MAJseq'_eWF' :
  forall m n i j c,
    m <= n ->
    not_in c i (n+1) -> not_in c j (n+1) -> not_overlap i j (n+1) ->
    eWF (MAJseq' m i j c).
Proof.
  induction m; unfold not_in in *; unfold not_overlap in *; intros.
  simpl. apply MAJ_eWF.
  assert (i <> j).
  apply H2;lia. lia.
  assert (c <> i). apply H0. lia. lia.
  assert (c <> j). apply H1. lia. lia.
  simpl. constructor. apply (IHm n). lia. assumption. assumption.
  assumption. apply MAJ_eWF.
  assert (i + S m <> j + S m).
  apply H2. lia. lia. lia.
  apply H2. lia. lia. lia.
Qed.

Lemma MAJseq'_eWF :
  forall n i j c,
    not_in c i (n+1) -> not_in c j (n+1) -> not_overlap i j (n+1) ->
    eWF (MAJseq' n i j c).
Proof.
 intros. apply (MAJseq'_eWF' n n); try lia;assumption.
Qed.

Lemma MAJseq'_eWT' :
  forall m n i j c dim,
    m <= n ->
    not_in c i (n+1) -> not_in c j (n+1) -> not_overlap i j (n+1) ->
    max(max c (i+n)) (j+n) < dim ->
    eWT dim (MAJseq' m i j c).
Proof.
  induction m; unfold not_in in *; unfold not_overlap in *; intros.
  simpl. apply MAJ_eWT;try lia.
  assert (i <> j).
  apply H2;lia. lia.
  assert (c <> i). apply H0. lia. lia.
  assert (c <> j). apply H1. lia. lia.
  simpl. constructor. apply (IHm n);try lia; assumption.
  apply MAJ_eWT; try lia.
  assert (i + S m <> j + S m).
  apply H2; lia. lia.
  apply H2; lia.
Qed.

Lemma MAJseq'_eWT :
  forall n i j c dim,
    not_in c i (n+1) -> not_in c j (n+1) -> not_overlap i j (n+1) ->
    max(max c (i+n)) (j+n) < dim ->
    eWT dim (MAJseq' n i j c).
Proof.
  intros. apply (MAJseq'_eWT' n n); try lia; assumption.
Qed.

Lemma MAJ_efresh:
  forall a b c f,
    a <> b -> b <> c -> a <> c
    -> a <> f -> b <> f -> c <> f ->
    efresh f (MAJ c b a).
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

Lemma neq_sym {A} : forall (x y: A), x <> y -> y <> x.
Proof.
 intros. intros R.
 subst. contradiction.
Qed.

Lemma MAJseq'_efresh' :
  forall m n i j c d,
    m <= n ->
    not_in c i (n+1) -> not_in c j (n+1) -> not_overlap i j (n+1) ->
    not_in d i (n+1) -> not_in d j (n+1) -> c <> d ->
    efresh d (MAJseq' m i j c).
Proof.
  induction m; unfold not_in in *; unfold not_overlap in *; intros.
  simpl.
  apply MAJ_efresh;try lia.
  apply neq_sym.
  apply H2;lia.
  apply neq_sym. apply H0;lia.
  apply neq_sym. apply H1;lia.
  apply neq_sym. apply H4;lia.
  apply neq_sym. apply H3;lia.
  simpl.
  constructor.
  apply (IHm n); try lia; assumption.
  apply MAJ_efresh;try lia.
  apply neq_sym. apply H2;lia.
  apply H2;lia.
  apply neq_sym. apply H4;lia.
  apply neq_sym. apply H3;lia.
  apply neq_sym. apply H4;lia.
Qed.

Lemma MAJseq'_efresh :
  forall n i j c d,
    not_in c i (n+1) -> not_in c j (n+1) -> not_overlap i j (n+1) ->
    not_in d i (n+1) -> not_in d j (n+1) -> c <> d ->
    efresh d (MAJseq' n i j c).
Proof.
  intros. apply (MAJseq'_efresh' n n); try lia; assumption.
Qed.


Fixpoint UMAseq' n i j c0 : bccom :=
  match n with
  | 0 => UMA c0 i j
  | S m => UMA (j + m) (i + n) (j + n); UMAseq' m i j c0
  end.
Definition UMAseq n i j := UMAseq' (n-1) i j 0.

Lemma UMA_efresh:
  forall a b c f,
    a <> b -> b <> c -> a <> c
    -> a <> f -> b <> f -> c <> f ->
    efresh f (UMA c b a).
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

Lemma UMAseq'_efresh' :
  forall m n i j c d,
    m <= n ->
    not_in c i (n+1) -> not_in c j (n+1) -> not_overlap i j (n+1) ->
    not_in d i (n+1) -> not_in d j (n+1) -> c <> d ->
    efresh d (UMAseq' m i j c).
Proof.
  induction m; unfold not_in in *; unfold not_overlap in *; intros.
  simpl.
  apply UMA_efresh;try lia.
  apply neq_sym. apply H2;lia.
  apply neq_sym. apply H0;lia.
  apply neq_sym. apply H1;lia.
  apply neq_sym. apply H4;lia.
  apply neq_sym. apply H3;lia.
  simpl.
  constructor.
  apply UMA_efresh;try lia.
  apply neq_sym. apply H2;lia.
  apply H2; lia.
  apply neq_sym. apply H4;lia.
  apply neq_sym. apply H3;lia.
  apply neq_sym. apply H4;lia.
  apply (IHm n); try lia; assumption.
Qed.

Lemma UMAseq'_efresh :
  forall n i j c d,
    not_in c i (n+1) -> not_in c j (n+1) -> not_overlap i j (n+1) ->
    not_in d i (n+1) -> not_in d j (n+1) -> c <> d ->
    efresh d (UMAseq' n i j c).
Proof.
  intros. apply (UMAseq'_efresh' n n); try lia; assumption.
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

Lemma UMAseq'_eWF' :
  forall m n i j c,
    m <= n ->
    not_in c i (n+1) -> not_in c j (n+1) -> not_overlap i j (n+1) ->
    eWF (UMAseq' m i j c).
Proof.
  induction m; unfold not_in in *; unfold not_overlap in *; intros.
  simpl. apply UMA_eWF.
  assert (i <> j).
  apply H2;lia. lia.
  assert (c <> i). apply H0. lia. lia.
  assert (c <> j). apply H1. lia. lia.
  simpl. constructor.
  apply UMA_eWF.
  assert (i + S m <> j + S m).
  apply H2. lia. lia. lia.
  apply H2. lia. lia. lia.
  apply (IHm n). lia. assumption. assumption.
  assumption.
Qed.

Lemma UMAseq'_eWF :
  forall n i j c,
    not_in c i (n+1) -> not_in c j (n+1) -> not_overlap i j (n+1) ->
    eWF (UMAseq' n i j c).
Proof.
 intros. apply (UMAseq'_eWF' n n); try lia;assumption.
Qed.

Lemma UMAseq'_eWT' :
  forall m n i j c dim,
    m <= n ->
    not_in c i (n+1) -> not_in c j (n+1) -> not_overlap i j (n+1) ->
    max(max c (i+n)) (j+n) < dim ->
    eWT dim (UMAseq' m i j c).
Proof.
  induction m; unfold not_in in *; unfold not_overlap in *; intros.
  simpl. apply UMA_eWT;try lia.
  assert (i <> j).
  apply H2;lia. lia.
  assert (c <> i). apply H0. lia. lia.
  assert (c <> j). apply H1. lia. lia.
  simpl. constructor.
  apply UMA_eWT; try lia.
  assert (i + S m <> j + S m).
  apply H2; lia. lia.
  apply H2; lia.
  apply (IHm n);try lia; assumption.
Qed.

Lemma UMAseq'_eWT :
  forall n i j c dim,
    not_in c i (n+1) -> not_in c j (n+1) -> not_overlap i j (n+1) ->
    max(max c (i+n)) (j+n) < dim ->
    eWT dim (UMAseq' n i j c).
Proof.
  intros. apply (UMAseq'_eWT' n n); try lia; assumption.
Qed.

(*
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
*)

Definition adder01 n i j: bccom := MAJseq n i j; UMAseq n i j.

Lemma sub_1_eq : forall n, 0 < n -> (n- 1 + 1) = n.
Proof. intros. lia. Qed.

Lemma plus_1_eq : forall n, (n + 1 - 1) = n.
Proof. intros. lia. Qed.

Lemma plus_sub_eq : forall x y, (x + y - x) = y.
Proof.
 intros. lia. 
Qed.

Ltac lia_simpl := repeat (try rewrite sub_1_eq by lia; try rewrite plus_1_eq ;
            try rewrite <- minus_diag_reverse; try rewrite plus_sub_eq; 
            try rewrite plus_0_l; try rewrite plus_0_r).

Lemma adder01_eWF: forall n i j, 
     0 < n ->
     not_in 0 i n -> not_in 0 j n -> not_overlap i j n -> eWF (adder01 n i j).
Proof.
 intros. unfold adder01, MAJseq, UMAseq.
 apply eWF_seq. apply MAJseq'_eWF; lia_simpl; assumption.
 apply UMAseq'_eWF;lia_simpl;assumption.
Qed.

Lemma adder01_eWT: forall n i j dim,    
     0 < n ->
     not_in 0 i n -> not_in 0 j n -> not_overlap i j n ->
    max(max 0 (i+(n-1))) (j+(n-1)) < dim -> eWT dim (adder01 n i j).
Proof.
 intros. unfold adder01, MAJseq, UMAseq.
 constructor. apply MAJseq'_eWT; lia_simpl; assumption.
 apply UMAseq'_eWT;lia_simpl; assumption.
Qed.

Lemma adder01_efresh:
   forall n i j d,
    0 < n ->
    not_in 0 i n -> not_in 0 j n -> not_overlap i j n ->
    not_in d i n -> not_in d j n -> 0 <> d -> efresh d (adder01 n i j).
Proof.
 intros. unfold adder01, MAJseq, UMAseq.
 constructor. apply MAJseq'_efresh; lia_simpl ;assumption.
 apply UMAseq'_efresh;lia_simpl;assumption.
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

Definition fbxor f g := fun (i : nat) => f i ⊕ g i.

Definition msma i b f g := fun (x : nat) => if (x <? i) then 
        (carry b (S x) f g ⊕ (f (S x))) else (if (x =? i) then carry b (S x) f g else f x).

Definition msmb i (b : bool) f g := fun (x : nat) => if (x <=? i) then (f x ⊕ g x) else g x.

Definition msmc i b f g := fun (x : nat) => if (x <=? i) then (f x ⊕ g x) else (carry b x f g ⊕ f x ⊕ g x).

Definition sumfb b f g := fun (x : nat) => carry b x f g ⊕ f x ⊕ g x.

Ltac fb_up_simpl := repeat (try rewrite fb_up_left by lia;
                try rewrite fb_up_mid by lia; try rewrite fb_up_right by lia).
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
  forall i c f g,
    msma i c f g i ⊕ msma i c f g (S i) = msma (S i) c f g i.
Proof.
  intros. unfold msma. IfExpSimpl. easy.
Qed.

Lemma msm_neq1 :
  forall i m c f g, m <> i -> m <> S i ->
    msma (S i) c f g m = msma i c f g m.
Proof.
  intros. unfold msma. IfExpSimpl. easy. easy.
Qed.

Lemma msm_eq2 :
  forall i c f g,
    msmb i c f g (S i) ⊕ msma i c f g (S i) = msmb (S i) c f g (S i).
Proof.
  intros. unfold msma. unfold msmb. IfExpSimpl. btauto.
Qed.

Lemma msm_neq2 :
  forall i m c f g, m <> S i ->
    msmb (S i) c f g m = msmb i c f g m.
Proof.
  intros. unfold msmb. IfExpSimpl. reflexivity. reflexivity.
Qed.

Lemma msm_eq3 :
  forall i c f g,
    majb (msma i c f g (S i)) (msmb i c f g (S i)) (msma i c f g i) = msma (S i) c f g (S i).
Proof.
  intros. unfold msma. unfold msmb. IfExpSimpl.
  simpl. unfold majb. easy.
Qed.

Lemma msm_neq3:
   forall i m c f g, i <> S m -> msmc m c f g i = msmc (S m) c f g i.
Proof.
 intros. unfold msmc.
 bdestruct (i <=? m).
 bdestruct (i <=? S m).
 reflexivity. lia.
 bdestruct (i <=? S m). lia.
 reflexivity.
Qed.

Local Opaque MAJ.

Lemma update_ext {A} : forall c v1 v2 (f g : nat -> A), v1 = v2 ->
       (forall i, i <> c -> f i = g i) -> f[c |-> v1] = g[c |-> v2].
Proof.
 intros. apply functional_extensionality.
 intros. rewrite H.
 bdestruct (x =? c).
 subst. 
 rewrite update_index_eq.
 rewrite update_index_eq. reflexivity.
 rewrite update_index_neq.
 rewrite update_index_neq.
 apply H0. 1-3:lia.
Qed.

Lemma fb_up_neq : forall x i n f g, not_in x i n -> fb_up i n f g x = g x.
Proof.
 intros. unfold not_in in H.
 unfold fb_up.
 bdestruct (x <? i). reflexivity.
 bdestruct (x <? i + n).
 assert (x <> x).
 apply H. lia. contradiction.
 reflexivity.
Qed.

Lemma fb_up_eq : forall x i n f g, i <= x < i + n -> fb_up i n f g x = f (x-i).
Proof.
 intros.
 unfold fb_up.
 bdestruct (x <? i). lia.
 bdestruct (x <? i + n). reflexivity.
 lia.
Qed.

Lemma not_in_spec : forall n c j,  0 < n -> not_in c j n -> c <> j.
Proof.
  intros. unfold not_in in H. apply H0. lia.
Qed.

Lemma not_in_spec_1 : forall n m c j,  m < n -> not_in c j n -> c <> j + m.
Proof.
  intros. unfold not_in in H0. apply H0. lia.
Qed.

Lemma not_overlap_sem : forall i j n,  not_overlap i j n -> not_in i j n.
Proof.
  intros. unfold not_in,not_overlap in *.
  intros. apply H. lia. assumption.
Qed.

Lemma not_overlap_sem_1 : forall i j m n,  m < n -> not_overlap i j n -> not_in (i+m) j n.
Proof.
  intros. unfold not_in,not_overlap in *.
  intros. apply H0. lia. assumption.
Qed.

Lemma not_overlap_spec : forall n i j x y,  x < n -> y < n -> not_overlap i j n -> i + x <> j + y.
Proof.
  intros. unfold not_overlap in *.
  apply H1. lia. lia.
Qed.

Local Transparent carry.

Lemma MAJseq'_correct :
  forall m n i j c cv f g h,
    m < n ->
    not_in c i n -> not_in c j n -> not_overlap i j n ->
    bcexec (MAJseq' m i j c) ((fb_up j n f (fb_up i n g h))[c |-> cv])
                 = ((fb_up j n (msma m cv f g) (fb_up i n (msmb m cv f g) h))[c |-> (cv ⊕ (f 0))]).
(* Admitted.
(* The following proof works, but too slow. Admitted when debugging. *) *)
Proof.
  induction m; intros.
  - simpl. rewrite MAJ_correct.
    apply update_ext.
    rewrite update_index_eq.
    rewrite update_index_neq.
    fb_up_simpl. rewrite <- minus_diag_reverse. reflexivity.
    apply H1. lia.
    intros.
    unfold msma, msmb. simpl.
    bdestruct (i0 =? i).
    subst. rewrite update_index_eq.
    rewrite fb_up_neq.
    rewrite fb_up_eq.
    rewrite update_index_neq.
    rewrite fb_up_neq.
    rewrite fb_up_eq.
    rewrite update_index_neq.
    rewrite fb_up_eq.
    rewrite <- minus_diag_reverse.
    rewrite <- minus_diag_reverse.
    bdestruct (0 <=? 0). bnauto. lia.
    lia. apply (not_in_spec n); assumption.
    lia. apply not_overlap_sem; assumption.
    apply (not_in_spec n); assumption. lia.
    apply not_overlap_sem; assumption.
    intros.
    bdestruct (i0 =? j).
    subst.
    rewrite update_index_eq.
    unfold majb.
    rewrite update_index_neq.
    rewrite update_index_eq.
    rewrite update_index_neq.
    rewrite fb_up_eq.
    rewrite update_index_neq.
    rewrite fb_up_neq.
    rewrite fb_up_eq.
    rewrite fb_up_eq.
    rewrite <- minus_diag_reverse.
    rewrite <- minus_diag_reverse.
    bdestruct (0 =? 0). 
    unfold carry. reflexivity.
    lia.
    1 - 2 : lia.
    apply not_overlap_sem;assumption.
    apply (not_in_spec n); assumption.
    lia.
    apply (not_in_spec n); assumption.
    lia.
    rewrite update_index_neq.
    rewrite update_index_neq.
    rewrite update_index_neq.
    bdestruct (j <=? i0).
    bdestruct (i0 <? j + n).
    rewrite fb_up_eq. rewrite fb_up_eq.
    bdestruct (i0 - j =? 0).
    lia. reflexivity. lia. lia.
    rewrite fb_up_neq.
    rewrite (fb_up_neq i0 j).
    bdestruct (i <=? i0).
    bdestruct (i0 <? i + n).
    rewrite fb_up_eq. rewrite fb_up_eq.
    bdestruct (i0 - i <=? 0). lia. reflexivity. lia. lia.
    rewrite fb_up_neq. rewrite fb_up_neq. reflexivity.
    unfold not_in. intros. intros R. subst. lia.
    unfold not_in; intros. lia.
    rewrite fb_up_left by lia.
    rewrite fb_up_left by lia. reflexivity.
    unfold not_in; intros. lia.
    unfold not_in; intros. lia.
    rewrite fb_up_left by lia.
    rewrite (fb_up_left i0 j) by lia.
    bdestruct (i <=? i0).
    bdestruct (i0 <? i + n).
    rewrite fb_up_eq by lia. rewrite fb_up_eq by lia.
    bdestruct (i0 - i <=? 0). lia. reflexivity.
    rewrite fb_up_right by lia.
    rewrite fb_up_right by lia.
    reflexivity.
    rewrite fb_up_left by lia.
    rewrite fb_up_left by lia. reflexivity.
    1 - 3 : lia.
    unfold not_overlap in H2.
    apply neq_sym. apply H2; lia.
    unfold not_in in H0. apply neq_sym. apply H0;lia.
    unfold not_in in H1. apply neq_sym. apply H1;lia.
  - simpl. rewrite IHm. rewrite MAJ_correct. simpl.
    rewrite (update_twice_neq (fb_up j n (msma m cv f g)
      (fb_up i n (msmb m cv f g) h))).
    rewrite (update_twice_neq ((fb_up j n (msma m cv f g)
      (fb_up i n (msmb m cv f g) h))
   [j + S m
   |-> majb
         (((fb_up j n (msma m cv f g)
              (fb_up i n (msmb m cv f g) h))
           [c |-> cv ⊕ f 0]) 
            (j + S m))
         (((fb_up j n (msma m cv f g)
              (fb_up i n (msmb m cv f g) h))
           [c |-> cv ⊕ f 0]) 
            (i + S m))
         (((fb_up j n (msma m cv f g)
              (fb_up i n (msmb m cv f g) h))
           [c |-> cv ⊕ f 0]) 
            (j + m))])).
    rewrite (update_twice_neq (((fb_up j n (msma m cv f g)
      (fb_up i n (msmb m cv f g) h))
   [j + S m
   |-> majb
         (((fb_up j n (msma m cv f g)
              (fb_up i n (msmb m cv f g) h))
           [c |-> cv ⊕ f 0]) 
            (j + S m))
         (((fb_up j n (msma m cv f g)
              (fb_up i n (msmb m cv f g) h))
           [c |-> cv ⊕ f 0]) 
            (i + S m))
         (((fb_up j n (msma m cv f g)
              (fb_up i n (msmb m cv f g) h))
           [c |-> cv ⊕ f 0]) 
            (j + m))]) [i + S m
  |-> ((fb_up j n (msma m cv f g)
          (fb_up i n (msmb m cv f g) h)) [c
       |-> cv ⊕ f 0]) (i + S m)
      ⊕ ((fb_up j n (msma m cv f g)
            (fb_up i n (msmb m cv f g) h))
         [c |-> cv ⊕ f 0]) (j + S m)])).
    apply update_ext. reflexivity. intros.
    bdestruct (i0 =? j + m).
    subst.
    rewrite update_index_eq.
    rewrite fb_up_mid by lia.
    lia_simpl.
    rewrite <- msm_eq1.
    rewrite update_index_neq by lia.
    rewrite update_index_neq.
    rewrite fb_up_mid by lia.
    rewrite fb_up_mid by lia.
    lia_simpl. reflexivity.
    unfold not_in in H1. apply H1. lia.
    rewrite update_index_neq by lia.
    bdestruct (i0 =? i + S m). subst.
    rewrite update_index_eq.
    rewrite update_index_neq by lia.
    rewrite update_index_neq.
    rewrite fb_up_neq.
    rewrite fb_up_mid by lia.
    rewrite fb_up_mid by lia.
    rewrite fb_up_neq.
    rewrite fb_up_mid by lia.
    lia_simpl.
    rewrite <- msm_eq2. reflexivity.
    apply not_overlap_sem_1 ; try lia; assumption.
    apply not_overlap_sem_1 ; try lia; assumption.
    apply (not_in_spec_1 n). lia. assumption.
    rewrite update_index_neq by lia.
    bdestruct (i0 =? j + S m).
    subst.
    rewrite update_index_eq.
    rewrite update_index_neq by lia.
    rewrite update_index_neq.
    rewrite update_index_neq.
    rewrite fb_up_mid by lia.
    rewrite fb_up_neq.
    rewrite fb_up_mid by lia.
    rewrite fb_up_mid by lia.
    lia_simpl.
    rewrite msm_eq3.
    rewrite fb_up_mid by lia.
    lia_simpl. reflexivity.
    apply (not_overlap_sem_1). lia. assumption.
    apply (not_in_spec_1 n). lia. assumption.
    apply (not_in_spec_1 n). lia. assumption.
    rewrite update_index_neq.
    bdestruct (i0 <? j).
    rewrite fb_up_left by lia.
    rewrite (fb_up_left i0 j) by lia.
    bdestruct (i0 <? i).
    rewrite fb_up_left by lia.
    rewrite fb_up_left by lia. reflexivity.
    bdestruct (i0 <? i + n).
    rewrite fb_up_mid by lia.
    rewrite fb_up_mid by lia.
    rewrite msm_neq2 by lia. reflexivity.
    rewrite fb_up_right by lia.
    rewrite fb_up_right by lia. reflexivity.
    bdestruct (i0 <? j + n).
    rewrite fb_up_mid by lia.
    rewrite fb_up_mid by lia.
    rewrite msm_neq1 by lia. reflexivity.
    rewrite fb_up_right by lia.
    rewrite (fb_up_right i0 j) by lia.
    bdestruct (i0 <? i).
    rewrite fb_up_left by lia.
    rewrite fb_up_left by lia. reflexivity.
    bdestruct (i0 <? i + n).
    rewrite fb_up_mid by lia.
    rewrite fb_up_mid by lia.
    rewrite msm_neq2 by lia. reflexivity.
    rewrite fb_up_right by lia.
    rewrite fb_up_right by lia. reflexivity.
    lia.
    apply (not_in_spec_1 n). lia. assumption.
    apply (not_in_spec_1 n). lia. assumption.
    apply (not_in_spec_1 n). lia. assumption.
    apply neq_sym.
    apply (not_overlap_spec n). lia. lia. assumption.
    apply (not_overlap_spec n). lia. lia. assumption.
    lia. lia. assumption. assumption. assumption.
Qed.

Local Opaque UMA.

Lemma UMAseq'_correct :
  forall m n i j c cv f g h,
    m < n ->
    not_in c i n -> not_in c j n -> not_overlap i j n ->
    bcexec (UMAseq' m i j c) ((fb_up j n (msma m cv f g) (fb_up i n (msmc m cv f g) h))[c |-> cv ⊕ (f 0)])
         = ((fb_up j n f (fb_up i n (sumfb cv f g) h))[c |-> cv]).
(* Admitted.
(* The following proof works, but too slow. Admitted when debugging. *) *)
Proof.
  induction m; intros.
  - simpl.
    rewrite UMA_correct_partial with (fa := f 0) (fb := g 0) (fc := carry cv 0 f g).
    unfold carry.
    apply update_ext. reflexivity. intros.
    bdestruct (i0 =? i). subst.
    rewrite update_index_eq.
    rewrite fb_up_neq.
    rewrite fb_up_mid by lia.
    lia_simpl.
    unfold sumfb,carry. btauto.
    apply not_overlap_sem. assumption.
    rewrite update_index_neq by lia.
    bdestruct (i0 =? j). subst.
    rewrite update_index_eq.
    rewrite fb_up_mid by lia.
    lia_simpl. reflexivity.
    rewrite update_index_neq by lia.
    rewrite update_index_neq by lia.
    bdestruct (i0 <? j).
    rewrite fb_up_left by lia.
    rewrite (fb_up_left i0 j) by lia.
    bdestruct (i0 <? i).
    rewrite fb_up_left by lia.
    rewrite fb_up_left by lia. reflexivity.
    bdestruct (i0 <? i + n).
    rewrite fb_up_mid by lia.
    rewrite fb_up_mid by lia.
    unfold msmc, sumfb.
    bdestruct (i0 - i <=? 0). lia. reflexivity.
    rewrite fb_up_right by lia.
    rewrite fb_up_right by lia. reflexivity.
    bdestruct (i0 <? j + n).
    rewrite fb_up_mid by lia.
    rewrite fb_up_mid by lia.
    unfold msma.
    bdestruct (i0 - j <? 0). lia.
    bdestruct (i0 - j =? 0). lia.
    reflexivity.
    rewrite fb_up_right by lia.
    rewrite (fb_up_right i0 j) by lia.
    bdestruct (i0 <? i).
    rewrite fb_up_left by lia.
    rewrite fb_up_left by lia. reflexivity.
    bdestruct (i0 <? i + n).
    rewrite fb_up_mid by lia.
    rewrite fb_up_mid by lia.
    unfold msmc, sumfb.
    bdestruct (i0 - i <=? 0). lia. reflexivity.
    rewrite fb_up_right by lia.
    rewrite fb_up_right by lia. reflexivity.
    apply neq_sym. apply H2; lia.
    apply neq_sym. apply H0;lia.
    apply neq_sym. apply H1;lia.
    rewrite update_index_neq.
    rewrite fb_up_eq by lia.
    unfold majb, msma.
    bdestruct (j - j <? 0). lia.
    bdestruct (j - j =? 0). 
    lia_simpl. unfold carry. reflexivity.
    lia.
    apply H1;lia.
    rewrite update_index_neq.
    rewrite fb_up_neq.
    rewrite fb_up_eq by lia.
    unfold msmc.
    bdestruct (i - i <=? 0). lia_simpl. btauto.
    lia.
    apply not_overlap_sem. assumption.
    apply H0;lia.
    rewrite update_index_eq.
    unfold carry. reflexivity.
  - simpl.
    replace (bcexec (UMA (j + m) (i + S m) (j + S m))
     ((fb_up j n (msma (S m) cv f g)(fb_up i n (msmc (S m) cv f g) h)) [c |-> cv ⊕ f 0]))
           with ((fb_up j n (msma m cv f g)(fb_up i n (msmc m cv f g) h)) [c |-> cv ⊕ f 0]).
    rewrite IHm. easy. lia. 1 - 3: assumption.
    rewrite UMA_correct_partial with (fa := f (S m)) (fb := g (S m)) (fc := carry cv (S m) f g).
    rewrite (update_twice_neq (fb_up j n (msma (S m) cv f g)
      (fb_up i n (msmc (S m) cv f g) h))).
    rewrite (update_twice_neq ((fb_up j n (msma (S m) cv f g)
      (fb_up i n (msmc (S m) cv f g) h))
        [j + S m |-> f (S m)])).
    rewrite (update_twice_neq (((fb_up j n (msma (S m) cv f g)
      (fb_up i n (msmc (S m) cv f g) h))
        [j + S m |-> f (S m)]) [i + S m |-> (f (S m) ⊕ g (S m)) ⊕ carry cv (S m) f g])).
    apply update_ext. reflexivity. intros.
    bdestruct (i0 =? j + m). subst.
    rewrite update_index_eq.
    rewrite fb_up_eq. lia_simpl.
    unfold msma. 
    bdestruct (m <? m). lia.
    bdestruct (m =? m). reflexivity. lia.
    lia.
    rewrite update_index_neq by lia.
    bdestruct (i0 =? i + S m). subst.
    rewrite update_index_eq.
    rewrite fb_up_neq.
    rewrite fb_up_mid by lia. lia_simpl.
    unfold msmc.
    bdestruct (S m <=? m). lia.
    btauto.
    apply (not_overlap_sem_1). lia. assumption.
    rewrite update_index_neq by lia.
    bdestruct (i0 =? j + S m). subst.
    rewrite update_index_eq.
    rewrite fb_up_mid by lia.
    lia_simpl.
    unfold msma.
    bdestruct (S m <? m). lia.
    bdestruct (S m =? m). lia. reflexivity.
    rewrite update_index_neq by lia.
    bdestruct (i0 <? j).
    rewrite fb_up_left by lia.
    rewrite (fb_up_left i0 j) by lia.
    bdestruct (i0 <? i).
    rewrite fb_up_left by lia.
    rewrite fb_up_left by lia. reflexivity.
    bdestruct (i0 <? i + n).
    rewrite fb_up_mid by lia.
    rewrite fb_up_mid by lia.
    rewrite msm_neq3 by lia.
    reflexivity.
    rewrite fb_up_right by lia.
    rewrite fb_up_right by lia. reflexivity.   
    bdestruct (i0 <? j + n).
    rewrite fb_up_mid by lia.
    rewrite (fb_up_mid i0 j) by lia.
    rewrite msm_neq1 by lia. reflexivity.
    rewrite fb_up_right by lia.
    rewrite (fb_up_right i0 j) by lia.   
    bdestruct (i0 <? i).
    rewrite fb_up_left by lia.
    rewrite fb_up_left by lia. reflexivity.
    bdestruct (i0 <? i + n).
    rewrite fb_up_mid by lia.
    rewrite fb_up_mid by lia.
    rewrite msm_neq3 by lia.
    reflexivity.
    rewrite fb_up_right by lia.
    rewrite fb_up_right by lia. reflexivity.
    apply (not_in_spec_1 n). lia. assumption.   
    apply (not_in_spec_1 n). lia. assumption.   
    apply (not_in_spec_1 n). lia. assumption.   
    apply neq_sym. apply (not_overlap_spec n); try lia; assumption.
    apply (not_overlap_spec n); try lia; assumption.
    lia.
    rewrite update_index_neq.
    rewrite fb_up_eq by lia.
    lia_simpl.
    unfold majb,msma.
    bdestruct (S m <? S m). lia.
    bdestruct (S m =? S m).
    simpl. btauto. lia.
    apply (not_in_spec_1 n); try lia; assumption.
    rewrite update_index_neq.
    rewrite fb_up_neq.
    rewrite fb_up_mid by lia.
    lia_simpl.
    unfold msmc.
    bdestruct (S m <=? S m). btauto. lia.
    apply (not_overlap_sem_1). lia. assumption.
    apply (not_in_spec_1 n). lia. assumption.
    rewrite update_index_neq.
    rewrite fb_up_eq.
    lia_simpl.
    unfold msma.
    bdestruct (m <? S m).  reflexivity.
    lia. lia.
    apply (not_in_spec_1 n). lia. assumption.
Qed.

Lemma adder01_correct_fb :
  forall n i j cv f g h,
    0 < n ->
    not_in 0 i n -> not_in 0 j n -> not_overlap i j n ->
    bcexec (adder01 n i j) ((fb_up j n f (fb_up i n g h))[0 |-> cv]) = ((fb_up j n f (fb_up i n (sumfb cv f g) h))[0 |-> cv]).
Proof.
  intros. unfold adder01. simpl. unfold MAJseq, UMAseq. rewrite MAJseq'_correct; try lia; try assumption.
  replace (fb_up i n (msmb (n - 1) cv f g) h) with (fb_up i n (msmc (n - 1) cv f g) h).
  2:{ apply functional_extensionality. intros.
      bdestruct (x <? i). fb_up_simpl. reflexivity.
      bdestruct (x <? i + n). fb_up_simpl. unfold msmc,msmb. IfExpSimpl. easy.
      fb_up_simpl. reflexivity.
  }
  apply UMAseq'_correct; try lia; try assumption.
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
  forall n i x f,
    reg_push x i n f = reg_push (x mod 2^n) i n f.
Proof.
  intros. unfold reg_push. unfold nat2fb.
  apply functional_extensionality. intros j.
  bdestruct (j <? i). fb_up_simpl. reflexivity.
  bdestruct (j <? i+n). fb_up_simpl. rewrite Nofnat_mod. 2: apply Nat.pow_nonzero; lia.
  rewrite Nofnat_pow. simpl.
  do 2 rewrite N2fb_Ntestbit. rewrite N.mod_pow2_bits_low. easy. lia.
  fb_up_simpl. easy.
Qed.

(* The following two lemmas show the correctness of the adder implementation based on MAJ;UMA circuit. 
   The usage of the adder is based on the carry0 lemma. *)
Lemma adder01_correct_carry0 :
  forall n i j x y f,
    0 < n ->
    not_in 0 i n -> not_in 0 j n -> not_overlap i j n ->
    bcexec (adder01 n i j) ((reg_push x j n (reg_push y i n f))[0 |-> false])
        = ((reg_push x j n (reg_push (x+y) i n f))[0 |-> false]).
Proof.
  intros. unfold reg_push. rewrite adder01_correct_fb by easy. rewrite sumfb_correct_carry0. easy.
Qed.

Lemma adder01_correct_carry1 :
  forall n i j x y f,
    0 < n ->
    not_in 0 i n -> not_in 0 j n -> not_overlap i j n ->
    bcexec (adder01 n i j) ((reg_push x j n (reg_push y i n f))[0 |-> true])
        = ((reg_push x j n (reg_push (x+y+1) i n f))[0 |-> true]).
Proof.
  intros. unfold reg_push. rewrite adder01_correct_fb by easy. rewrite sumfb_correct_carry1. easy.
Qed.

Opaque adder01.


(* The implementation of a new constant adder. *)
Definition single_carry (i:nat) (c:nat) (M:nat -> bool) := if M 0 then bccnot i c else bcskip.

(* for anything that is ge 2. *)
Fixpoint half_carry (n:nat) (i:nat) (j:nat) (M : nat -> bool) := 
    match n with 0 => (if M 1 then bccnot (i+1) j ; bcx j else bcskip) ; (if M 0 then bcccnot i (i+1) j else bccnot (i+1) j)
              | S m => (if M (n+1) then bccnot (i+(n+1)) (j+n) ; bcx (j+n) else bcskip); bcccnot (j+m) (i+(n+1)) (j+n);
                               half_carry m i j M; bcccnot (j+m) (i+(n+1)) (j+n)
    end.

Definition half_carry_result (m:nat) (b:bool) (f g : nat -> bool) (M:nat -> bool) :=
             fun x => if (x <=? m) then (b ⊕ (f x ⊕ (carry b (x+2) g M))) else g x.

Lemma half_carry_sem : forall m n i j b f g h M, m < n -> 1 < n -> 
       not_overlap i j n ->
       bcexec (half_carry m i j M) (fb_up j n f (fb_up i n g h))
       = (fb_up j n (half_carry_result m b f g M) (fb_up i n g h)).
Proof.
  intros.
  induction m;simpl.
  destruct (M 0) eqn:eq1.
  destruct (M 1) eqn:eq2.
  rewrite bcseq_correct.
  replace (bcexec (bccnot (i + 1) j) (fb_up j n f (fb_up i n g h))) with 
          ((fb_up j n f (fb_up i n g h))[j |-> f 0 ⊕ g 1]).
 2:{
  rewrite bccnot_correct.
  apply update_ext.
  rewrite fb_up_mid by lia.
  rewrite fb_up_neq.
  rewrite fb_up_mid by lia.
  lia_simpl. reflexivity.
  unfold not_in. intros. apply H1. lia. lia.
  intros. reflexivity.
  apply H1. lia. lia.
  }
  replace (bcexec (bcx j)
     ((fb_up j n f (fb_up i n g h)) [j |-> f 0 ⊕ g 1]))
    with ((fb_up j n f (fb_up i n g h))[j |-> ¬ (f 0 ⊕ g 1)]).
  2:{
     simpl.
     rewrite (update_twice_eq).
     apply update_ext.
     rewrite update_index_eq. reflexivity.
     intros. reflexivity.
  }
  replace (bcexec (bcccnot i (i + 1) j)
  ((fb_up j n f (fb_up i n g h)) [j |-> ¬ (f 0 ⊕ g 1)]))
          with ((fb_up j n f (fb_up i n g h)) [j |-> (¬ (f 0 ⊕ g 1)) ⊕ (g 1 && g 0)]).
 2:{
   rewrite bcccnot_correct;try lia.
   rewrite update_twice_eq.
   apply update_ext.
   rewrite update_index_eq.
   rewrite update_index_neq.
   rewrite update_index_neq.
   rewrite fb_up_neq.
   rewrite fb_up_mid by lia.
   rewrite fb_up_neq.
   rewrite fb_up_mid by lia.
   lia_simpl. reflexivity.
   apply (not_overlap_sem). assumption.
   apply (not_overlap_sem_1). lia. assumption.
   apply neq_sym. apply H1. lia. lia.
   apply neq_sym. apply H1. lia. lia.
   intros. reflexivity.
   apply H1. lia. lia.
   apply H1. lia. lia.
  }
  unfold half_carry_result.
  apply functional_extensionality. intros.
  lia_simpl. rewrite update_index_eq.
  btauto.
  IfExpSimpl.
Qed.

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
  | S m => UMA (i + m) (j + n) (i + n); UMAseq' m i j c0
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

