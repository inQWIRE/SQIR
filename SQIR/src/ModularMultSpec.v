Require Import VectorStates UnitaryOps Coq.btauto.Btauto.
(* The following belows to the ModularMult specification file, which 
      contains the conceptual properties about the ModularMult circuit that produces the result of C*x % M. *)

(* Here, we push the proof of the addition of two binary numbers is equal 
    to the addition of two decimal numbers, if the binary numbers and decimal numbers
     are the same under different representations. 
   We use the positive library to help us finish the job. 
   We built a special representation for the proof. 
   Need to connect the proof with our own representations. *)
Local Open Scope nat_scope.

Lemma mod_sum_lt :
  forall x y M,
    0 < x < M ->
    0 < y < M ->
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


Definition majb a b c := (a && b) ⊕ (b && c) ⊕ (a && c).

Fixpoint carry_spec b n f g :=
  match n with
  | 0 => b
  | S n' => let c := carry_spec b n' f g in
           let a := f n' in
           let b := g n' in
           (a && b) ⊕ (b && c) ⊕ (a && c)
  end.

Lemma carry_spec_sym :
  forall b n f g,
    carry_spec b n f g = carry_spec b n g f.
Proof.
  intros. induction n. reflexivity.
  simpl. rewrite IHn. btauto.
Qed.

Definition funbool_push b f : nat -> bool :=
  fun x => match x with
        | O => b
        | S n => f n
        end.

Definition allfalse := fun (_ : nat) => false.

Lemma carry_spec_false_0_l: forall n f, 
    carry_spec false n allfalse f = false.
Proof.
unfold allfalse.
induction n.
simpl.
reflexivity.
intros. simpl.
rewrite IHn. rewrite andb_false_r.
reflexivity.
Qed.

Lemma carry_spec_false_0_r: forall n f, 
    carry_spec false n f allfalse = false.
Proof.
unfold allfalse.
induction n.
simpl.
reflexivity.
intros. simpl.
rewrite IHn. rewrite andb_false_r.
reflexivity.
Qed.

Lemma carry_spec_fbpush :
  forall n a ax ay fx fy,
    carry_spec a (S n) (funbool_push ax fx) (funbool_push ay fy) = carry_spec (majb a ax ay) n fx fy.
Proof.
  induction n; intros.
  simpl. unfold majb. btauto.
  remember (S n) as Sn. simpl. rewrite IHn. unfold funbool_push. subst.
  simpl. easy.
Qed.

Fixpoint pos2fb p : nat -> bool :=
  match p with
  | xH => funbool_push true allfalse
  | xI p' => funbool_push true (pos2fb p')
  | xO p' => funbool_push false (pos2fb p')
  end.

Compute (pos2fb (xO (xI xH))).

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

Lemma carry_spec_succ :
  forall m p,
    carry_spec true m (pos2fb p) allfalse = pos2fb (Pos.succ p) m ⊕ (pos2fb p) m.
Proof.
  induction m; intros. simpl. destruct p; reflexivity.
  replace allfalse with (funbool_push false allfalse).
  2:{ unfold funbool_push, allfalse. apply functional_extensionality. intros. destruct x; reflexivity.
  }
  Local Opaque funbool_push carry_spec.
  destruct p; simpl.
  rewrite carry_spec_fbpush; unfold majb; simpl. rewrite IHm. reflexivity.
  rewrite carry_spec_fbpush; unfold majb; simpl. rewrite carry_spec_false_0_r. Local Transparent funbool_push. simpl. btauto.
  rewrite carry_spec_fbpush; unfold majb; simpl. Local Transparent carry_spec. destruct m; reflexivity.
Qed.

Lemma carry_spec_succ' :
  forall m p,
    carry_spec true m allfalse (pos2fb p) = pos2fb (Pos.succ p) m ⊕ (pos2fb p) m.
Proof.
  intros. rewrite carry_spec_sym. apply carry_spec_succ.
Qed.

Lemma carry_spec_succ0 :
  forall m, carry_spec true m allfalse allfalse = pos2fb xH m.
Proof.
  induction m. easy. 
  replace allfalse with (funbool_push false allfalse).
  2:{ unfold funbool_push, allfalse. apply functional_extensionality. intros. destruct x; reflexivity.
  }
  rewrite carry_spec_fbpush. unfold majb. simpl. rewrite carry_spec_false_0_l. easy.
Qed.

Lemma carry_add_pos_eq :
  forall m b p q,
    carry_spec b m (pos2fb p) (pos2fb q) ⊕ (pos2fb p) m ⊕ (pos2fb q) m = pos2fb (add_c b p q) m.
Proof.
  induction m; intros. simpl. destruct p, q, b; reflexivity.
  Local Opaque carry_spec.
  destruct p, q, b; simpl; rewrite carry_spec_fbpush; 
                  try (rewrite IHm; reflexivity); try (unfold majb; simpl; 
                      try rewrite carry_spec_succ; try rewrite carry_spec_succ'; 
                  try rewrite carry_spec_succ0; try rewrite carry_spec_false_0_l;
                   try rewrite carry_spec_false_0_r;
                  unfold allfalse; try btauto; try (destruct m; reflexivity)).
Qed.

Lemma carry_add_eq :
  forall m x y,
    carry_spec false m (N2fb x) (N2fb y) ⊕ (N2fb x) m ⊕ (N2fb y) m = (N2fb (x + y)) m.
Proof.
  intros.
  destruct x as [|p]; destruct y as [|q]; simpl; unfold allfalse.
  rewrite carry_spec_false_0_l. easy.
  rewrite carry_spec_false_0_l. btauto.
  rewrite carry_spec_false_0_r. btauto.
  apply carry_add_pos_eq.
Qed.

(* implementation of fb2N, *)
Definition push_0 x := match x with 0%N => 0%N
                                  | Npos p => Npos (xO p)
                       end.

Definition push_1 x := match x with 0%N => Npos xH
                                  | Npos p => Npos (xI p)
                       end.

Fixpoint fb2N' (n:nat) (f:nat -> bool) (acc: N) : N :=
    match n with 0 => acc
               | S n' => fb2N' n' f (if (f n') then push_1 acc else push_0 acc)
    end.
Definition fb2N n f := fb2N' n f (0%N).

Lemma fb2N'_eq : forall n f f' b,
  (forall x, x < n -> f x = f' x)%nat ->
  fb2N' n f b = fb2N' n f' b.
Proof.
  intros.
  generalize dependent b.
  induction n.
  simpl.
  reflexivity.
  intros.
  simpl.
  assert (f n = f' n).
  apply H. lia.
  destruct (f n) eqn:eq.
  rewrite <- H0.
  rewrite IHn.
  reflexivity.
  intros. 
  apply H.
  lia.
  rewrite <- H0.
  rewrite IHn.
  reflexivity.
  intros. 
  apply H.
  lia.
Qed.

Lemma fb2N_eq : forall n f f',
  (forall x, x < n -> f x = f' x)%nat ->
  fb2N n f = fb2N n f'.
Proof.
intros. unfold fb2N. 
apply fb2N'_eq.
apply H.
Qed.

Definition nat2fb x := N2fb (N.of_nat x).

Lemma nat_N_id : forall n, nat_of_N (N_of_nat n) = n.
Proof. intros. lia.
Qed.


Lemma nat_pow_ind_eq: forall p , Pos.to_nat (Pos.iter (Pos.mul 2) 1%positive p) = 2%nat ^ (Pos.to_nat p).
Proof.
intros.
induction p.
Admitted.

Lemma nat_pow_2_eq: forall (n:N), N.to_nat((2 ^ n)%N) = (N.to_nat 2) ^ (N.to_nat n).
Proof.
intros. unfold N.pow.
destruct n eqn:eq.
rewrite Nat.pow_0_r.
lia.
assert (N.to_nat (N.pos (2 ^ p)) = Pos.to_nat (2 ^ p)) by lia.
rewrite H.
unfold Pos.pow.
rewrite nat_pow_ind_eq.
assert (N.to_nat (2%N) = 2%nat) by lia.
rewrite H0.
assert (N.to_nat (N.pos p) = Pos.to_nat p) by lia.
rewrite H1. reflexivity.
Qed.

Lemma size_nat_size_same : 
   forall n, (N.to_nat (N.size n)) = (N.size_nat n).
Proof.
intros.
destruct n.
simpl. reflexivity.
simpl.
induction p.
simpl.
rewrite <- IHp. lia.
simpl.
rewrite <- IHp. lia.
simpl. lia.
Qed.

Lemma size_gt_nat : forall (n:nat), (n < (2 ^ (N.size_nat (N.of_nat (n%nat))))).
Proof.
intros.
specialize (N.size_gt (N.of_nat n)) as eq.
assert ((N.to_nat (N.of_nat n)) < N.to_nat ((2 ^ N.size (N.of_nat n))%N))%nat.
lia.
rewrite nat_N_id in H.
assert (N.to_nat (2 ^ N.size (N.of_nat n))%N = (N.to_nat 2%N) ^ (N.to_nat (N.size (N.of_nat n))%N))%nat.
rewrite nat_pow_2_eq.
reflexivity.
rewrite H0 in H.
assert (N.to_nat 2 = 2) by lia.
rewrite H1 in H.
rewrite size_nat_size_same in H.
apply H.
Qed.

Lemma pos_size_up_1 : forall (p : positive), 
           Pos.succ (Pos.size p) = Pos.size (xO p).
Proof.
induction p; simpl; reflexivity.
Qed.

Lemma pos_size_s_eq :forall (n:positive), Pos.size(Pos.succ n) 
         = Pos.size n \/ Pos.size (Pos.succ n) = (Pos.size n + 1)%positive.
Proof.
intros.
induction n.
simpl.
destruct IHn.
left.
rewrite <- H. reflexivity.
right.
rewrite H.
lia.
simpl.
destruct IHn.
left. lia.
left. lia.
simpl. right.
reflexivity.
Qed.

Lemma size_s_eq : forall (n:N), N.size (N.succ n) = N.size n \/ N.size (N.succ n) = (N.size n + 1)%N.
Proof.
intros.
unfold N.size.
unfold N.succ.
destruct n.
simpl. right.
reflexivity.
specialize (pos_size_s_eq p) as H.
destruct H.
left.
rewrite H. reflexivity.
right.
rewrite H. reflexivity.
Qed.

Lemma size_lt_eq : forall (n:N), (N.size (N.succ (N.succ n)) = N.size n + 1)%N.
Proof.
intros.
Admitted.

Lemma size_le_nat : forall (n:nat),0 < n -> ((2 ^ ((N.size_nat (N.of_nat (n%nat))) - 1)) <= n).
Proof.
intros.
assert (2^(N.size(N.of_nat n) - 1) <= (N.of_nat n))%N.
specialize (N.size_le ((N.of_nat n))) as H1.
rewrite N.succ_double_spec in H1.
destruct n.
lia.
destruct n.
simpl. lia.
assert ((2 ^ (N.size (N.of_nat (S (S n))) - 1) = (2 ^ (N.size (N.of_nat n))))%N).
assert ((N.of_nat (S (S n))) = N.succ (N.succ (N.of_nat n)))%N by lia.
rewrite H0.
rewrite size_lt_eq.
assert ((N.size (N.of_nat n) + 1 - 1) = N.size (N.of_nat n))%N by lia.
rewrite H2. reflexivity.
rewrite H0.
assert (2 * 2 ^ N.size (N.of_nat n) = 2 ^ N.size (N.of_nat (S (S n))))%N.
assert ((N.of_nat (S (S n))) = (N.succ (N.succ (N.of_nat n)))) by lia.
rewrite H2.
rewrite size_lt_eq.
assert ((N.size (N.of_nat n) + 1) = N.succ (N.size (N.of_nat n)))%N by lia.
rewrite H3.
rewrite N.pow_succ_r.
reflexivity.
lia. 
rewrite <- H2 in H1.
Admitted.

Lemma size_low_bound : forall (x n:nat), x < 2 ^ n -> (N.size_nat (N.of_nat (x%nat))) <= n.
Proof.
intros.
destruct x.
unfold N.size_nat. simpl.
lia.
specialize (size_le_nat (S x)) as H1.
assert (0 < S x) by lia.
apply H1 in H0.
assert (2 ^ (N.size_nat (N.of_nat (S x)) - 1) < 2 ^ n) by lia.
apply Nat.pow_lt_mono_r_iff in H2.
lia.
lia.
Qed.


Lemma pos2fb_bound : forall n p m , (Pos.to_nat p) < 2 ^ n -> n <= m -> pos2fb p m = false.
Proof.
intros n p.
induction p.
intros. simpl.
Admitted.

Lemma N2fb_bound :
    forall n x m, x < 2 ^ n -> n <= m -> (nat2fb x) m = false.
Proof.
 intros.
 unfold nat2fb.
 unfold N2fb.
 destruct (N.of_nat x) eqn:eq.
 unfold allfalse. reflexivity.
Admitted.

Definition fb2nat n f := N.to_nat (fb2N n f).


Definition bool_shift (f : nat -> bool) := fun i => if i =? 0 then false else f (i-1).

Lemma bool_shift_0 : forall f, (bool_shift f) 0 = false.
Proof.
  intros. unfold bool_shift.
  easy.
Qed.

Lemma fb2nat_shift_true_aux:
  forall n f m,
      N.to_nat (fb2N' (S n) (bool_shift f) m) + 2 ^ S n * Nat.b2n (f (S n - 1)) = 2 * N.to_nat (fb2N' (S n) f m).
Proof.
 intros n f.
 induction n.
 intros m.
 simpl.
 destruct (f 0).
 unfold push_0, push_1.
 destruct m.
 simpl. reflexivity.
Admitted.


Lemma fb2nat_shift_true : 
   forall n f, 0 < n -> fb2nat n (bool_shift f) + (2^n * (Nat.b2n (f (n-1))))
                = 2 * fb2nat n f.
Proof.
intros.
 unfold fb2nat, fb2N.
 destruct n.
 lia.
 rewrite fb2nat_shift_true_aux.
 reflexivity.
Qed.


Lemma fb2nat_shift_2 :
    forall n f, 0 < n -> f (n - 1) = false ->
        fb2nat n (bool_shift f)
                = 2 * fb2nat n f.
Proof.
intros.
rewrite <- fb2nat_shift_true.
rewrite H0.
assert (Nat.b2n false = 0) by easy.
rewrite H1. lia.
assumption.
Qed.


Lemma fb2nat_0 : forall n, fb2N' n allfalse 0 = 0%N.
Proof.
intros.
induction n.
simpl. reflexivity.
simpl. apply IHn.
Qed.


Lemma nat2fb_inverse : forall n x, 
  (x < 2 ^ n)%nat -> fb2nat n (nat2fb x) = x.
Proof.
  intros.
  unfold fb2nat, nat2fb, fb2N, N2fb.
  destruct (N.of_nat x) eqn:eq.
  assert (x = 0) by lia.
  rewrite H0.
  rewrite fb2nat_0. lia.
Admitted.


(* proofs of specs on double x in the boolean function. *)

Definition times_two_spec (f:nat -> bool) := bool_shift f.

(* Showing the times_two spec is correct. *)

Lemma nat2fb_high:
     forall n x, 0 < n -> x < 2^(n-1) -> (nat2fb x) (n-1) = false.
Proof.
intros.
unfold nat2fb.
Admitted.

Lemma times_two_correct:
   forall n x, 0 < n -> x < 2^(n-1)
         -> fb2nat n (times_two_spec (nat2fb x)) = 2 * x.
Proof.
intros.
unfold times_two_spec.
specialize (fb2nat_shift_2 n (nat2fb x) H) as H2.
specialize (nat2fb_high n x H H0) as H3.
apply H2 in H3.
rewrite H3.
rewrite nat2fb_inverse.
reflexivity.
assert (x < 2^n).
assert (n = S (n-1)) by lia.
rewrite H1.
rewrite Nat.pow_succ_r.
lia.
lia.
assumption.
Qed.


(* Showing the adder spec is correct. *)
    
Definition add_bit f g := fun i => (carry_spec false i f g)  ⊕ f i ⊕ g i.


Definition adder_spec (f g : nat -> bool) := add_bit f g.

Lemma adder_spec_correct_aux :
   forall n m x y, m <= n ->
      fb2nat m (adder_spec (nat2fb x) (nat2fb y))
              = fb2nat m (nat2fb (x + y)).
Proof.
intros.
unfold fb2nat,fb2N,nat2fb,adder_spec,add_bit.
induction m.
simpl.
reflexivity.
simpl.
Admitted.

Lemma adder_spec_correct:
  forall n x y, 0 < n -> x < 2 ^(n - 1) -> y < 2 ^ (n - 1)
   -> fb2nat n (adder_spec (nat2fb x) (nat2fb y))
          = x + y.
Proof.
intros.
specialize (adder_spec_correct_aux n n x y) as H2.
rewrite H2.
rewrite nat2fb_inverse.
reflexivity.
assert (n = S (n - 1)) by lia.
rewrite H3.
rewrite Nat.pow_succ_r.
lia. lia. lia.
Qed.

(* Here we show that the spec of comparator is correct. *)
Definition com_spec (f : nat -> bool) := fun i => negb (f i).

Definition compare_spec (f g: nat -> bool) := com_spec (add_bit (com_spec f) g).

Lemma compare_spec_correct_lt:
   forall n x y, 0 < n -> x < 2 ^ n -> y < 2 ^ n ->
         if bool_dec ((compare_spec (nat2fb x) (nat2fb y)) n) true then x < y else y <= x.
Proof.
intros.
Admitted.


Lemma compare_spec_inverse :
   forall n f g, f n = false -> g n = false ->
        if bool_dec ((compare_spec f g) n) true 
                    then fb2nat n f < fb2nat n g 
                     else fb2nat n g <= fb2nat n f.
Proof.
intros.
Admitted.


Lemma compare_spec_correct_result:
   forall n x y, 0 < n -> x < 2 ^ n -> y < 2 ^ n ->
          fb2nat n (compare_spec (nat2fb x) (nat2fb y))
              = (if x <? y then x + (2^n) - y else x - y).
Proof.
intros.
Admitted.


Definition one_step_sepc n f g := 
    let twof := (times_two_spec f) in
    let compare := compare_spec twof g in 
             if compare n then adder_spec twof g else twof.

Lemma one_step_correct :
  forall n x y , 0 < n -> x < 2 ^ (n-1) -> y < 2 ^ (n-1) ->
      fb2nat n (one_step_sepc n (nat2fb x) (nat2fb y)) = (2 * x) mod y.
Proof.
intros.
Admitted.

Definition clean_bit n f := fun i => if i =? n then false else f i.


Lemma clean_bit_correct :
   forall n f, (clean_bit n f) n = false.
Proof.
intros. unfold clean_bit. 
destruct (n =? n) eqn:eq.
reflexivity.
apply EqNat.beq_nat_false in eq.
lia.
Qed.

Fixpoint repeat_step_spec n len f g :=
       match n with 
          | 0 => f
          | S n' => repeat_step_spec n' len (clean_bit len (one_step_sepc len f g)) g
       end.

Lemma repeat_step_correct :
   forall len n x y,  0 < n -> x < 2 ^ (n-1) -> y < 2 ^ (n-1) -> x < y ->
      fb2nat n (repeat_step_spec len n (nat2fb x) (nat2fb y)) = (2 ^ len * x) mod y.
Proof.
intros.
induction len.
simpl.
assert (y <> 0) by lia.
specialize (Nat.mod_small_iff (x + 0) y H3) as eq.
assert (x + 0 < y) by lia.
apply eq in H4.
rewrite H4.
rewrite nat2fb_inverse.
lia.
assert (x < 2^n).
assert (n = S (n-1)) by lia.
rewrite H5.
rewrite Nat.pow_succ_r.
lia.
lia.
Admitted.

Definition basis_step_spec n fold f g :=
    let fplus := (adder_spec fold f) in
    let compare := compare_spec fplus g in 
             if compare n then adder_spec fplus g else fplus.


Lemma basis_step_correct:
   forall n x y z,  0 < n -> x < 2 ^ (n-1) -> y < 2 ^ (n-1)
       -> z < 2 ^ (n-1) ->
       fb2nat n (basis_step_spec n (nat2fb x) (nat2fb y) (nat2fb z)) = (x + y) mod z.
Proof.
intros.
unfold basis_step_spec.
specialize (adder_spec_correct n x y H H0 H1) as eq.
Admitted.

Fixpoint all_step_spec' n len (c: nat -> bool) fold f g :=
   match n with 
    | 0 => if c 0 then basis_step_spec len fold f g else f
    | S m => if c (S m) then
         all_step_spec' m len c fold (repeat_step_spec (S m) len f g) g
         else all_step_spec' m len c fold f g
   end.

Definition all_step_spec dim c f g := all_step_spec' (dim - 1) dim c f f g.

Lemma all_step_correct :
  forall dim c x y, fb2nat dim (all_step_spec dim (nat2fb c) (nat2fb x) (nat2fb y)) = (c * x) mod y.
Proof.
intros.
Admitted.
