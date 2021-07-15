Require Import UnitarySem.
Require Import VectorStates.
(* Require Import Coq.Lists.Streams. *)

(* Parameter rng : Stream R. *)

(* MOVE TO: Matrix.v *)
Fixpoint vec_to_list {n : nat} (v : Vector n) :=
  match n with
  | O    => nil
  | S n' => v n' O :: @vec_to_list n' v
  end.

Lemma vec_to_list_length_aux : forall m n (v : Vector n), length (@vec_to_list m v) = m.
Proof.
  intros.
  induction m; auto.
  simpl. rewrite IHm.
  reflexivity.
Qed.

Lemma vec_to_list_length : forall n (v : Vector n), length (vec_to_list v) = n.
Proof. intros. apply vec_to_list_length_aux. Qed.
  
  
(* MOVE TO: Complex.v *)
Definition Cnorm2 (c : C) : R := fst c ^ 2 + snd c ^ 2.
Definition Cnorm (c : C) : R := √ (Cnorm2 c).
Lemma Cnorm2_ge_0 : forall c, 0 <= Cnorm2 c.
Proof. intros. simpl. field_simplify. apply Rplus_le_le_0_compat; apply pow2_ge_0. Qed.
  
Fixpoint sample (l : list R) (r : R) : nat :=
  match l with
  | nil    => 0
  | x :: l' => if Rle_lt_dec r x then 0 else S (sample l' (r-x))
  end.

(* Returns a nat, could also return the basis vector *)
(* Could provide input explicitly instead of assuming all zero *)
Definition run_ucom_all {dim} (c : base_ucom dim) (rnd : R) : nat :=
  let v := (uc_eval c) × basis_vector (2^dim) 0 in
  let l := map Cnorm2 (vec_to_list v) in
  sample l rnd.

Definition pr_run_outcome {dim} (c : base_ucom dim) (n : nat) : R :=
  let v := (uc_eval c) × basis_vector (2^dim) 0 in
  let l := map Cnorm2 (vec_to_list v) in
  nth n l 0.

(* There's probably a better run-based definition. *)
(* Not sure if we need r1 <= r2 or 0 or 1 bounds. 
   < and <= should be equivalent for our purposes. *)
Inductive max_interval (P : R -> Prop) : R -> Prop :=
| MI: forall r1 r2, 0 <= r1 <= r2 ->
           (forall r, r1 < r < r2 -> P r) ->               
           (forall r, 0 <= r < r1 -> ~ P r) ->
           (forall r, r2 < r -> ~ P r) ->
           max_interval P (r2 - r1)%R.

Lemma max_interval_unique : forall r1 r2 P,
    max_interval P r1 ->
    max_interval P r2 ->
    r1 = r2.
Proof.
  intros.
  inversion H; subst.
  inversion H0; subst.
  destruct (total_order_T r0 r1) as [[L | E] | G] .
  assert (~ (P r0)). apply H7. lra.
  assert ((P r1)). apply H2.
(* bit tricky in current form *)
Admitted.  
  
(* Generalizes the lemma below *)
Lemma max_interval_size : forall k l,
    (k < length l)%nat ->
    Forall (fun x => 0 <= x) l ->
    max_interval (fun x => sample l x = k) (nth k l 0).
Proof.
  intros.
  gen k.
  induction l; intros; simpl in H; try lia.
  inversion H0; subst.
  destruct k; simpl.
  - replace a with (a-0)%R by lra.
    econstructor; intros; try lra. 
    + destruct (Rle_lt_dec r (a - 0)); try lra; easy.
    + destruct (Rle_lt_dec r (a - 0)); try lra. easy.
  - apply lt_S_n in H.
    specialize (IHl H4 k H).
    inversion IHl.
    replace (r2 - r1)%R with ((r2 + a) - (r1 + a))%R by lra.
    constructor; intros; try lra.
    + destruct (Rle_lt_dec r a). lra.
      f_equal.
      apply H5.
      lra.
    + destruct (Rle_lt_dec r a). lia.
      intros F.
      apply (H6 (r-a)%R). lra.
      lia.
    + destruct (Rle_lt_dec r a). lia.
      intros F.
      apply (H7 (r-a)%R). lra.
      lia.
Qed.      
  
(* Need to connect run-based definition to eay one. *)
Lemma pr_run_outcome_eq : forall dim (c : base_ucom dim) n,
  (n < 2^dim)%nat ->
  max_interval (fun x : R => run_ucom_all c x = n) (pr_run_outcome c n).
Proof.
  intros.
  apply max_interval_size.
  rewrite map_length, vec_to_list_length; easy.
  remember (vec_to_list (uc_eval c × basis_vector (2 ^ dim) 0)) as l. clear Heql.
  apply Forall_nth; intros.
  gen l. induction i; intros.
  - destruct l. simpl in H0; lia.
    simpl. apply Cnorm2_ge_0.
  - destruct l; simpl in H0; try lia.
    apply IHi.
    lia.
Qed.    

(* I prefer this definition, but it needs the uniqueness proof above. *)
Lemma pr_run_outcome_eq' : forall dim (c : base_ucom dim) n r,
  (n < 2^dim)%nat ->
  pr_run_outcome c n = r <-> max_interval (fun x => run_ucom_all c x = n) r.
Proof.
  split; intros.
  - rewrite <- H0.
    apply pr_run_outcome_eq.
    easy.
  - eapply max_interval_unique.
    apply pr_run_outcome_eq; trivial.
    easy.
Qed.
    
