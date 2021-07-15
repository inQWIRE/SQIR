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
(* Not sure if we need r1 <= r2 or the 0 or 1 bounds. 
   < and <= should be equivalent for our purposes. *)
Inductive max_interval (P : R -> Prop) : R -> Prop :=
| MI: forall r1 r2, 0 <= r1 <= r2 ->
           (forall r, r1 < r < r2 -> P r) ->               
           (forall r, 0 <= r < r1 -> ~ P r) ->
           (forall r, r2 < r <= 1 -> ~ P r) ->
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
  assert ((P r0)). apply H7. lra.
  
  
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
    + destruct (Rle_lt_dec r (a - 0)); try lra; easy.
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
Lemma pr_run_outcome_eq : forall dim (c : base_ucom dim) n r,
  (n < 2^dim)%nat ->
  pr_run_outcome c n = r <-> max_interval (fun x => run_ucom_all c x = n) r.
Proof.
  intros.
  assert(SOL: max_interval (fun x : R => run_ucom_all c x = n) (pr_run_outcome c n)). 
  { apply max_interval_size.
    rewrite map_length, vec_to_list_length.
    easy.
    remember (vec_to_list (uc_eval c × basis_vector (2 ^ dim) 0)) as l. clear Heql.
    apply Forall_nth; intros.
    gen l. induction i; intros.
    destruct l. simpl in H0; lia.
    simpl. apply Cnorm2_ge_0.
    destruct l; simpl in H0; try lia.
    apply IHi.
    lia.
    }
  split.
  intros; subst; auto.

    
  split; intros.
  - unfold pr_run_outcome in H0.
    unfold run_ucom_all.
    remember (map Cnorm2 (vec_to_list (uc_eval c × basis_vector (2 ^ dim) 0))) as l.
    gen r.
    induction n; intros.
    + replace r with (r - 0)%R by lra.
      constructor; intros; try lra.
      * destruct l; simpl in *.
        lra.
        subst.
        destruct (vec_to_list (uc_eval c × basis_vector (2 ^ dim) 0)); try easy.
        simpl in Heql. inversion Heql; subst.
        apply Cnorm2_ge_0.
      * unfold sample.
        destruct l; trivial.
        simpl in H0; subst.
        destruct (Rle_lt_dec r0 r); auto.
        lra.
      * unfold sample.
        assert (length l = length (map Cnorm2 (vec_to_list (uc_eval c × basis_vector (2 ^ dim) 0)))) by (rewrite Heql; easy). 
        destruct l; trivial.
        rewrite map_length, vec_to_list_length in H2. simpl in H2. lia.
        simpl in H0; subst.
        destruct (Rle_lt_dec r0 r); auto.
        lra.
    + assert (smallest_interval (fun x : R => sample l x = n) (nth n l 0)).
      apply IHn. lia. easy.
      assert (length l = length (map Cnorm2 (vec_to_list (uc_eval c × basis_vector (2 ^ dim) 0)))) by (rewrite Heql; easy). 
      destruct l; trivial.
      rewrite map_length, vec_to_list_length in H2. simpl in H2. lia.
      clear H2.
      simpl in H0; subst.
      inversion H1.
      remember (nth n l 0 + r2)%R as r3.
      replace (nth n l 0) with (r3 - r2)%R by lra.
      constructor.
      * assert (nth (S n) (r0 :: l) 0 >= 0).
        { rewrite Heql.
          apply Forall_nth.
          admit. (* trivial *)
          rewrite map_length, vec_to_list_length. easy.
        }
        simpl in H6. lra.
      *
   (*   intros.

        destruct n.
        -- rewrite <- H0 in *.
           unfold sample.
           destruct (Rle_lt_dec r (r2 - r1)).
           lra.
           
           
          
        assert (Hrl : 0 <= r0).
        { destruct (vec_to_list (uc_eval c × basis_vector (2 ^ dim) 0)); try easy.
          simpl in Heql. inversion Heql; subst.
          apply Cnorm2_ge_0. }
        simpl in *.
        destruct (Rle_lt_dec r r0) eqn:E.
        specialize (H3 r). specialize (H4 r). specialize (H5 r). rewrite E in *.
        rewrite E in *.
        
        
        
        destruct n.
        simpl in *.

        
        unfold sample. 
        destruct (Rle_lt_dec r r0).
        unfold sample in *. simpl in *.
        econstructor.
          unfold Forall.
          Search Forall map.
          
        destruct ((vec_to_list (uc_eval c × basis_vector (2 ^ dim) 0))); try easy.
        inversion Heql.
        
      destruct n. simpl in *. 
      
      simpl in H1.
      
        destruct l.
      
      simpl in H0.
*)
        admit.
      * admit.
      * admit.
  - unfold pr_run_outcome.
    
    


    induction n.
    + inversion H0.
      unfold run_ucom_all in *.
      destruct (map Cnorm2 (vec_to_list (uc_eval c × basis_vector (2 ^ dim) 0))) eqn:E.
      specialize (map_length Cnorm2 (vec_to_list (uc_eval c × basis_vector (2 ^ dim) 0))) as Hm.
      rewrite E in Hm. rewrite vec_to_list_length in Hm. simpl in Hm. lia.
      simpl.
      rewrite H5. assert (r >= 0) by lra. clear H1 H5.
      destruct (total_order_T r r0) as [[L | EQ] | G]; try lra.
      * 

Locate C.
        
(* Below would be a nice definition, but I couldn't make it work: 
Search R "max".
Search lub.
Search (R -> Prop).
Search ((R -> Prop) -> R).

Lemma run_ucom_all_bound : forall dim (c : base_ucom dim) n,
    (n < 2^dim)%nat -> bound (fun x => run_ucom_all c x = n).
Proof.
  intros.
  unfold bound.
  exists 1. intros x H'.
  unfold run_ucom_all in *.
  Search WF_Unitary uc_eval.
  (* Okay, we need lemmas about unit vectors. *)
  (* In this case, if c is well typed, the outcome is a unit vector else 0. *)
  (* Either way, our bound holds *)
Admitted.  

Definition pr_run_outcome {dim} (c : base_ucom dim) (n : nat) (pf : (n < 2^dim)%nat) : R :=
  completeness (fun x => run_ucom_all c x = n) (run_ucom_all_bound dim c n pf). 

*)  

