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
Arguments Cnorm2 c /.
Arguments Cnorm c /.

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
Inductive smallest_interval (P : R -> Prop) : R -> Prop :=
  | SI: forall r1 r2, (P r1) -> (P r2) ->
           (forall r, 0 < r < r1 -> ~ P r) ->
           (forall r, r2 < r < 1 -> ~ P r) ->
           smallest_interval P (r2 - r1)%R.

(* Need to connect run-based definition to eay one. *)
Lemma pr_run_outcome_eq : forall dim (c : base_ucom dim) n r,
  r > 0 ->
  (n < 2^dim)%nat ->
  pr_run_outcome c n = r <-> smallest_interval (fun x => run_ucom_all c x = n) r.
Proof.
  split; intros.
  - unfold pr_run_outcome in H1.
    unfold run_ucom_all.
    remember (map Cnorm2 (vec_to_list (uc_eval c × basis_vector (2 ^ dim) 0))) as l.
    gen r.
    induction n; intros.
    + replace r with (r - 0)%R by lra.
      constructor.
      * unfold sample. destruct l. easy. destruct (Rle_lt_dec 0 r0); auto.
        destruct (vec_to_list (uc_eval c × basis_vector (2 ^ dim) 0)). discriminate.
        simpl in Heql. inversion Heql; subst.
        contradict r1. apply Rge_not_lt. field_simplify.
        specialize (pow2_ge_0 (fst c0)) as G1.
        specialize (pow2_ge_0 (snd c0)) as G2.
        lra.  (* TODO: hideous. add Cnorm2 lemmas *)
      * unfold sample.
        destruct l. easy.
        simpl in H1. subst.
        destruct (Rle_lt_dec r r); auto.
        lra.
      * intros; lra.
      * intros.
        unfold sample.
        destruct l; simpl in *. lra.
        subst.
        destruct (Rle_lt_dec r0 r); auto.
        lra.
    + assert (smallest_interval (fun x : R => sample l x = n) (nth n l 0)).
      apply IHn; auto. lia.
      2:{ inversion H2. 

      
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

