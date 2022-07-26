Require Import QuantumLib.Prelim QuantumLib.Permutations QuantumLib.Summation.
Require Import FMapAVL FMapFacts.

Local Close Scope C_scope.
Local Close Scope R_scope.

(** * Definition of layouts for mapping **)

(** We represent a layout with two maps: one from logical qubits to physical 
    qubits, and one from physical qubits to logical qubits. We represent both
    logical and physical qubits using nats -- you can think of them as indices
    into a global qubit register. We use two maps instead of one to make lookup 
    in either direction efficient. 

    It would be better to define an abstract type for bidirectional maps,
    but we'll settle for a hardcoded implementation for now.
**)

Module FMap := FMapAVL.Make(Coq.Structures.OrderedTypeEx.Nat_as_OT).
Module FMapFacts := FMapFacts.Facts FMap.

Definition layout : Type := FMap.t nat * FMap.t nat.
Definition empty : layout := (FMap.empty nat, FMap.empty nat).

(* To help keep things straight, we'll use lay for layout, l for logical
   qubit, and p for physical qubit. *)
Definition find_phys (lay : layout) l := FMap.find l (fst lay).
Definition get_phys lay l := match find_phys lay l with Some p => p | _ => O end.
Definition find_log (lay : layout) p := FMap.find p (snd lay).
Definition get_log lay p := match find_log lay p with Some l => l | _ => O end.

Definition add (lay : layout) l p : layout :=
  (FMap.add l p (fst lay), FMap.add p l (snd lay)).

Definition remove (lay : layout) l p : layout :=
  (FMap.remove l (fst lay), FMap.remove p (snd lay)).

Lemma find_phys_empty : forall l, find_phys empty l = None.
Proof. 
  intros.
  unfold find_phys, empty.
  simpl.
  apply FMapFacts.empty_o.
Qed.

Lemma find_phys_add_eq : forall lay l p, find_phys (add lay l p) l = Some p.
Proof. 
  intros.
  unfold find_phys, add.
  destruct lay; simpl.
  apply FMapFacts.add_eq_o.
  reflexivity.
Qed.

Lemma find_phys_add_neq : forall lay l p l', 
  l <> l' -> find_phys (add lay l p) l' = find_phys lay l'.
Proof. 
  intros.
  unfold find_phys, add.
  destruct lay; simpl.
  apply FMapFacts.add_neq_o.
  assumption.
Qed.

Lemma find_log_empty : forall l, find_log empty l = None.
Proof. 
  intros.
  unfold find_log, empty.
  simpl.
  apply FMapFacts.empty_o.
Qed.

Lemma find_log_add_eq : forall lay l p, find_log (add lay l p) p = Some l.
Proof. 
  intros.
  unfold find_phys, add.
  destruct lay; simpl.
  apply FMapFacts.add_eq_o.
  reflexivity.
Qed.

Lemma find_log_add_neq : forall lay l p p', 
  p <> p' -> find_log (add lay l p) p' = find_log lay p'.
Proof. 
  intros.
  unfold find_phys, add.
  destruct lay; simpl.
  apply FMapFacts.add_neq_o.
  assumption.
Qed.

(** A layout is well-formed if find_log and find_phys are inverses **)
Definition well_formed (lay : layout) : Prop := 
  forall l p, find_phys lay l = Some p <-> find_log lay p = Some l.

Lemma empty_well_formed : well_formed empty.
Proof. 
  unfold well_formed. 
  intros l p.
  rewrite find_phys_empty, find_log_empty.
  easy.
Qed.     

Definition In lay l p := 
  (exists l, find_phys lay l = Some p) \/ (exists p, find_log lay p = Some l).

Lemma add_well_formed : forall lay l p,
  well_formed lay -> ~ In lay l p -> well_formed (add lay l p).
Proof.
  intros lay l p WF H l' p'.
  unfold well_formed, In, find_phys, find_log, add in *.
  destruct lay; simpl in *.
  apply Decidable.not_or in H as [H1 H2].
  eapply Classical_Pred_Type.not_ex_all_not in H1.
  eapply Classical_Pred_Type.not_ex_all_not in H2.
  bdestruct (l =? l'); bdestruct (p =? p'); subst.
  - rewrite 2 FMapFacts.add_eq_o by auto.
    easy.
  - rewrite FMapFacts.add_eq_o by auto.
    rewrite FMapFacts.add_neq_o by auto.
    split; intro H3.
    inversion H3.
    contradiction.
    contradict H2. 
    apply H3.
  - rewrite FMapFacts.add_neq_o by auto.
    rewrite FMapFacts.add_eq_o by auto.
    split; intro H3.
    contradict H1.
    apply H3.
    inversion H3.
    contradiction.
  - rewrite 2 FMapFacts.add_neq_o by auto.
    easy.
Qed.

Lemma not_In_add : forall lay l0 l1 p0 p1,
  l0 <> l1 -> p0 <> p1 -> ~ In lay l0 p0 -> ~ In (add lay l1 p1) l0 p0.
Proof.
  intros lay l0 l1 p0 p1 Hl Hp H contra.
  contradict H.
  destruct contra as [[l H] | [p H]].
  left.
  bdestruct (l =? l1). subst.
  rewrite find_phys_add_eq in H.
  inversion H; subst; contradiction.
  rewrite find_phys_add_neq in H by auto.
  exists l. apply H.
  right.
  bdestruct (p =? p1). subst.
  rewrite find_log_add_eq in H.
  inversion H; subst; contradiction.
  rewrite find_log_add_neq in H by auto.
  exists p. apply H.
Qed.

(** A layout is bijective for n if it is well formed and has some 
   binding for every value up to n. *)
Definition layout_bijective (n : nat) (lay : layout) : Prop :=
  well_formed lay /\
  (forall l, l < n -> exists p, find_phys lay l = Some p /\ p < n) /\
  (forall p, p < n -> exists l, find_log lay p = Some l /\ l < n).

Lemma get_phys_perm : forall n l,
  layout_bijective n l ->
  permutation n (get_phys l).
Proof.
  intros n l H.
  exists (get_log l).
  intros x Hx.
  destruct H as [H1 [H2 H3]].
  specialize (H2 x Hx).
  specialize (H3 x Hx).
  destruct H2 as [pq [? ?]].
  destruct H3 as [lq [? ?]].
  unfold get_log, get_phys.
  unfold find_log, find_phys in *.
  rewrite H, H2.
  repeat split; auto.
  apply H1 in H.
  unfold find_log in H. 
  rewrite H. auto.
  apply H1 in H2.
  unfold find_phys in H2. 
  rewrite H2. auto.
Qed.

Lemma get_log_perm : forall n l,
  layout_bijective n l ->
  permutation n (get_log l).
Proof.
  intros n l H.
  exists (get_phys l).
  intros x Hx.
  destruct H as [H1 [H2 H3]].
  specialize (H2 x Hx).
  specialize (H3 x Hx).
  destruct H2 as [pq [? ?]].
  destruct H3 as [lq [? ?]].
  unfold get_log, get_phys.
  unfold find_log, find_phys in *.
  rewrite H, H2.
  repeat split; auto.
  apply H1 in H2.
  unfold find_phys in H2. 
  rewrite H2. auto.
  apply H1 in H.
  unfold find_log in H. 
  rewrite H. auto.
Qed.

Lemma get_log_phys_inv : forall n lay l,
  layout_bijective n lay -> l < n ->
  get_log lay (get_phys lay l) = l.
Proof.
  intros n lay l [Hlay [H1 _]] Hl.
  unfold get_log, get_phys.
  specialize (H1 l Hl).
  destruct H1 as [p [H2 _]].
  rewrite H2.
  apply Hlay in H2.
  rewrite H2.
  reflexivity.
Qed.

Lemma get_phys_log_inv : forall n lay p,
  layout_bijective n lay -> p < n ->
  get_phys lay (get_log lay p) = p.
Proof.
  intros n lay p [Hlay [_ H1]] Hp.
  unfold get_log, get_phys.
  specialize (H1 p Hp).
  destruct H1 as [l [H2 _]].
  rewrite H2.
  apply Hlay in H2.
  rewrite H2.
  reflexivity.
Qed.

Lemma get_phys_lt : forall dim m x,
  layout_bijective dim m ->
  x < dim ->
  get_phys m x < dim.
Proof.
  intros dim m x Hm Hx.
  apply get_phys_perm in Hm.
  destruct Hm as [? Hm].
  specialize (Hm x Hx).
  destruct Hm as [? _].
  assumption.
Qed.

Lemma get_phys_neq : forall dim m x y,
  layout_bijective dim m ->
  x < dim -> y < dim -> x <> y ->
  get_phys m x <> get_phys m y.
Proof.
  intros dim m x y Hm Hx Hy Hneq.
  apply get_phys_perm in Hm.
  intro contra.
  apply permutation_is_injective with (x:=x) (y:=y) in Hm; auto.
Qed.

Lemma get_log_lt : forall dim m x,
  layout_bijective dim m ->
  x < dim ->
  get_log m x < dim.
Proof.
  intros dim m x Hm Hx.
  apply get_log_perm in Hm.
  destruct Hm as [? Hm].
  specialize (Hm x Hx).
  destruct Hm as [? _].
  assumption.
Qed.

Lemma get_log_neq : forall dim m x y,
  layout_bijective dim m ->
  x < dim -> y < dim -> x <> y ->
  get_log m x <> get_log m y.
Proof.
  intros dim m x y Hm Hx Hy Hneq.
  apply get_log_perm in Hm.
  intro contra.
  apply permutation_is_injective with (x:=x) (y:=y) in Hm; auto.
Qed.

(** * Swap function *)

(** Swap the logical qubits associated with two physical qubits. We currently
    only use it in the case where the layout is bijective, so the definition
    (and associated correctness properties) only apply in that case. **)
Definition swap_log (lay : layout) p1 p2 : layout :=
  match find_log lay p1, find_log lay p2 with
  | Some l1, Some l2 => add (add lay l1 p2) l2 p1
  | _, _ => lay
  end.

(* It is not possible to have (layout_bijective n lay) and 
   (find_log lay p = None) for p < n. *)
Lemma layout_bijective_contradition : forall n lay p,
    p < n -> layout_bijective n lay -> find_log lay p = None -> False.
Proof.
  intros n lay p Hp Hlay Hcontra.
  destruct Hlay as [_ [_ Hlay]].
  specialize (Hlay p Hp).
  destruct Hlay as [? [H _]].
  rewrite H in Hcontra. 
  inversion Hcontra.
Qed.

Lemma find_phys_swap_log_1 : forall n lay p1 p2,
  p1 < n -> p2 < n ->
  layout_bijective n lay ->
  find_phys (swap_log lay p1 p2) (get_log lay p1) = Some p2.
Proof.
  intros n lay p1 p2 Hp1 Hp2 Hlay.
  unfold swap_log, get_log.
  destruct (find_log lay p1) eqn:H1. 
  destruct (find_log lay p2) eqn:H2.
  - destruct Hlay as [Hlay _].
    assert (H3:=H1).
    assert (H4:=H2).
    apply Hlay in H3.
    apply Hlay in H4.
    bdestruct (n1 =? n0); subst. 
    rewrite find_phys_add_eq.
    rewrite H3 in H4.
    inversion H4. auto.
    rewrite find_phys_add_neq by auto.
    rewrite find_phys_add_eq.
    reflexivity.
  - eapply layout_bijective_contradition in H2.
    easy. apply Hp2. auto.
  - eapply layout_bijective_contradition in H1.
    easy. apply Hp1. auto.
Qed.

Lemma find_phys_swap_log_2 : forall n lay p1 p2,
  p1 < n -> p2 < n ->
  layout_bijective n lay ->
  find_phys (swap_log lay p1 p2) (get_log lay p2) = Some p1.
Proof.
  intros n lay p1 p2 Hp1 Hp2 Hlay.
  unfold swap_log, get_log.
  destruct (find_log lay p1) eqn:H1. 
  destruct (find_log lay p2) eqn:H2.
  - destruct Hlay as [Hlay _].
    assert (H3:=H1).
    assert (H4:=H2).
    apply Hlay in H3.
    apply Hlay in H4.
    rewrite find_phys_add_eq.
    reflexivity.
  - eapply layout_bijective_contradition in H2.
    easy. apply Hp2. auto.
  - eapply layout_bijective_contradition in H1.
    easy. apply Hp1. auto.
Qed.

Lemma find_phys_swap_log_3 : forall n lay p1 p2 l,
  p1 < n -> p2 < n ->
  layout_bijective n lay ->
  find_log lay p1 <> Some l -> find_log lay p2 <> Some l -> 
  find_phys (swap_log lay p1 p2) l = find_phys lay l.
Proof.
  intros n lay p1 p2 l Hp1 Hp2 Hlay Hneq1 Hneq2.
  unfold swap_log.
  destruct (find_log lay p1) eqn:H1. 
  destruct (find_log lay p2) eqn:H2.
  - rewrite 2 find_phys_add_neq.
    reflexivity.
    intro contra. subst. contradiction.
    intro contra. subst. contradiction.
  - eapply layout_bijective_contradition in H2.
    easy. apply Hp2. auto.
  - eapply layout_bijective_contradition in H1.
    easy. apply Hp1. auto.
Qed.

Lemma find_log_swap_log_1 : forall n lay p1 p2,
  p1 < n -> p2 < n ->
  layout_bijective n lay ->
  find_log (swap_log lay p1 p2) p1 = find_log lay p2.
Proof.
  intros n lay p1 p2 Hp1 Hp2 Hlay.
  unfold swap_log.
  destruct (find_log lay p1) eqn:H1.
  destruct (find_log lay p2) eqn:H2. 
  - rewrite find_log_add_eq. reflexivity.
  - eapply layout_bijective_contradition in H2.
    easy. apply Hp2. auto.
  - eapply layout_bijective_contradition in H1.
    easy. apply Hp1. auto.
Qed.

Lemma find_log_swap_log_2 : forall n lay p1 p2,
  p1 < n -> p2 < n ->
  layout_bijective n lay ->
  find_log (swap_log lay p1 p2) p2 = find_log lay p1.
Proof.
  intros n lay p1 p2 Hp1 Hp2 Hlay.
  unfold swap_log.
  destruct (find_log lay p1) eqn:H1. 
  destruct (find_log lay p2) eqn:H2.
  - bdestruct (p1 =? p2). subst.
    rewrite H1 in H2. inversion H2. subst.
    rewrite find_log_add_eq. reflexivity.
    rewrite find_log_add_neq by assumption. 
    rewrite find_log_add_eq. reflexivity.
  - eapply layout_bijective_contradition in H2.
    easy. apply Hp2. auto.
  - eapply layout_bijective_contradition in H1.
    easy. apply Hp1. auto.
Qed.

Lemma find_log_swap_log_3 : forall n lay p1 p2 p,
  p1 < n -> p2 < n ->
  layout_bijective n lay ->
  p1 <> p -> p2 <> p ->
  find_log (swap_log lay p1 p2) p = find_log lay p.
Proof.
  intros n lay p1 p2 p Hp1 Hp2 Hlay Hneq1 Hneq2.
  unfold swap_log.
  destruct (find_log lay p1) eqn:H1. 
  destruct (find_log lay p2) eqn:H2.
  - rewrite 2 find_log_add_neq by auto.
    reflexivity.
  - eapply layout_bijective_contradition in H2.
    easy. apply Hp2. auto.
  - eapply layout_bijective_contradition in H1.
    easy. apply Hp1. auto.
Qed.

Lemma swap_log_preserves_bij : forall n lay p1 p2,
  p1 < n -> p2 < n ->
  layout_bijective n lay ->
  layout_bijective n (swap_log lay p1 p2).
Proof.
  intros n lay p1 p2 Hp1 Hp2 Hlay.
  repeat split; intros.
  - bdestruct (l =? get_log lay p1). subst.
    rewrite find_phys_swap_log_1 with (n:=n) in H by auto.
    inversion H; subst.
    rewrite find_log_swap_log_2 with (n:=n) by auto.
    unfold get_log.
    destruct (find_log lay p1) eqn:contra.
    reflexivity.
    eapply layout_bijective_contradition in contra.
    easy. apply Hp1. auto.
    bdestruct (l =? get_log lay p2). subst.
    rewrite find_phys_swap_log_2 with (n:=n) in H by auto.
    inversion H; subst.
    rewrite find_log_swap_log_1 with (n:=n) by auto.
    unfold get_log.
    destruct (find_log lay p2) eqn:contra.
    reflexivity.
    eapply layout_bijective_contradition in contra.
    easy. apply Hp2. auto.
    assert (H2:=Hlay).
    destruct Hlay as [Hlay _].
    rewrite find_phys_swap_log_3 with (n:=n) in H; auto.
    rewrite find_log_swap_log_3 with (n:=n); auto.
    apply Hlay. auto.
    all: intro contra; subst; unfold get_log in *.
    apply Hlay in H.    
    rewrite H in *. contradiction.
    apply Hlay in H.
    rewrite H in *. contradiction.
    rewrite contra in *. contradiction.
    rewrite contra in *. contradiction.
  - bdestruct (p =? p1). subst.
    rewrite find_log_swap_log_1 with (n:=n) in H by auto.
    assert (l = get_log lay p2).
    unfold get_log. rewrite H. auto. subst.
    apply find_phys_swap_log_2 with (n:=n); auto.
    bdestruct (p =? p2). subst.
    rewrite find_log_swap_log_2 with (n:=n) in H by auto.
    assert (l = get_log lay p1).
    unfold get_log. rewrite H. auto. subst.
    apply find_phys_swap_log_1 with (n:=n); auto.
    rewrite find_log_swap_log_3 with (n:=n) in H by auto.
    assert (H2:=Hlay).
    destruct Hlay as [Hlay _].
    rewrite find_phys_swap_log_3 with (n:=n); auto.
    apply Hlay. auto.
    intro contra.
    apply Hlay in H.
    apply Hlay in contra.
    rewrite H in contra.
    inversion contra. easy.
    intro contra.
    apply Hlay in H.
    apply Hlay in contra.
    rewrite H in contra.
    inversion contra. easy.
  - bdestruct (l =? get_log lay p1). subst.
    exists p2.
    split; auto.
    rewrite find_phys_swap_log_1 with (n:=n); auto.
    bdestruct (l =? get_log lay p2). subst.
    exists p1.
    split; auto.
    rewrite find_phys_swap_log_2 with (n:=n); auto.
    exists (get_phys lay l).
    assert (tmp:=Hlay).
    destruct tmp as [_ [tmp _]].
    unfold get_phys.
    specialize (tmp l H).
    destruct tmp as [p [Hp ?]].
    rewrite Hp.
    split; auto.
    rewrite find_phys_swap_log_3 with (n:=n); auto.
    unfold get_log in *.
    destruct (find_log lay p1).
    intro contra.
    inversion contra. subst. 
    contradiction. easy.
    unfold get_log in *.
    destruct (find_log lay p2).
    intro contra.
    inversion contra. subst. 
    contradiction. easy.
  - bdestruct (p =? p1). subst.
    exists (get_log lay p2).
    assert (Hlay2:=Hlay).
    destruct Hlay as [_ [_ Hlay]].
    specialize (Hlay p2 Hp2).
    destruct Hlay as [? [Hlay ?]].
    unfold get_log; rewrite Hlay.
    split; auto.
    rewrite find_log_swap_log_1 with (n:=n); auto.
    bdestruct (p =? p2). subst.
    exists (get_log lay p1).
    assert (Hlay2:=Hlay).
    destruct Hlay as [_ [_ Hlay]].
    specialize (Hlay p1 Hp1).
    destruct Hlay as [? [Hlay ?]].
    unfold get_log; rewrite Hlay.
    split; auto.
    rewrite find_log_swap_log_2 with (n:=n); auto.
    exists (get_log lay p).
    assert (Hlay2:=Hlay).
    destruct Hlay as [_ [_ Hlay]].
    specialize (Hlay p H).
    destruct Hlay as [? [Hlay ?]].
    unfold get_log; rewrite Hlay.
    split; auto.
    rewrite find_log_swap_log_3 with (n:=n); auto.
Qed.

(** * Trivial layout *)

Fixpoint trivial_layout n : layout :=
  match n with
  | O => empty
  | S n' => add (trivial_layout n') n' n' 
  end.

Lemma find_phys_trivial_layout : forall n x,
  x < n -> find_phys (trivial_layout n) x = Some x.
Proof.
  intros n x Hx.
  induction n. lia.
  simpl.
  bdestruct (n =? x). subst.
  apply find_phys_add_eq.
  rewrite find_phys_add_neq by assumption.
  apply IHn.
  lia.
Qed.

Lemma find_phys_trivial_layout_None : forall n x,
  x >= n -> find_phys (trivial_layout n) x = None.
Proof.
  intros n x Hx.
  induction n; simpl.
  unfold find_phys, empty.
  simpl.
  apply FMapFacts.empty_o.
  unfold find_phys, add.
  simpl.
  rewrite FMapFacts.add_neq_o by lia.
  apply IHn. lia.
Qed.

Lemma find_log_trivial_layout : forall n x,
  x < n -> find_log (trivial_layout n) x = Some x.
Proof.
  intros n x Hx.
  induction n. lia.
  simpl.
  bdestruct (n =? x). subst.
  apply find_log_add_eq.
  rewrite find_log_add_neq by assumption.
  apply IHn.
  lia.
Qed.

Lemma find_log_trivial_layout_None : forall n x,
  x >= n -> find_log (trivial_layout n) x = None.
Proof.
  intros n x Hx.
  induction n; simpl.
  unfold find_log, empty.
  simpl.
  apply FMapFacts.empty_o.
  unfold find_log, add.
  simpl.
  rewrite FMapFacts.add_neq_o by lia.
  apply IHn. lia.
Qed.

Lemma layout_bijective_0 : forall m, well_formed m -> layout_bijective 0 m.
Proof.
  split; [| split]; auto.
  intros. lia.
  intros. lia.
Qed.

Lemma trivial_layout_bijective : forall n,
  layout_bijective n (trivial_layout n).
Proof.
  induction n; simpl.
  - apply layout_bijective_0.
    apply empty_well_formed.
  - destruct IHn as [? [? ?]].
    split; [| split].
    + apply add_well_formed. auto.
      unfold In.
      intro contra.
      destruct contra as [[x contra] | [x contra]].
      bdestruct (x <? n).
      rewrite find_phys_trivial_layout in contra by auto.
      inversion contra. lia.
      rewrite find_phys_trivial_layout_None in contra by auto.
      inversion contra.
      bdestruct (x <? n).
      rewrite find_log_trivial_layout in contra by auto.
      inversion contra. lia.
      rewrite find_log_trivial_layout_None in contra by auto.
      inversion contra.
    + intros.
      bdestruct (n =? l). subst.
      exists l. split; auto.
      apply find_phys_add_eq.
      exists l. split; auto.
      rewrite find_phys_add_neq by assumption.
      apply find_phys_trivial_layout.
      lia.
    + intros.
      bdestruct (n =? p). subst.
      exists p. split; auto.
      apply find_log_add_eq.
      exists p. split; auto.
      rewrite find_log_add_neq by assumption.
      apply find_log_trivial_layout.
      lia.
Qed.

(** * Convert between a layout and a list (for I/O) *)

(** Convert a layout to a list where Some l at index p indicates that
   logical qubit l is stored at physcial qubit p.  *)
Fixpoint layout_to_list' x (m : layout) :=
  match x with 
  | O => []
  | S x' => (layout_to_list' x' m) ++ [find_log m x'] 
  end.
Definition layout_to_list n (m : layout) := 
  layout_to_list' n m.

(** Produce a layout from its list representation. *)
Fixpoint list_to_layout' l acc : layout :=
  match l with
  | [] => empty
  | h :: t =>
      let m' := list_to_layout' t (S acc) in
      add m' h acc
  end.
Definition list_to_layout l : layout := 
  list_to_layout' l 0.

(** Examples *)
Definition test_layout : layout := 
  add (add (add (add (add empty 4 1) 3 0) 2 3) 1%nat 2) 0 4.

(* Expected output: [Some 3; Some 4; Some 1; Some 2; Some 0] *)
Compute (layout_to_list 5 test_layout).
(* Expected output: [Some 0; Some 1; Some 2; Some 3; Some 4] *)
Compute (layout_to_list 5 (list_to_layout (0 :: 1 :: 2 :: 3 :: 4 :: []))).
(* Expected output: [Some 3; Some 4; Some 1; Some 2; Some 0] *)
Compute (layout_to_list 5 (list_to_layout (3 :: 4 :: 1 :: 2 :: 0 :: []))).

Fixpoint nodup (l : list nat) : bool := (* different from Coq's standard defn *)
  match l with
  | [] => true
  | x::xs => if existsb (fun y => y =? x) xs then false else nodup xs
  end.

Lemma nodup_NoDup : forall l, nodup l = true -> NoDup l.
Proof.
  induction l; simpl; intros. 
  constructor.
  destruct (existsb (fun y : nat => y =? a) l) eqn:b.
  inversion H.
  constructor.
  intro contra.
  specialize In_nth as HIn.
  specialize (HIn nat l a O contra).
  destruct HIn as [n [Hn1 Hn2]].
  specialize existsb_nth as He.
  specialize (He nat (fun x => x =? a) l n O Hn1 b).
  rewrite Hn2 in He.
  rewrite Nat.eqb_refl in He.
  inversion He.
  apply IHl. auto.
Qed.

Definition check_list l := forallb (fun x => x <? length l) l && nodup l.

Fixpoint nth_opt {A} n (l : list A) :=
  match n, l with
  | O, h :: _ => Some h
  | O, _ => None
  | S n', [] => None
  | S n', _ :: t => nth_opt n' t
  end.

Lemma nth_opt_Some : forall {A} i (l : list A) a, nth_opt i l = Some a -> List.In a l.
Proof.
  intros A i l a H.
  gen i.
  induction l; intros i H.
  destruct i; simpl in H; inversion H.
  destruct i; simpl in *.
  inversion H; subst.
  left. auto.
  right. eapply IHl. apply H.
Qed.

Lemma nth_opt_bound : forall {A} i (l : list A), i < length l -> exists a, nth_opt i l = Some a.
Proof.
  intros A i l H.
  gen i.
  induction l; intros i H; simpl in H.
  lia.
  destruct i; simpl.
  exists a. reflexivity.
  apply IHl. lia.
Qed.

Lemma find_log_list_to_layout' : forall l i x,
  i <= x -> find_log (list_to_layout' l i) x = nth_opt (x - i) l.
Proof.
  intros l i x Hi.
  gen i.
  induction l; intros.
  simpl.
  rewrite find_log_empty.
  destruct (x - i)%nat; reflexivity.
  simpl.
  bdestruct (i =? x). subst.
  rewrite find_log_add_eq.
  rewrite Nat.sub_diag.
  reflexivity.
  rewrite find_log_add_neq by auto.
  rewrite IHl by lia.
  replace (x - i)%nat with (S (x - S i))%nat by lia.
  reflexivity.
Qed.

Lemma find_log_list_to_layout'_None : forall l i x,
  x < i -> find_log (list_to_layout' l i) x = None.
Proof.
  intros l i x Hi.
  gen i.
  induction l; intros.
  simpl.
  apply find_log_empty.
  simpl.
  rewrite find_log_add_neq by lia.
  apply IHl. lia.
Qed.

Fixpoint find_index' x l acc :=
  match l with
  | [] => None
  | h :: t => if h =? x then Some acc else find_index' x t (S acc)
  end.
Definition find_index x l := find_index' x l O.

Lemma find_index_Some : forall x l,
  List.In x l -> exists n, find_index x l = Some n /\ n < length l.
Proof.
  intros x l H. 
  assert (aux : forall i, exists n : nat, find_index' x l i = Some n /\ n < i + length l).
  { induction l.
    inversion H.
    intro i.
    simpl in *.
    bdestruct (a =? x). subst.
    exists i.
    split; auto. lia.
    destruct H; try contradiction.
    specialize (IHl H (S i)).
    destruct IHl as [n [? ?]].
    exists n.
    split.
    apply H1.
    lia. }
  apply aux.
Qed.

Lemma find_index'_geq : forall n l i x,
  find_index' n l i = Some x -> i <= x.
Proof.
  induction l; intros i x H; simpl in H.
  inversion H.
  bdestruct (a =? n). subst.
  inversion H. lia.
  apply IHl in H. lia.
Qed.

Lemma find_phys_list_to_layout' : forall l i x,
  find_phys (list_to_layout' l i) x = find_index' x l i.
Proof.
  intros l i x.
  gen i.
  induction l; intros.
  simpl.
  rewrite find_phys_empty.
  reflexivity.
  simpl.
  bdestruct (a =? x). subst.
  rewrite find_phys_add_eq.
  reflexivity.
  rewrite find_phys_add_neq by auto.
  apply IHl.
Qed.

Lemma list_to_layout'_WF : forall l i, NoDup l -> well_formed (list_to_layout' l i).
Proof.
  intros l i Hl.
  gen i.
  induction l; intro i.
  apply empty_well_formed.
  inversion Hl; subst.
  simpl.
  apply add_well_formed.
  apply IHl. auto.
  unfold In.
  apply Classical_Prop.and_not_or.
  split.
  apply Classical_Pred_Type.all_not_not_ex.
  intros n contra.
  rewrite find_phys_list_to_layout' in contra.
  apply find_index'_geq in contra. lia.
  apply Classical_Pred_Type.all_not_not_ex.
  intros n contra.
  bdestruct (n <? S i).
  rewrite find_log_list_to_layout'_None in contra by auto.
  inversion contra.
  rewrite find_log_list_to_layout' in contra by lia.
  apply nth_opt_Some in contra.
  contradiction.
Qed.

Lemma count_occ_bounded : forall l n,
  (forall x : nat, List.In x l -> x < n) ->
  big_sum (fun x => count_occ Nat.eq_dec l x) n = length l.
Proof.
  induction l; intros n H.
  simpl. rewrite big_sum_0; auto.
  assert (H0 : forall x : nat, List.In x l -> x < n).
  { intros. apply H. simpl. right. auto. }
  apply IHl in H0.
  clear IHl.
  simpl.
  rewrite <- H0.
  assert (Ha : a < n).
  apply H. left. auto.
  clear - Ha.
  induction n.
  lia.
  simpl.
  bdestruct (a =? n).
  subst. clear.
  destruct (Nat.eq_dec n n); try lia.
  rewrite <- Nat.add_succ_r.
  apply f_equal2; auto.
  apply big_sum_eq_bounded.
  intros x Hx.
  destruct (Nat.eq_dec n x); lia.
  rewrite IHn by lia.
  rewrite <- Nat.add_succ_l.
  apply f_equal2; auto.
  destruct (Nat.eq_dec a n); lia.
Qed.

Lemma list_bounded_no_dups : forall l x,
  (forall x, List.In x l -> x < length l) -> NoDup l ->
  x < length l -> List.In x l.
Proof.
  intros l x BD ND Hx.
  apply (count_occ_In Nat.eq_dec l x).
  rewrite (NoDup_count_occ Nat.eq_dec l) in ND.
  apply count_occ_bounded in BD.
  assert (count_occ Nat.eq_dec l x <> 0).
  { intro contra.
    contradict BD.
    apply Nat.lt_neq.
    remember (length l) as n.
    clear Heqn.
    induction n.
    lia.
    simpl.
    bdestruct (x =? n).
    subst. clear IHn Hx.
    rewrite contra. clear contra.
    rewrite Nat.add_0_r.
    assert (big_sum (fun x : nat => count_occ Nat.eq_dec l x) n <= big_sum (fun _ => 1%nat) n).
    apply Nsum_le.
    intros x Hx. apply ND.
    rewrite big_sum_constant in H.
    rewrite times_n_nat in H.
    lia.
    specialize (ND n).
    lia. }
  simpl in H.
  lia.
Qed.

(** A bounded list with no duplicates produces a bijective layout. *)
Lemma check_list_layout_bijective : forall l,
  check_list l = true ->
  layout_bijective (length l) (list_to_layout l).
Proof.
  intros l Hl.
  unfold check_list in Hl.
  apply andb_prop in Hl as [Hl1 Hl2].
  rewrite forallb_forall in Hl1.
  apply nodup_NoDup in Hl2.
  split; [| split].
  - apply list_to_layout'_WF. 
    assumption.
  - intros x Hx.
    assert (List.In x l).
    { apply list_bounded_no_dups; auto.
      intros. apply Nat.ltb_lt. apply Hl1; auto. }
    apply find_index_Some in H as [n [? ?]].
    exists n.
    split; auto.
    unfold list_to_layout.
    rewrite find_phys_list_to_layout'.
    apply H.
  - intros x Hx.
    destruct (nth_opt x l) eqn:no.
    exists n.
    split.
    unfold list_to_layout.
    rewrite find_log_list_to_layout'.
    rewrite Nat.sub_0_r. auto. lia.
    apply nth_opt_Some in no.
    apply Hl1 in no.
    apply Nat.ltb_lt in no. auto.
    apply nth_opt_bound in Hx.
    destruct Hx as [? ?].
    rewrite H in no.
    inversion no.
Qed.

(* Also useful: prove that list_to_layout and layout_to_list are inverses *)

