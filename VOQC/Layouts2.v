Require Import QuantumLib.Prelim QuantumLib.Permutations.
Require Import Equalities FMapAVL FMapFacts.
Require Import Orders OrdersAlt OrdersEx.

Local Close Scope C_scope.
Local Close Scope R_scope.


(** * Definition of bidirectional maps *)

(** A layout maps between logical qubits (i.e., program qubits) 
   and physical qubits (i.e., qubits available on the machine).

   It is a bidirectional map, supporting lookup in either direction.
   Our definition of BiMap is based on Coq's FMapInterface.
*)

Module Type BiMap (K V : UsualDecidableType).

  Definition key := K.t.
  Definition val := V.t.

  (** Abstract type *)
  Parameter t : Type.

  (** Empty bimap *)
  Parameter empty : t.

  (** lookup functions *)
  Parameter find_val : t -> key -> option val.
  Parameter find_key : t -> val -> option key.

  (** add a (key, val) pair *)
  Parameter add : t -> key -> val -> t.

  (** Remove a (key, val) pair *)
  Parameter remove : t -> key -> val -> t.

  Section Spec.

    Variable m : t.
    Variable k k1 k2 : key.
    Variable v v1 v2 : val.

    Parameter MapsTo : t -> key -> val -> Prop.
    Definition Empty m := forall (k:key) (v:val) , ~ MapsTo m k v.

    (** Specification of empty *)
    Parameter empty_1 : Empty empty.

    (** Specification of find functions *)
    Parameter find_1 : MapsTo m k v -> find_val m k = Some v.
    Parameter find_2 : MapsTo m k v -> find_key m v = Some k.
    Parameter find_3 : find_val m k = Some v -> 
                       find_key m v = Some k -> 
                       MapsTo m k v.

    (** Specification of add *)
    Parameter add_1 : MapsTo (add m k v) k v.
    Parameter add_2 : k1 <> k2 -> v1 <> v2 -> 
                      MapsTo m k2 v2 -> MapsTo (add m k1 v1) k2 v2.
    Parameter add_3 : k1 <> k2 -> v1 <> v2 -> 
                      MapsTo (add m k1 v1) k2 v2 -> MapsTo m k2 v2.
    
    (** Specification of remove functions *)
    Parameter remove_1 : ~ MapsTo (remove m k v) k v.
    Parameter remove_2 : k1 <> k2 -> v1 <> v2 -> MapsTo m k2 v2 -> 
                         MapsTo (remove m k1 v1) k2 v2.
    Parameter remove_3 : MapsTo (remove m k2 v2) k1 v1 -> MapsTo m k1 v1.

    (** A bimap is well-formed when lookup in one direction is consistent 
       with the other. *)
    Definition well_formed (m : t) : Prop := 
      forall k v, find_val m k = Some v <-> find_key m v = Some k.

    Definition In m k v := (exists v, MapsTo m k v) \/ (exists k, MapsTo m k v).

    Parameter empty_well_formed : well_formed empty.
    Parameter add_well_formed : well_formed m -> ~ In m k v -> 
                                well_formed (add m k v).
    Parameter remove_not_In : well_formed m -> MapsTo m k v -> 
                              ~ In (remove m k v) k v.
    Parameter remove_well_formed : well_formed m -> MapsTo m k v -> 
                                   well_formed (remove m k v).

  End Spec.

End BiMap.

(** * Implementation of bidirectional maps using a pair of maps *)

Module BiMapPair (K V : UsualOrderedType).

  (* FMapInterface.WSfun uses a slightly different defn of DecidableType *)
  Module Kcompat := Backport_OT K.
  Module Vcompat := Backport_OT V.

  (* TODO: generalize this module so it takes a map type as input *)
  Module KMap := FMapAVL.Make Kcompat.
  Module VMap := FMapAVL.Make Vcompat.

  Module KMapFacts := FMapFacts.Facts KMap.
  Module VMapFacts := FMapFacts.Facts VMap.

  Module BM <: BiMap K V. 

    Definition key := K.t.
    Definition val := V.t. 
    Definition t : Type := KMap.t val * VMap.t key.

    Definition empty : t := (KMap.empty val, VMap.empty key).

    Definition find_val (m : t) (k : key) := KMap.find k (fst m).

    Definition find_key (m : t) (v : val) := VMap.find v (snd m).

    Definition add (m : t) (k : key) (v : val) : t :=
      let (m1, m2) := m in
      (KMap.add k v m1, VMap.add v k m2).

    Definition remove (m : t) (k : key) (v : val) : t :=
      let (m1, m2) := m in
      (KMap.remove k m1, VMap.remove v m2).

    Definition MapsTo (m : t) (k : key) (v : val) :=
      find_val m k = Some v /\ find_key m v = Some k.

    Definition Empty m := forall (k:key) (v:val) , ~ MapsTo m k v.

    Lemma empty_1 : Empty empty.
    Proof. 
      unfold Empty, MapsTo, empty, find_val.
      simpl.
      intros k v [contra _].
      rewrite KMapFacts.empty_o in contra.
      inversion contra.
    Qed.

    Lemma find_1 : forall m k v, MapsTo m k v -> find_val m k = Some v.
    Proof. unfold MapsTo. intros m k v [? ?]. auto. Qed.

    Lemma find_2 : forall m k v, MapsTo m k v -> find_key m v = Some k.
    Proof. unfold MapsTo. intros m k v [? ?]. auto. Qed.

    Lemma find_3 : forall m k v, 
        find_val m k = Some v -> find_key m v = Some k ->  MapsTo m k v.
    Proof. intros. unfold MapsTo. auto. Qed.

    Lemma add_1 : forall m k v, MapsTo (add m k v) k v.
    Proof. 
      intros.
      unfold MapsTo, add, find_val, find_key.
      destruct m; simpl.
      split.
      apply KMapFacts.add_eq_o. auto.
      apply VMapFacts.add_eq_o. auto.
    Qed.

    Lemma add_2 : forall m k1 k2 v1 v2,
        k1 <> k2 -> v1 <> v2 -> MapsTo m k2 v2 -> MapsTo (add m k1 v1) k2 v2.
    Proof.
      intros.
      unfold MapsTo, add, find_val, find_key.
      destruct m; simpl.
      split.
      apply find_1 in H1.
      rewrite <- H1.
      apply KMapFacts.add_neq_o. auto.
      apply find_2 in H1.
      rewrite <- H1.
      apply VMapFacts.add_neq_o. auto.
    Qed.

    Lemma add_3 : forall m k1 k2 v1 v2, 
        k1 <> k2 -> v1 <> v2 -> MapsTo (add m k1 v1) k2 v2 -> MapsTo m k2 v2.
    Proof.
      intros.
      unfold MapsTo, add, find_val, find_key in *.
      destruct m; simpl in *.
      destruct H1.
      rewrite KMapFacts.add_neq_o in H1 by auto.
      rewrite VMapFacts.add_neq_o in H2 by auto.
      split; auto.
    Qed.

    Lemma remove_1 : forall m k v, ~ MapsTo (remove m k v) k v.
    Proof.
      intros. subst.
      unfold MapsTo, remove, find_val, find_key.
      destruct m; simpl.
      rewrite KMapFacts.remove_eq_o by auto.
      easy.
    Qed.

    Lemma remove_2 : forall m k1 k2 v1 v2,
        k1 <> k2 -> v1 <> v2 -> MapsTo m k2 v2 -> MapsTo (remove m k1 v1) k2 v2.
    Proof.
      intros.
      unfold MapsTo, remove, find_val, find_key in *.
      destruct m; simpl in *.
      rewrite KMapFacts.remove_neq_o by auto.
      rewrite VMapFacts.remove_neq_o by auto.
      auto.
    Qed.
    
    Lemma remove_3 : forall m k1 k2 v1 v2, MapsTo (remove m k2 v2) k1 v1 -> MapsTo m k1 v1.
    Proof.
      intros.
      unfold MapsTo, remove, find_val, find_key in *.
      destruct m; simpl in *.
      destruct H.
      apply KMap.find_2 in H.
      apply VMap.find_2 in H0.
      split.
      apply KMap.find_1.
      eapply KMap.remove_3. apply H.
      apply VMap.find_1.
      eapply VMap.remove_3. apply H0.
    Qed.

    Definition well_formed (m : t) : Prop := 
      forall k v, find_val m k = Some v <-> find_key m v = Some k.

    Definition In m k v := (exists v, MapsTo m k v) \/ (exists k, MapsTo m k v).

    Lemma empty_well_formed : well_formed empty.
    Proof. 
      unfold well_formed, find_key, find_val, empty. 
      intros k v.
      split; intro H.
      rewrite KMapFacts.empty_o in H.
      inversion H.
      rewrite VMapFacts.empty_o in H.
      inversion H.
    Qed.     

    Lemma add_well_formed : forall m k v,
      well_formed m -> ~ In m k v -> well_formed (add m k v).
    Proof.
      intros m k v WF H k' v'.
      unfold well_formed, In, MapsTo, find_val, find_key, add in *.
      destruct m; simpl in *.
      apply Decidable.not_or in H as [H1 H2].
      eapply Classical_Pred_Type.not_ex_all_not in H1.
      eapply Classical_Pred_Type.not_ex_all_not in H2.
      destruct (KMap.E.eq_dec k k'); destruct (VMap.E.eq_dec v v'); subst.
      - rewrite KMapFacts.add_eq_o by auto.
        rewrite VMapFacts.add_eq_o by auto.
        easy.
      - rewrite KMapFacts.add_eq_o by auto.
        rewrite VMapFacts.add_neq_o by auto.
        split; intro H3.
        inversion H3.
        contradiction.
        contradict H1.
        split.
        apply WF. apply H3. apply H3.
      - rewrite KMapFacts.add_neq_o by auto.
        rewrite VMapFacts.add_eq_o by auto.
        split; intro H3.
        contradict H2.
        split.
        apply H3. apply WF. apply H3.
        inversion H3.
        contradiction.
      - rewrite KMapFacts.add_neq_o by auto.
        rewrite VMapFacts.add_neq_o by auto.
        easy.
    Qed.

    Lemma remove_not_In : forall m k v,
      well_formed m -> MapsTo m k v -> ~ In (remove m k v) k v.
    Proof.
      intros m k v WF [H1 H2].
      unfold well_formed, In, MapsTo, find_val, find_key, remove in *.
      destruct m; simpl in *.
      apply Classical_Prop.and_not_or.
      split; apply Classical_Pred_Type.all_not_not_ex.
      intro v'.
      rewrite KMapFacts.remove_eq_o by auto.
      easy.
      intro k'.
      rewrite VMapFacts.remove_eq_o by auto.
      easy.
    Qed.

    Lemma remove_well_formed : forall m k v,
      well_formed m -> MapsTo m k v -> well_formed (remove m k v).
    Proof.
      intros m k v WF [H1 H2].
      unfold well_formed, find_val, find_key, remove in *.
      destruct m; simpl in *.
      intros k' v'.
      destruct (KMap.E.eq_dec k k'); destruct (VMap.E.eq_dec v v'); subst.
      - rewrite KMapFacts.remove_eq_o by auto.
        rewrite VMapFacts.remove_eq_o by auto.
        easy.
      - rewrite KMapFacts.remove_eq_o by auto.
        rewrite VMapFacts.remove_neq_o by auto.
        split; intro H3.
        inversion H3.
        apply WF in H3.
        rewrite H1 in H3.
        inversion H3.
        contradiction.
      - rewrite KMapFacts.remove_neq_o by auto.
        rewrite VMapFacts.remove_eq_o by auto.
        split; intro H3.
        apply WF in H3.
        rewrite H2 in H3.
        inversion H3.
        contradiction.
        inversion H3.
      - rewrite KMapFacts.remove_neq_o by auto.
        rewrite VMapFacts.remove_neq_o by auto.
        easy.
    Qed.

  End BM.
  Include BM.

End BiMapPair.

(** * Layouts for mapping *)

(** For mapping, we will use a BiMapPair instantiated with FMapAVLs and
   nat key and value types. In our bimap, the keys represent _logical_ qubits 
   and the values represent _physical_ qubits. We provide special names for 
   the bimap functions to make this clear. *)

Module Layout := BiMapPair Nat_as_OT Nat_as_OT.
Import Layout.

Definition layout := t.
Definition find_phys := find_val.
Definition get_phys m k := match find_phys m k with Some v => v | _ => O end.
Definition find_log := find_key.
Definition get_log m v := match find_log m v with Some k => k | _ => O end.

(** A layout is bijective for n if it is well formed and has some 
   binding for every value up to n. *)
Definition layout_bijective (n : nat) (l : layout) : Prop :=
  well_formed l /\
  (forall lq, lq < n -> exists pq, find_phys l lq = Some pq /\ pq < n) /\
  forall pq, pq < n -> exists lq, find_log l pq = Some lq /\ lq < n.

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

Lemma get_log_phys_inv : forall n l x,
  layout_bijective n l -> x < n ->
  get_log l (get_phys l x) = x.
Proof.
  intros n l x [Hl [H1 _]] Hx.
  unfold get_log, get_phys.
  specialize (H1 x Hx).
  destruct H1 as [pq [H2 _]].
  rewrite H2.
  apply Hl in H2.
  unfold find_log.
  rewrite H2.
  reflexivity.
Qed.

Lemma get_phys_log_inv : forall n l x,
  layout_bijective n l -> x < n ->
  get_phys l (get_log l x) = x.
Proof.
  intros n l x [Hl [_ H1]] Hx.
  unfold get_log, get_phys.
  specialize (H1 x Hx).
  destruct H1 as [pq [H2 _]].
  rewrite H2.
  apply Hl in H2.
  unfold find_phys.
  rewrite H2.
  reflexivity.
Qed.

(** ** Swap function *)

(** Useful operation on layouts; swap the logical qubits associated with
   two physical qubits. *)
Definition swap_log (l : layout) pq1 pq2 : layout :=
  match find_log l pq1, find_log l pq2 with
  | None, None => l
  | Some lq, None => add (remove l lq pq1) lq pq2
  | None, Some lq => add (remove l lq pq2) lq pq1
  (* the removes aren't necessary here, but it makes the proof easier *)
  | Some lq1, Some lq2 => 
      add (add (remove (remove l lq1 pq1) lq2 pq2) lq1 pq2) lq2 pq1
  end.

(*
Lemma phys_neq_implies_log_neq : forall l lq1 lq2 pq1 pq2,
  layout_well_formed l -> 
  MapsTo l lq1 pq1 -> 
  find_key l pq2 = Some lq2 -> 
  pq1 <> pq2 ->
  lq2 <> lq1.
Proof.
  intros l lq1 lq2 pq1 pq2 H1 [H2 _] H3 H4.
  intro contra. subst.
  apply H1 in H3.
  unfold find_phys in H3.
  rewrite H2 in H3.
  inversion H3; auto.
Qed.

Lemma swap_log_1 : forall l lq1 pq1 pq2,
  layout_well_formed l -> MapsTo l lq1 pq1 -> MapsTo (swap_log l pq1 pq2) lq1 pq2.
Proof.
  intros l lq1 pq1 pq2 Hl H.
  unfold swap_log, find_log.
  rewrite (find_2 _ _ _ H).
  destruct (find_key l pq2) eqn:H1.
  - bdestruct (pq1 =? pq2).
    + subst.
      destruct H.
      rewrite H0 in H1.
      inversion H1; subst.
      apply add_1; auto.
    + apply add_2; auto.
      apply (phys_neq_implies_log_neq _ _ _ _ _ Hl H H1 H0).
      apply add_1.
  - apply add_1.
Qed.

Lemma swap_log_2 : forall l lq2 pq1 pq2,
  MapsTo l lq2 pq2 -> MapsTo (swap_log l pq1 pq2) lq2 pq1.
Proof.
  intros l lq1 pq1 pq2 H.
  unfold swap_log, find_log.
  rewrite (find_2 _ _ _ H).
  destruct (find_key l pq1); apply add_1.
Qed.

Lemma swap_log_3 : forall l lq pq pq1 pq2,
  layout_well_formed l -> pq <> pq1 -> pq <> pq2 -> 
  MapsTo l lq pq -> MapsTo (swap_log l pq1 pq2) lq pq.
Proof. 
  intros l lq pq pq1 pq2 Hl H1 H2 H3.
  unfold swap_log.
  destruct (find_log l pq1) eqn:H4; destruct (find_log l pq2) eqn:H5.
  - apply add_2; auto.
    apply (phys_neq_implies_log_neq _ _ _ _ _ Hl H3 H5 H2).
    apply add_2; auto.
    apply (phys_neq_implies_log_neq _ _ _ _ _ Hl H3 H4 H1).
  - apply add_2; auto.
    apply (phys_neq_implies_log_neq _ _ _ _ _ Hl H3 H4 H1).
    apply remove_2; auto.
    apply (phys_neq_implies_log_neq _ _ _ _ _ Hl H3 H4 H1).
  - apply add_2; auto.
    apply (phys_neq_implies_log_neq _ _ _ _ _ Hl H3 H5 H2).
    apply remove_2; auto.
    apply (phys_neq_implies_log_neq _ _ _ _ _ Hl H3 H5 H2).
  - auto.
Qed.
*)

Lemma add_preserves_bij : forall dim m k v,
  k < dim -> v < dim ->
  well_formed m ->
  (forall lq, lq < dim -> lq <> k -> exists pq, find_phys m lq = Some pq /\ pq < dim) ->
  (forall pq, pq < dim -> pq <> v -> exists lq, find_log m pq = Some lq /\ lq < dim) ->
  ~ In m k v -> 
  layout_bijective dim (add m k v).
Proof.
  intros dim m k v Hk Hv WF Hbij1 Hbij2 H.
  split; [| split].
  - apply add_well_formed; auto.
  - intros.
    bdestruct (lq =? k).
    subst.
    exists v.
    split; auto.
    apply add_1.
    specialize (Hbij1 lq H0 H1).
    destruct Hbij1 as [pq [? ?]].
    exists pq.
    split; auto.
    apply find_1.
    assert (MapsTo m lq pq).
    { split. assumption. apply WF. assumption. }
    apply add_2; auto.
    intro contra.
    subst.
    contradict H.
    right.
    exists lq.
    assumption.
  - intros.
    bdestruct (pq =? v).
    subst.
    exists k.
    split; auto.
    apply add_1.
    specialize (Hbij2 pq H0 H1).
    destruct Hbij2 as [lq [? ?]].
    exists lq.
    split; auto.
    apply find_2.
    assert (MapsTo m lq pq).
    { split. apply WF. assumption. assumption. }
    apply add_2; auto.
    intro contra.
    subst.
    contradict H.
    left.
    exists pq.
    assumption.
Qed.

Lemma remove_preserves_bij : forall dim m k v,
  layout_bijective dim m ->
  MapsTo m k v ->
  let m' := remove m k v in
  well_formed m' /\
  (forall lq, lq < dim -> lq <> k -> exists pq, find_phys m' lq = Some pq /\ pq < dim) /\
  (forall pq, pq < dim -> pq <> v -> exists lq, find_log m' pq = Some lq /\ lq < dim).
Proof.
  intros dim m k v [WF [Hbij1 Hbij2]] H m'.
  split; [| split].
  - apply remove_well_formed; auto.
  - intros.
    specialize (Hbij1 lq H0).
    destruct Hbij1 as [pq [? ?]].
    exists pq.
    split; auto.
    apply find_1.
    assert (MapsTo m lq pq).
    { split. assumption. apply WF. assumption. }
    subst m'.
    apply remove_2; auto.
    intro contra.
    subst.
    contradict H1.
    destruct H as [_ H].
    destruct H4 as [_ H4].
    rewrite H in H4.
    inversion H4.
    reflexivity.
  - intros.
    specialize (Hbij2 pq H0).
    destruct Hbij2 as [lq [? ?]].
    exists lq.
    split; auto.
    apply find_2.
    assert (MapsTo m lq pq).
    { split. apply WF. assumption. assumption. }
    subst m'.
    apply remove_2; auto.
    intro contra.
    subst.
    contradict H1.
    destruct H as [H _].
    destruct H4 as [H4 _].
    rewrite H in H4.
    inversion H4.
    reflexivity.
Qed.

Lemma swap_log_preserves_bij : forall n l pq1 pq2,
  pq1 < n -> pq2 < n ->
  layout_bijective n l ->
  layout_bijective n (swap_log l pq1 pq2).
Proof.
  intros n l pq1 pq2 Hpq1 Hpq2 Hl.
unfold swap_log.
destruct (find_log l pq1) eqn:H1; destruct (find_log l pq2) eqn:H2; auto.
- apply add_preserves_bij.
destruct Hl as [? [? ?]].
admit. (* k0 < n *)
auto.
apply add_well_formed.
apply remove_well_formed.
apply remove_well_formed.
destruct Hl as [? _]. auto.
split. apply Hl. assumption. assumption.

Admitted.


(** ** Boolean predicate to check layout_bijective *)

Definition eq_Some (o : option nat) (n : nat) := 
  match o with
  | Some x => Nat.eqb x n
  | _ => false
  end.

Fixpoint layout_bijective_b' dim n l :=
  match n with
  | O => true
  | S n => 
      match find_phys l n, find_log l n with
      | Some pq, Some lq => 
          Nat.ltb pq dim && Nat.ltb lq dim && 
          eq_Some (find_log l pq) n && eq_Some (find_phys l lq) n &&
          layout_bijective_b' dim n l
      | _, _ => false
      end
  end. 
Definition layout_bijective_b (n : nat) (l : layout) :=
  layout_bijective_b' n n l.

Lemma layout_bijective_b_implies_layout_bijective : forall n l,
  layout_bijective_b n l = true -> layout_bijective n l.
Proof.
Admitted.
(*  intros.
  assert (forall x, layout_well_formed_b' dim x m = true ->
          forall x0, x0 < x -> log2phys m x0 < dim /\ 
                         phys2log m x0 < dim /\ 
                         phys2log m (log2phys m x0) = x0 /\
                         log2phys m (phys2log m x0) = x0).
  { intros x Hx x0 Hx0.
    induction x.
    lia.
    simpl in Hx.
    apply andb_prop in Hx as [Hx Hx5].
    apply andb_prop in Hx as [Hx Hx4].
    apply andb_prop in Hx as [Hx Hx3].
    apply andb_prop in Hx as [Hx1 Hx2].
    apply Nat.ltb_lt in Hx1.
    apply Nat.ltb_lt in Hx2.
    apply beq_nat_true in Hx3.
    apply beq_nat_true in Hx4.
    specialize (IHx Hx5).
    bdestruct (x0 =? x).    
    subst. 
    repeat split; assumption.
    apply IHx.
    lia. }
  specialize (H0 dim H).
  assumption.
Qed.*)


(** ** Equality over layouts *)

Definition layout_eq n m1 m2 := 
  forall x, x < n -> get_log m1 x = get_log m2 x /\
               get_phys m1 x = get_phys m2 x.

Fixpoint layout_eqb n m1 m2 :=
  match n with
  | O => true
  | S n' => (get_log m1 n' =? get_log m2 n') &&
           (get_phys m1 n' =? get_phys m2 n') &&
           layout_eqb n' m1 m2
  end.

Lemma layout_eq_eqb_equiv : forall n m1 m2,
  layout_eq n m1 m2 <-> layout_eqb n m1 m2 = true.
Proof.
Admitted.

(** ** Trivial layout *)

Fixpoint trivial_layout n : layout :=
  match n with
  | O => empty
  | S n' => add (trivial_layout n') n' n' 
  end.

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
    apply add_well_formed; auto.
unfold In.
    admit. (* ~ In (trivial_layout n) n n *)
    intros.
    bdestruct (lq =? n).
    subst.
    exists n.
    split; try lia.
    apply find_1.
    apply add_1.
    assert (lq < n) by lia.
    specialize (H0 lq H4).
    destruct H0 as [? [? ?]].
    exists x.
    split; try lia.
    apply find_1.
    apply add_2.
auto.
lia.
apply find_3; auto.
apply H. auto.
(* symmetric case with find_log *)
Admitted.

(** ** Convert between a layout and a list (for I/O) *)

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
  add (add (add (add (add empty 4 1) 3 0) 2 3) 1 2) 0 4.

(* Expected output: [Some 0; Some 1; Some 2; Some 3; Some 4] *)
Compute (layout_to_list 5 (trivial_layout 5)).
(* Expected output: [Some 3; Some 4; Some 1; Some 2; Some 0] *)
Compute (layout_to_list 5 test_layout).
(* Expected output: [Some 0; Some 1; Some 2; Some 3; Some 4] *)
Compute (layout_to_list 5 (list_to_layout (0 :: 1 :: 2 :: 3 :: 4 :: []))).
(* Expected output: [Some 3; Some 4; Some 1; Some 2; Some 0] *)
Compute (layout_to_list 5 (list_to_layout (3 :: 4 :: 1 :: 2 :: 0 :: []))).

(** TODOs: 
  - prove that list_to_layout and layout_to_list are inverses
  - prove that a bounded list with no duplicates produces a bijective layout
*)
