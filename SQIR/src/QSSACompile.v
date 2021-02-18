Require Import VectorStates UnitaryOps Coq.btauto.Btauto Strings.String.
Require Import Arith.
Require Import ZArith.
Require Import ZArith.BinIntDef.
Require Import RCIRplus.
Require Import QSSA.

Local Open Scope rexp.
Local Open Scope nat_scope.

(* all calculations are assumed to perform in terms of two's complemetn. *)
Definition majb a b c := (a && b) ⊕ (b && c) ⊕ (a && c).

Definition MAJ a b c := RCNOT c b ; RCNOT c a ; RCCX a b c.
Definition UMA a b c := RCCX a b c ; RCNOT c a ; RCNOT a b.

Lemma MAJ_WF :
  forall hr a b c,
    a <> b -> b <> c -> a <> c ->
    well_formed_mem hr ->
    well_defined hr a -> well_defined hr b -> well_defined hr c ->
    WF_rexp hr (MAJ c b a).
Proof.
  intros. unfold MAJ. constructor. constructor.
  apply RCNOT_WF; assumption.
  apply RCNOT_WF; assumption.
  apply RCCX_WF.
  intros R. rewrite R in H0. contradiction.
  intros R. subst. contradiction.
  intros R. subst. contradiction. 
  1 - 4: assumption.  
Qed.

Lemma UMA_WF :
  forall hr a b c,
    a <> b -> b <> c -> a <> c ->
    well_formed_mem hr ->
    well_defined hr a -> well_defined hr b -> well_defined hr c ->
    WF_rexp hr (UMA c b a).
Proof.
  intros. unfold UMA. constructor. constructor.
  apply RCCX_WF.
  intros R. rewrite R in H0. contradiction.
  intros R. subst. contradiction.
  intros R. subst. contradiction. 
  1 - 4: assumption.  
  apply RCNOT_WF; assumption.
  apply RCNOT_WF.
  intros R. subst. contradiction.
  1 - 3 : assumption. 
Qed.

Lemma MAJ_correct :
  forall hr a b c fa fb fc,
    a <> b -> b <> c -> a <> c ->
    get hr a = Some fa -> get hr b = Some fb -> get hr c = Some fc ->
    estep hr (MAJ c b a) (hr[ a |-> majb fa fb fc][b |-> fb ⊕ fa][c |-> fc ⊕ fa]).
(*Admitted. 
(* The following proof works, but too slow. Admitted when debugging. *)*)
Proof.
  intros hr a b c fa fb fc Hab' Hbc' Hac' Vfa Vfb Vfc. 
  unfold MAJ.
  eapply seq_rule. 
  eapply seq_rule. 
  apply RCNOT_correct. assumption.
  apply Vfa. apply Vfb.
  apply RCNOT_correct. assumption.
  rewrite get_neq. apply Vfa. assumption.
  rewrite get_neq. apply Vfc.
  intros R. subst. contradiction.
  assert (c <> b). intros R. subst. contradiction.
  assert (b <> a). intros R. subst. contradiction.
  assert (c <> a). intros R. subst. contradiction.
  assert (get ((hr [b |-> fb ⊕ fa]) [c |-> fc ⊕ fa]) c = Some (fc ⊕ fa)).
  apply get_1. rewrite get_neq. rewrite Vfc. easy. assumption.
  assert (get ((hr [b |-> fb ⊕ fa]) [c |-> fc ⊕ fa]) b = Some (fb ⊕ fa)).
  rewrite get_index_neq. apply get_1. rewrite get_neq.
  rewrite Vfb. easy. 1-2:assumption.
  rewrite Vfc. easy.
  rewrite Vfb. easy.
  assert ( get ((hr [b |-> fb ⊕ fa]) [c |-> fc ⊕ fa]) a = Some fa).
  rewrite get_neq. rewrite get_neq. 1 - 3:assumption.
  specialize (RCCX_correct ((hr [b |-> fb ⊕ fa]) [c |-> fc ⊕ fa]) c b a (fc ⊕ fa) (fb ⊕ fa) fa
                 H H0 H1 H2 H3 H4) as eq1.
  assert (fa ⊕ (fb ⊕ fa && fc ⊕ fa) =  majb fa fb fc).
  unfold majb. btauto.
  rewrite H5 in eq1.
  rewrite (get_index_neq (hr [b |-> fb ⊕ fa])) in eq1.
  rewrite (get_index_neq hr a b) in eq1.
  assumption. assumption. 
  rewrite Vfa. easy.
  rewrite Vfb. easy.
  assumption.
  rewrite get_neq. rewrite Vfa. easy.
  assumption.
  rewrite get_neq. rewrite Vfc. easy.
  assumption.
Qed.

Lemma UMA_correct_partial :
  forall hr' a b c fa fb fc,
    a <> b -> b <> c -> a <> c ->
    get hr' a = Some (majb fa fb fc) ->
    get hr' b = Some (fb ⊕ fa) -> get hr' c = Some (fc ⊕ fa) ->
    estep hr' (UMA c b a) (((hr'[a |-> fa])[b |-> fa ⊕ fb ⊕ fc])[c |-> fc]).
Proof.
  intros. unfold UMA.
  assert (c <> b). intros R. subst. contradiction.
  assert (b <> a). intros R. subst. contradiction.
  assert (c <> a). intros R. subst. contradiction.
  eapply seq_rule.
  eapply seq_rule.
  apply RCCX_correct; try assumption.
  apply H4. apply H3. apply H2.
  apply RCNOT_correct; try assumption.
  rewrite get_1. reflexivity.
  rewrite H2. easy.
  rewrite get_neq; try assumption.
  apply H4.
  assert (majb fa fb fc ⊕ (fb ⊕ fa && fc ⊕ fa) = fa).
  unfold majb. btauto.
  rewrite H8.
  assert ((fc ⊕ fa) ⊕ fa = fc) by btauto.
  rewrite H9.
  assert (get ((hr' [a |-> fa]) [c |-> fc]) c = Some fc).
  rewrite get_1. reflexivity.
  rewrite get_neq. rewrite H4. easy.
  assumption.
  assert (get ((hr' [a |-> fa]) [c |-> fc]) b = Some (fb ⊕ fa)).
  rewrite get_neq; try assumption. rewrite get_neq; try assumption.
  specialize (RCNOT_correct ((hr' [a |-> fa]) [c |-> fc]) c b fc (fb ⊕ fa) H5 H10 H11) as eq1.
  assert ((fb ⊕ fa) ⊕ fc = (fa ⊕ fb) ⊕ fc) by btauto.
  rewrite H12 in eq1.
  rewrite (get_index_neq (hr' [a |-> fa])).
  1-2:assumption.
  rewrite get_neq. rewrite H4. easy.
  assumption.
  rewrite get_neq. rewrite H3. easy.
  assumption.
Qed.

(* The following defines n-bits MAJ and UMA circuit. 
   Eventually, MAJ;UMA circuit takes [x][y] and produce [x][(x+y) % 2 ^ n] *)
Fixpoint MAJseq (i:nat) (c:pos) (x:avar) (y:avar) : rexp :=
  match i with
  | 0 => MAJ c (y,0%nat) (x,0)
  | S i' => MAJseq i' c x y; MAJ (x,i') (y,i) (x,i)
  end.

(*
Definition MAJseq n := MAJseq' (n - 1) n 0.
*)

Lemma MAJseq_WF' :
  forall i n hr c x y,
    i <= n -> (fst c) <> x -> x <> y -> (fst c <> y) ->
    well_formed_mem hr ->
    well_defined hr c -> well_defined_all hr x (n+1)
   ->  well_defined_all hr y (n+1) ->
    WF_rexp hr (MAJseq i c x y).
Proof.
  induction i.
  intros. simpl.
  destruct c.
  apply MAJ_WF.
  intros R. inv R. contradiction.
  intros R. inv R. contradiction.
  intros R. inv R. contradiction.
  assumption.
  unfold well_defined_all in *.
  apply H5. lia.
  apply H6. lia. assumption.
  intros. simpl. apply WF_rseq. 
  apply (IHi n).
  lia. 1 - 7:assumption. 
  unfold well_defined_all in *.
  apply MAJ_WF.
  intros R. inv R. contradiction.
  intros R. inv R. contradiction.
  intros R. inv R. lia.
  assumption.
  apply H5. lia.
  apply H6. lia.
  apply H5. lia.
Qed.

Lemma MAJseq_WF : forall n hr c x y,
    (fst c) <> x -> x <> y -> (fst c <> y) ->
    well_formed_mem hr ->
    well_defined hr c -> well_defined_all hr x (n+1)
   ->  well_defined_all hr y (n+1) ->
    WF_rexp hr (MAJseq n c x y).
Proof.
 intros. apply (MAJseq_WF' n n).
 lia. 1-7:assumption.
Qed.

Fixpoint UMAseq (i:nat) (c:pos) (x:avar) (y:avar) : rexp :=
  match i with
  | 0 => UMA c (y,0) (x,0)
  | S i' => UMA (x,i') (y, i) (x, i); UMAseq i' c x y
  end.

Lemma UMAseq_WF' :
  forall i n hr c x y,
    i <= n -> (fst c) <> x -> x <> y -> (fst c <> y) ->
    well_formed_mem hr ->
    well_defined hr c -> well_defined_all hr x (n+1)
   ->  well_defined_all hr y (n+1) ->
    WF_rexp hr (UMAseq i c x y).
Proof.
  induction i.
  intros. simpl.
  destruct c.
  apply UMA_WF.
  intros R. inv R. contradiction.
  intros R. inv R. contradiction.
  intros R. inv R. contradiction.
  assumption.
  unfold well_defined_all in *.
  apply H5. lia.
  apply H6. lia. assumption.
  intros. simpl. apply WF_rseq. 
  apply UMA_WF.
  intros R. inv R. contradiction.
  intros R. inv R. contradiction.
  intros R. inv R. lia.
  assumption.
  apply H5. lia.
  apply H6. lia.
  apply H5. lia.
  apply (IHi n).
  lia. 1 - 7:assumption. 
Qed.

Lemma UMAseq_WF : forall n hr c x y,
    (fst c) <> x -> x <> y -> (fst c <> y) ->
    well_formed_mem hr ->
    well_defined hr c -> well_defined_all hr x (n+1)
   ->  well_defined_all hr y (n+1) ->
    WF_rexp hr (UMAseq n c x y).
Proof.
 intros. apply (UMAseq_WF' n n).
 lia. 1-7:assumption.
Qed.

Notation "{ x ,, y ,, .. ,, z }" := (cons x (cons y .. (cons z nil) ..)).

(* The adder is a two's complement adder, where the high bit is not a indicating of negative number,
   but an indication on whether or not the result of the computation overflows.
    We assume that the input are two n + 1 bit numbers, a carry test bit, and a high test bit.
    The adder is implemented as an RCIR+ function. The expression corrsponded in QSSA is r = x + y
    where the input are x and y, and the function will generate the high-bit
    the input number n is the number of bits in x and y.  *)
Definition add_aux {A:Type} (n:nat) (c:ivar) (x:evar) (y:evar) (r:evar) :=
    Fun A {(Q (n+1), x) ,, (Q (n+1), y)} r [(Q 1, c)] 
          (MAJseq n (lvar c,0) (gvar x) (gvar y); UMAseq n (lvar c,0) (gvar x) (gvar y)) (gvar y).

Lemma empty_regs_empty : Regs.is_empty (empty_regs) = true.
Proof.
 unfold empty_regs, Regs.is_empty,Regs.Raw.is_empty.
 destruct (Regs.this (Regs.empty (rtype * (nat -> bool)))) eqn:eq1.
 reflexivity. unfold Regs.this,Regs.empty,Regs.Raw.empty in eq1.
 inv eq1.
Qed.

Lemma empty_regs_no_map : forall x v, ~ Regs.MapsTo x v empty_regs.
Proof.
 intros.
 specialize (empty_regs_empty) as eq1.
 apply Regs.is_empty_2 in eq1.
 unfold Regs.Empty,Regs.Raw.Empty in eq1.
 apply eq1.
Qed.

Lemma add_aux_WF {A:Type}: forall n h c x y r,
    x <> y -> y <> r -> r <> x ->
    well_formed_heap h -> (exists v1, Heap.MapsTo x (Q (n+1), v1) h)
   ->  (exists v2, Heap.MapsTo y (Q (n+1), v2) h) 
   -> (exists v3, Heap.MapsTo r (Q (n+1), v3) h)  ->
    @WF_rfun A h (add_aux n c x y r) h.
Proof.
 intros. unfold add_aux.
 destruct H3. destruct H4. destruct H5.
 eapply WF_fun.
 apply H5. reflexivity.
 unfold gen_regs.
 unfold well_formed_regs.
 intros. 
 bdestruct (x3 =? c).
 subst.
 apply Regs.find_1 in H6.
 rewrite Regs.find_add in H6.
 inv H6. lia.
 apply Regs.add_3 in H6.
 apply empty_regs_no_map in H6.
 inv H6.
 lia.
 unfold lookup.
 apply Heap.find_1.
 apply Heap.remove_2. lia.
 apply H4.
 apply WF_rseq.
 apply MAJseq_WF.
 easy. intros R. inv R. contradiction.
 easy.
 unfold well_formed_mem.
 split. simpl.
 unfold well_formed_heap in *.
 intros.
 bdestruct (x3 =? r).
 symmetry in H7.
 apply (@Heap.remove_1 (rtype * (nat -> bool)) h) in H7.
 unfold Heap.In,Heap.Raw.PX.In in H7.
 destruct H7. exists (Q n0, g). assumption.
 apply Heap.remove_3 in H6.
 apply H2 in H6. assumption.
 unfold well_formed_regs.
 intros. 
 simpl in *.
 bdestruct (x3 =? c).
 subst.
 apply Regs.find_1 in H6.
 rewrite Regs.find_add in H6.
 inv H6. lia.
 apply Regs.add_3 in H6.
 apply empty_regs_no_map in H6.
 inv H6. lia.
 eapply (well_defined_regs (Heap.remove (elt:=rtype * (nat -> bool)) r h) (gen_regs ((Q 1, c)::nil)) c 0 1).
 unfold gen_regs.
 apply Regs.add_1. reflexivity. lia.
 unfold well_defined_all.
 intros. 
 eapply well_defined_heap.
 apply Heap.remove_2.
 lia. apply H3. assumption.
 unfold well_defined_all.
 intros. 
 eapply well_defined_heap.
 apply Heap.remove_2.
 lia. apply H4. assumption.
 apply UMAseq_WF.
 easy. intros R. inv R. contradiction.
 easy.
 unfold well_formed_mem.
 split. simpl.
 unfold well_formed_heap in *.
 intros.
 bdestruct (x3 =? r).
 symmetry in H7.
 apply (@Heap.remove_1 (rtype * (nat -> bool)) h) in H7.
 unfold Heap.In,Heap.Raw.PX.In in H7.
 destruct H7. exists (Q n0, g). assumption.
 apply Heap.remove_3 in H6.
 apply H2 in H6. assumption.
 unfold well_formed_regs.
 intros. 
 simpl in *.
 bdestruct (x3 =? c).
 subst.
 apply Regs.find_1 in H6.
 rewrite Regs.find_add in H6.
 inv H6. lia.
 apply Regs.add_3 in H6.
 apply empty_regs_no_map in H6.
 inv H6. lia.
 eapply (well_defined_regs (Heap.remove (elt:=rtype * (nat -> bool)) r h) (gen_regs ((Q 1, c)::nil)) c 0 1).
 unfold gen_regs.
 apply Regs.add_1. reflexivity. lia.
 unfold well_defined_all.
 intros. 
 eapply well_defined_heap.
 apply Heap.remove_2.
 lia. apply H3. assumption.
 unfold well_defined_all.
 intros. 
 eapply well_defined_heap.
 apply Heap.remove_2.
 lia. apply H4. assumption.
 simpl.
 destruct (Heap.find (elt:=rtype * (nat -> bool)) r h) eqn:eq1.
 destruct p. destruct r0.
 split.
 apply Heap.find_1 in H5. rewrite H5 in eq1.
 inv eq1. reflexivity.
 destruct (Heap.find (elt:=rtype * (nat -> bool)) x h) eqn:eq2.
 destruct p. destruct r0.
 split.
 apply Heap.find_1 in H3. rewrite H3 in eq2.
 inv eq2. reflexivity.
 destruct (Heap.find (elt:=rtype * (nat -> bool)) y h) eqn:eq3.
 destruct p. destruct r0.
 split.
 apply Heap.find_1 in H4. rewrite H4 in eq3.
 inv eq3. reflexivity. easy.
 apply Heap.find_1 in H4. rewrite H4 in eq3. inv eq3.
 apply Heap.find_1 in H3. rewrite H3 in eq2. inv eq2.
 apply Heap.find_1 in H5. rewrite H5 in eq1. inv eq1.
Qed.

Definition adder {A : Type} (n:nat) (r:evar) (x:evar) (y:evar) (c:ivar) : list (rfun A) := 
        { Cast A (Q n) x (Q (n+1)) ,, Cast A (Q n) y (Q (n+1)) ,, 
                       Cast A (Q n) r (Q (n+1)) ,, add_aux n c x y r }.


Lemma adder_WF {A:Type}: forall n h r x y c,
    0 < n -> x <> y -> y <> r -> r <> x ->
    well_formed_heap h -> (exists v1, Heap.MapsTo x (Q n, v1) h)
   ->  (exists v2, Heap.MapsTo y (Q n, v2) h) 
   -> (exists v3, Heap.MapsTo r (Q n, v3) h)  ->
    (exists h', @WF_rfun_list A h (adder n r x y c) h').
Proof.
 intros. unfold adder.
 destruct H4. destruct H5. destruct H6.
 exists (update_type_heap (update_type_heap (update_type_heap h x (Q (n+1))) y (Q (n+1))) r (Q (n+1))).
 eapply WF_many.
 eapply WF_cast.
 apply H4. assumption.
 lia.
 eapply WF_many.
 eapply WF_cast.
 unfold update_type_heap.
 apply Heap.add_2. lia.
 apply H5.
 assumption. lia.
 eapply WF_many.
 eapply WF_cast.
 unfold update_type_heap.
 apply Heap.add_2. lia.
 apply Heap.add_2. lia.
 apply H6.
 assumption. lia.
 eapply WF_many.
 apply add_aux_WF.
 1 - 3:lia.
 unfold update_type_heap.
 unfold well_formed_heap in *.
 intros. 
 bdestruct (x3 =? r). subst.
 apply Heap.mapsto_add1 in H7.
 inv H7. lia.
 apply Heap.add_3 in H7.
 bdestruct (x3 =? y). subst.
 apply Heap.mapsto_add1 in H7.
 inv H7. lia.
 apply Heap.add_3 in H7.
 bdestruct (x3 =? x). subst.
 apply Heap.mapsto_add1 in H7.
 inv H7. lia.
 apply Heap.add_3 in H7.
 apply H3 in H7. assumption.
 1 - 3: lia.
 unfold update_type_heap.
 exists allfalse.
 apply Heap.add_2. lia.
 apply Heap.add_2. lia.
 apply Heap.add_1. reflexivity.
 unfold update_type_heap.
 exists allfalse.
 apply Heap.add_2. lia.
 apply Heap.add_1. reflexivity.
 unfold update_type_heap.
 exists allfalse.
 apply Heap.add_1. reflexivity.
 apply WF_empty.
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
(* Admitted.
(* The following proof works, but too slow. Admitted when debugging. *) *)
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
    bcexec (MAJseq' i n 0) (c ` b1 ` fb_push_n n f (fb_push_n n g h)) = (c ⊕ (f 0)) ` b1 ` fb_push_n n (msma i c f g) (fb_push_n n (msmb i c f g) h).
(* Admitted.
(* The following proof works, but too slow. Admitted when debugging. *) *)
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
    bcexec (UMAseq' i n 0) ((c ⊕ (f 0)) ` b1 ` fb_push_n n (msma i c f g) (fb_push_n n (msmc i c f g) h)) = c ` b1 ` fb_push_n n f (fb_push_n n (sumfb c f g) h).
(* Admitted.
(* The following proof works, but too slow. Admitted when debugging. *) *)
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
