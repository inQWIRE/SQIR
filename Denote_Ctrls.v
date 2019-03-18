Require Export SQIMP.
Require Export Quantum.
Require Import List.

Local Opaque WF_Matrix.

Class Denote source target := {denote : source -> target}.

Notation "⟦ s ⟧" := (denote s) (at level 10).

(** Unitary Denotation **)

Fixpoint denote_unitary {n} (U : Unitary n) : Square (2^n) :=
  match U with  
  | _H          => hadamard 
  | _X          => σx
  | _Y          => σy
  | _Z          => σz
  | _R_ ϕ       => phase_shift ϕ
  | ctrl g     => control (denote_unitary g)
  end.

Instance Denote_Unitary n : Denote (Unitary n) (Square (2^n)) := 
    {| denote := denote_unitary |}.

Lemma WF_Matrix_U : forall {n} (U : Unitary n), 
      WF_Matrix (2^n) (2^n) (⟦U⟧).
Proof.
  induction U; simpl; auto with wf_db.
Qed.
Hint Resolve WF_Matrix_U : wf_db.

Lemma unitary_gate_unitary : forall {n} (U : Unitary n), WF_Unitary (⟦U⟧).
Proof.
  induction U.
  + apply H_unitary.
  + apply σx_unitary.
  + apply σy_unitary.
  + apply σz_unitary.
  + apply phase_unitary.
  + simpl. apply control_unitary; assumption. 
Qed.

(*
Lemma denote_unitary_transpose : forall {n} (U : Unitary n), ⟦trans U⟧ = ⟦U⟧†.
Proof.
  induction U; simpl; Msimpl; trivial. 
  - simpl_rewrite IHU. setoid_rewrite control_adjoint. easy.
  - simpl_rewrite IHU. setoid_rewrite control_adjoint. easy.
Qed.
*)

(***********************************)
(** Applying Unitaries to Systems **)
(***********************************)

Fixpoint ctrls_to_list {n} (lb : list bool) (l : list nat) (g : Unitary n) {struct g}: 
  (nat * list bool * Square 2) :=
  match g with
  | ctrl g'     => match l with 
                  | n :: l' => let (res,u) := ctrls_to_list lb l' g' in
                              let (k,lb') := res in
                              (k,update_at lb' n true, u)  
                  | _       => (O,[],Zero)
                  end
  | u           => match l with
                  | k :: l' => (k,lb,⟦u⟧)
                  | _       => (O,[],Zero)
                  end
  end.

Fixpoint ctrl_list_to_unitary_r (r : list bool) (u : Square 2) : 
  (Square (2^(length r + 1))) := 
  match r with 
  | false :: r' =>  ctrl_list_to_unitary_r r' u ⊗ I 2
  | true  :: r' =>  ctrl_list_to_unitary_r r' u ⊗ ∣1⟩⟨1∣ .+ I _ ⊗ ∣0⟩⟨0∣
  | []          => u
  end.

Fixpoint ctrl_list_to_unitary (l r : list bool) (u : Square 2) : 
  (Square (2^(length l + length r + 1))) := 
  match l with 
  | false :: l' => I 2 ⊗ ctrl_list_to_unitary l' r u
  | true  :: l' => ∣1⟩⟨1∣ ⊗ ctrl_list_to_unitary l' r u .+ ∣0⟩⟨0∣ ⊗ I _
  | []          => ctrl_list_to_unitary_r r u
  end.

Definition denote_ctrls {n} (dim : nat) (g : Unitary n) (l : list nat) : Square (2^dim) := 
  let (res, u) := ctrls_to_list (repeat false dim) l g in
  let (k, lb) := res in
  let ll := firstn k lb in
  let lr := rev (skipn (S k) lb) in 
  ctrl_list_to_unitary ll lr u. 

(* New in-place version of apply_U *)

Definition apply_unitary {n} (dim : nat) (U : Unitary n) (l : list nat) : Square (2^dim) :=
  match n with
  | 1 => let k := (hd O l) in
            I (2^k) ⊗ ⟦U⟧ ⊗ I (2 ^ (dim - k -1))
  | _ => denote_ctrls dim U l
  end.

Definition apply_U {n} (dim : nat) (U : Unitary n) (l : list nat) 
  : Superoperator (2^dim) (2^dim) := super (apply_unitary dim U l).

(* In case we add other multi-qubit unitaries 
Fixpoint apply_U {n} (dim : nat) (U : Unitary W) (l : list nat) 
           : Superoperator (2^dim) (2^dim) :=
  match U with
  | _H          => apply_to_first (apply_qubit_unitary hadamard) l
  | _X          => apply_to_first (apply_qubit_unitary σx) l
  | _Y          => apply_to_first (apply_qubit_unitary σy) l
  | _Z          => apply_to_first (apply_qubit_unitary σz) l
  | _R_ ϕ       => apply_to_first (apply_qubit_unitary (phase_shift ϕ)) l
  | ctrl g      => super (denote_ctrls n U l)  
  end.
*)

(***********************************)
(* Lemmas about applying unitaries *)
(***********************************)

Lemma ctrl_list_to_unitary_r_false : forall n (u : Matrix 2 2),
  ctrl_list_to_unitary_r (repeat false n) u = u ⊗ I  (2^n).
Proof.
  induction n; intros.
  - simpl. Msimpl. reflexivity.
  - intros.
    simpl.
    rewrite IHn.
    setoid_rewrite kron_assoc.
    rewrite id_kron.
    unify_pows_two.
    reflexivity.
Qed.

Lemma ctrl_list_to_unitary_false : forall m n (u : Matrix 2 2),
  WF_Matrix 2 2 u ->
  ctrl_list_to_unitary (repeat false m) (repeat false n) u = I  (2^m) ⊗ u ⊗ I  (2^n).
Proof.
  induction m; intros.
  - simpl. Msimpl. apply ctrl_list_to_unitary_r_false. 
  - simpl.
    rewrite IHm by easy.
    Msimpl.
    repeat rewrite repeat_length.
    match goal with
    | |- context [ @kron ?a1 ?a2 ?bc1 ?bc2 ?A (@kron ?b1 ?b2 ?c1 ?c2 ?B ?C)] => idtac B; 
      replace bc1 with (b1 * c1)%nat by (unify_pows_two); 
      replace bc2 with (b2 * c2)%nat by (unify_pows_two);
      rewrite <- (kron_assoc a1 a2 b1 b2 c1 c2 A B C)
    end.
    match goal with
    | |- context [ @kron ?a1 ?a2 ?bc1 ?bc2 ?A (@kron ?b1 ?b2 ?c1 ?c2 ?B ?C)] => idtac B; 
      replace bc1 with (b1 * c1)%nat by (unify_pows_two); 
      replace bc2 with (b2 * c2)%nat by (unify_pows_two);
      rewrite <- (kron_assoc a1 a2 b1 b2 c1 c2 A B C)
    end.
    rewrite id_kron.
    unify_pows_two.
    repeat rewrite Nat.add_1_r.
    reflexivity.
Qed.
         
Lemma ctrls_to_list_empty  : forall n lb u, @ctrls_to_list n lb [] u = (O, [], Zero).
Proof. destruct u; easy. Qed.  

Lemma denote_ctrls_empty : forall n (dim : nat) (u : Unitary n),
  denote_ctrls n u [] = Zero.
Proof. destruct u; cbv; easy. Qed.

Lemma denote_ctrls_qubit : forall dim (u : Unitary 1) k,
  (k < dim)%nat ->
  denote_ctrls dim u [k] = I (2^k) ⊗ ⟦u⟧ ⊗ I  (2^(dim-k-1)).
Proof.
  intros dim u k L.
  remember 1%nat as n.   
  destruct u.
  Opaque rev skipn.
  1-5: unfold denote_ctrls; simpl;
       rewrite firstn_repeat_le, skipn_repeat, rev_repeat by omega;
       rewrite ctrl_list_to_unitary_false; auto with wf_db;
       rewrite Nat.sub_succ_r, Nat.sub_1_r;
       reflexivity.
  inversion Heqn. subst. inversion u.  
Qed.

Lemma ctrl_list_to_unitary_r_unitary : forall r (u : Square 2),
    WF_Unitary u -> WF_Unitary (ctrl_list_to_unitary_r r u).
Proof.
  intros r u Uu.
  induction r; auto.
  simpl.
  destruct a.
  - simpl.
    assert (H : forall n (U : Square n), WF_Unitary U -> WF_Unitary (U ⊗ ∣1⟩⟨1∣ .+ I n ⊗ ∣0⟩⟨0∣)).
    intros n U [WFU UU].
    unfold WF_Unitary.
    split; auto with wf_db.
    Msimpl.
    rewrite Mmult_plus_distr_r, Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_l.
    Msimpl.
    rewrite UU.
    replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2) by solve_matrix.
    replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2) by solve_matrix.
    repeat rewrite kron_0_r.
    rewrite Mplus_0_r, Mplus_0_l.
    rewrite <- kron_plus_distr_l.
    replace (∣1⟩⟨1∣ × ∣1⟩⟨1∣ .+ ∣0⟩⟨0∣ × ∣0⟩⟨0∣) with (I 2) by solve_matrix.
    rewrite id_kron.
    reflexivity.
    specialize (H _ (ctrl_list_to_unitary_r r u)).
    rewrite Nat.mul_comm in H.
    apply H.
    apply IHr.
  - specialize (kron_unitary _ (I 2) IHr) as H.
    rewrite Nat.mul_comm in H.
    apply H.
    apply id_unitary. 
Qed.

Lemma ctrl_list_to_unitary_unitary : forall l r (u : Square 2), WF_Unitary u ->
                                                           WF_Unitary (ctrl_list_to_unitary l r u).
Proof.
  intros l r u Uu.
  induction l.
  - simpl. apply ctrl_list_to_unitary_r_unitary. easy.
  - simpl.
    destruct a.
    + simpl.
      assert (H : forall n (U : Square n), WF_Unitary U -> WF_Unitary (∣1⟩⟨1∣ ⊗ U .+ ∣0⟩⟨0∣ ⊗ (I n))).
      intros n U [WFU UU].
      unfold WF_Unitary.
      split; auto with wf_db.
      Msimpl.
      rewrite Mmult_plus_distr_l, Mmult_plus_distr_r.
      rewrite Mmult_plus_distr_r.
      Msimpl.
      setoid_rewrite kron_mixed_product.
      rewrite UU.
      replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2) by solve_matrix.
      replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2) by solve_matrix.
      repeat rewrite kron_0_l.
      rewrite Mplus_0_r, Mplus_0_l.
      Msimpl. 
      rewrite <- kron_plus_distr_r.
      replace (∣1⟩⟨1∣ × ∣1⟩⟨1∣ .+ ∣0⟩⟨0∣ × ∣0⟩⟨0∣) with (I 2) by solve_matrix.
      rewrite id_kron.
      reflexivity.
      specialize (H _ (ctrl_list_to_unitary l r u)).
      apply H.
      apply IHl.
    + specialize (kron_unitary _ _ (id_unitary 2) IHl) as H.
      apply H.
Qed.

Lemma ctrls_to_list_spec : forall n l (g : Unitary n) k lb lb' u, 
  (length l = n)%nat ->
  ctrls_to_list lb l g = (k, lb', u) ->
  @WF_Unitary 2 u /\ length lb' = length lb /\ In k l.
Proof.
  intros n l g.
  gen l.
  induction g; simpl in *; intros l k lb lb' u L H.
  - destruct l; inversion L. inversion H; subst. split. rewrite H1. apply H_unitary. 
    split. easy. constructor. easy.
  - destruct l; inversion L. inversion H; subst. split. rewrite H1. apply σx_unitary. 
    split. easy. constructor. easy.
  - destruct l; inversion L. inversion H; subst. split. rewrite H1. apply σy_unitary. 
    split. easy. constructor. easy.
  - destruct l; inversion L. inversion H; subst. split. rewrite H1. apply σz_unitary. 
    split. easy. constructor. easy.
  - destruct l; inversion L. inversion H; subst. split. rewrite H1. 
    apply phase_unitary. split. easy. constructor. easy.
  - destruct l; inversion L.
    destruct (ctrls_to_list lb l g) as [[k' lb''] u'] eqn:E.
    inversion H; subst.
    rewrite update_length.    
    specialize (IHg l k lb lb'' u eq_refl E) as [U [LE I]].
    split; [|split]; trivial.
    right. easy.
Qed.    

Lemma denote_ctrls_unitary : forall n dim (g : Unitary n) l, 
    (forall x, In x l -> x < dim)%nat -> 
    (length l = n)%nat ->
    WF_Unitary (denote_ctrls dim g l).
Proof.
  intros n dim g l H H0.
  unfold denote_ctrls. simpl.
  destruct (ctrls_to_list (repeat false dim) l g) as [[k lb] u] eqn:E.
  apply ctrls_to_list_spec in E as [Uu [L I]]; trivial.
  specialize (H k I).
  specialize (ctrl_list_to_unitary_unitary (firstn k lb) (rev (skipn (S k) lb)) u Uu) 
    as U.  
  assert (E: (length (firstn k lb) + length (rev (skipn (S k) lb)) + 1 = dim)%nat).
  rewrite firstn_length_le.
  rewrite rev_length.
  rewrite skipn_length.
  rewrite L, repeat_length. omega.
  rewrite L, repeat_length. omega.
  rewrite E in U.
  apply U.
Qed.

(*
Lemma denote_ctrls_transpose_qubit : forall (n : nat) (u : Unitary Qubit) (li : list nat),
  denote_ctrls n (trans u) li = (denote_ctrls n u li)†.
Proof.
  intros.
  destruct li as [| k li].
  rewrite 2 denote_ctrls_empty. rewrite zero_adjoint_eq. easy.
  dependent destruction u.
  - simpl.
    unfold denote_ctrls. subst; clear.
    unfold ctrls_to_list.
    rewrite skipn_repeat, rev_repeat, firstn_repeat.
    simpl. rewrite ctrl_list_to_unitary_false by (auto with wf_db).    
    repeat setoid_rewrite kron_adjoint.
    Msimpl.
    reflexivity.
  - simpl.
    unfold denote_ctrls. subst; clear.
    unfold ctrls_to_list.
    rewrite skipn_repeat, rev_repeat, firstn_repeat.
    simpl. rewrite ctrl_list_to_unitary_false by (auto with wf_db).    
    repeat setoid_rewrite kron_adjoint.
    Msimpl.
    reflexivity.
  - simpl.
    unfold denote_ctrls. subst; clear.
    unfold ctrls_to_list.
    rewrite skipn_repeat, rev_repeat, firstn_repeat.
    simpl. rewrite ctrl_list_to_unitary_false by (auto with wf_db).    
    repeat setoid_rewrite kron_adjoint.
    Msimpl.
    reflexivity.
  - simpl.
    unfold denote_ctrls. subst; clear.
    unfold ctrls_to_list.
    rewrite skipn_repeat, rev_repeat, firstn_repeat.
    simpl. rewrite ctrl_list_to_unitary_false by (auto with wf_db).    
    repeat setoid_rewrite kron_adjoint.
    Msimpl.
    reflexivity.
  - simpl.
    unfold denote_ctrls. subst; clear.
    unfold ctrls_to_list.
    rewrite skipn_repeat, rev_repeat, firstn_repeat.
    simpl. rewrite 2 ctrl_list_to_unitary_false by (auto with wf_db).    
    repeat setoid_rewrite kron_adjoint.
    Msimpl.
    reflexivity.
Qed.

Lemma ctrls_to_list_transpose : forall W lb li (u : Unitary W) n lb' u', 
  ctrls_to_list lb li u = (n, lb', u') ->
  ctrls_to_list lb li (trans u) = (n, lb', u'†).
Proof.                            
  induction W; intros lb li u n lb' u' H; try solve [inversion u].
  - destruct li as [| k li].
    rewrite ctrls_to_list_empty in *.
    inversion H; subst. rewrite zero_adjoint_eq. easy.
    dependent destruction u.
    + simpl in *.
      inversion H; subst.
      Msimpl. easy.
    + simpl in *.
      inversion H; subst.
      Msimpl. easy.
    + simpl in *.
      inversion H; subst.
      Msimpl. easy.
    + simpl in *.
      inversion H; subst.
      Msimpl. easy.
    + simpl in *.
      inversion H; subst.
      Msimpl. easy.
  - clear IHW1.
    destruct li as [| k li].
    rewrite ctrls_to_list_empty in *.
    inversion H; subst. rewrite zero_adjoint_eq. easy.
    dependent destruction u.
    + simpl in *.
      destruct (ctrls_to_list lb li u) as [[j l] v] eqn:E.
      apply IHW2 in E. rewrite E.
      inversion H; subst.
      easy.
    + simpl in *.
      destruct (ctrls_to_list lb li u) as [[j l] v] eqn:E.
      apply IHW2 in E. rewrite E.
      inversion H; subst.
      easy.
Qed.

Lemma ctrl_list_to_unitary_transpose : forall l r u, 
  ctrl_list_to_unitary l r (u†) = (ctrl_list_to_unitary l r u)†.
Proof.                            
  intros l r u.
  induction l.
  simpl.
  - induction r; trivial.
    simpl.
    destruct a.
    + rewrite IHr.
      match goal with
      | [|- _ = (?A .+ ?B)† ] => setoid_rewrite (Mplus_adjoint _ _ A B)
      end.
      Msimpl.
      reflexivity.
    + rewrite IHr.
      setoid_rewrite kron_adjoint.
      Msimpl.
      reflexivity.
  - simpl.
    destruct a.
    + Msimpl. rewrite IHl. easy.
    + Msimpl. rewrite IHl. easy.
Qed.

Lemma denote_ctrls_transpose: forall W (n : nat) (u : Unitary W) li, 
  denote_ctrls n (trans u) li = (denote_ctrls n u li) †.
Proof.
  intros.
  unfold denote_ctrls.
  destruct (ctrls_to_list (repeat false n) li u) as [[j l] v] eqn:E.
  apply ctrls_to_list_transpose in E.
  rewrite E.
  rewrite ctrl_list_to_unitary_transpose.
  easy.
Qed.
 *)

Lemma apply_unitary_unitary : forall n dim (u : Unitary n) l,
    length l = n ->
    (forall x, In x l -> x < dim)%nat -> 
    WF_Unitary (apply_unitary dim u l).
Proof.
  intros n dim u l L LT.
  destruct n as [|[|n]]; try solve [inversion u].
  - simpl.
    destruct l; try solve [inversion L].
    simpl in *.
    specialize (LT n (or_introl eq_refl)).
    replace (2^dim)%nat with (2^n * 2 * 2^(dim - n - 1))%nat by unify_pows_two.
    repeat apply kron_unitary; try apply id_unitary; try apply unitary_gate_unitary.
    specialize (unitary_gate_unitary u) as UU. apply UU.
  - dependent destruction u; apply denote_ctrls_unitary; auto.
Qed.    

Lemma apply_U_correct : forall n dim (U : Unitary n) l,
                            length l = n ->
                            (forall x, In x l -> x < dim)%nat -> 
                            WF_Superoperator (apply_U dim U l). 
Proof.
  intros.
  apply super_unitary_correct; trivial.
  apply apply_unitary_unitary; easy.
Qed.
