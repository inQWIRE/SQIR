Require Export SQIMP.
Require Export Quantum.
Require Import Setoid.

Open Scope ucom_scope.

(** Denotation of Unitaries *)

Definition pad {n} (start dim : nat) (A : Square (2^n)) : Square (2^dim) :=
  if start + n <=? dim then I (2^start) ⊗ A ⊗ I (2^(dim - n - start)) else Zero.

Lemma WF_pad : forall n start dim (A : Square (2^n)),
  WF_Matrix A ->
  WF_Matrix (pad start dim A).
Proof.
  intros n start dim A WFA. unfold pad.
  bdestruct (start + n <=? dim); auto with wf_db.
Qed.  

(* k must be 1, but dependent types... *)
Definition ueval1 {k} (dim n : nat) (u : Unitary k) : Square (2^dim) :=
  @pad 1 n dim
  match u with  
  | U_H         => hadamard 
  | U_X         => σx
  | U_Y         => σy
  | U_Z         => σz
  | U_R ϕ       => phase_shift ϕ
  | _           => Zero
  end.

(* Restriction: m <> n and m, n < dim *)
Definition ueval_cnot (dim m n: nat) : Square (2^dim) :=
  if (m <? n) then
    @pad (1+(n-m-1)+1) m dim (∣1⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I (2^(n-m)))
  else if (n <? m) then
    @pad (1+(m-n-1)+1) n dim (σx ⊗ I (2^(m-n-1)) ⊗ ∣1⟩⟨1∣ .+ I (2^(m-n)) ⊗ ∣0⟩⟨0∣)
  else
    Zero.

Definition ueval {n} (dim : nat) (u : Unitary n) (l : list nat) : Square (2^dim) :=
  match n, l with
  | 1, [i]   => ueval1 dim i u
  | 2, i::[j] => ueval_cnot dim i j
  | _, _     => Zero
  end.

(** Denotation of ucoms **)

Fixpoint uc_eval (dim : nat) (c : ucom) : Matrix (2^dim) (2^dim) :=
  match c with
  | uskip    => I (2^dim)
  | uapp u l => ueval dim u l
  | c1 ; c2  => uc_eval dim c2 × uc_eval dim c1 
  end.

(** Well-formedness **)

Lemma WF_ueval1 : forall dim n (u : Unitary 1), WF_Matrix (ueval1 dim n u).
Proof.
  intros dim n u.
  apply WF_pad.
  destruct u; auto with wf_db.
Qed.  
  
Lemma WF_ueval_cnot : forall dim m n, WF_Matrix (ueval_cnot dim m n). 
Proof.
  intros dim m n.
  unfold ueval_cnot.
  bdestruct (m <? n); [|bdestruct (n <? m)];
    try apply WF_pad; unify_pows_two; auto 10 with wf_db.    
Qed.  

Lemma WF_ueval : forall n dim (u : Unitary n) l, WF_Matrix (ueval dim u l).
Proof.
  intros n dim u l.
  destruct n as [|[|[|n']]]; simpl; auto with wf_db.
  - destruct l as [|i [| j l]]; simpl; auto with wf_db.
    apply WF_ueval1.
  - destruct l as [|i [| j [| k l]]]; simpl; auto with wf_db.
    apply WF_ueval_cnot.
Qed.  

Lemma WF_uc_eval : forall dim c, WF_Matrix (uc_eval dim c).
Proof.
  intros dim c.
  induction c; simpl; auto with wf_db.
  apply WF_ueval.
Qed.

Hint Resolve WF_pad WF_ueval1 WF_ueval_cnot WF_ueval WF_uc_eval : wf_db.


(* Some unit tests *)

Lemma eval_H : uc_eval 1 (H 0) = hadamard.
Proof.
  simpl. unfold ueval1, pad. (* have these automatically simplify *)
  simpl. Msimpl. reflexivity.
Qed.

Lemma eval_HHpar : uc_eval 2 (H 0; H 1) = hadamard ⊗ hadamard.
Proof.
  simpl. unfold ueval1, pad. (* have these automatically simplify *)
  simpl. restore_dims.  Msimpl. 
  restore_dims. Msimpl. 
  reflexivity.
Qed.

Lemma eval_HHseq : uc_eval 2 (H 0; H 0) = I 4.
Proof.
  simpl. unfold ueval1, pad. (* have these automatically simplify *)
  simpl. Msimpl. solve_matrix.
Qed.

Lemma eval_CNOT : uc_eval 2 (CNOT 0 1) = cnot.
Proof.
  unfold uc_eval. simpl.
  simpl. unfold ueval_cnot, pad. (* have these automatically simplify *)
  simpl. Msimpl. solve_matrix.
Qed.

(** Equivalence and Structural Rules **)

(* Precondition about typing? *)
Definition uc_equiv (c1 c2 : ucom) := forall dim, uc_eval dim c1 = uc_eval dim c2.

Infix "≡" := uc_equiv : ucom_scope.

Lemma uc_equiv_refl : forall c1, c1 ≡ c1. 
Proof. easy. Qed.

Lemma uc_equiv_sym : forall c1 c2, c1 ≡ c2 -> c2 ≡ c1. 
Proof. easy. Qed.

Lemma uc_equiv_trans : forall c1 c2 c3, c1 ≡ c2 -> c2 ≡ c3 -> c1 ≡ c3. 
Proof. intros c1 c2 c3 H12 H23 dim. rewrite H12. easy. Qed.

Lemma useq_assoc : forall c1 c2 c3, ((c1 ; c2) ; c3) ≡ (c1 ; (c2 ; c3)).
Proof.
  intros c1 c2 c3 dim. simpl.
  rewrite Mmult_assoc. easy.
Qed.

Lemma useq_congruence : forall c1 c1' c2 c2',
    c1 ≡ c1' ->
    c2 ≡ c2' ->
    c1 ; c2 ≡ c1' ; c2'.
Proof.
  intros c1 c1' c2 c2' Ec1 Ec2 dim.
  simpl.
  rewrite Ec1, Ec2.
  reflexivity.
Qed.

Add Relation ucom uc_equiv 
  reflexivity proved by uc_equiv_refl
  symmetry proved by uc_equiv_sym
  transitivity proved by uc_equiv_trans
  as uc_equiv_rel.

Add Morphism useq 
  with signature (@uc_equiv) ==> (@uc_equiv) ==> (@uc_equiv) as useq_mor.
Proof. intros x y H x0 y0 H0. apply useq_congruence; easy. Qed.

Lemma test_rel : forall c1 c2, c1 ≡ c2 -> c2 ≡ c1.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma test_mor : forall c1 c2, c1 ≡ c2 -> c2 ; c1 ≡ c1 ; c1.
Proof. intros. rewrite H. reflexivity. Qed.

(** Example Equivalences **)

Lemma uskip_id_l : forall (c : ucom),
   (uskip ; c) ≡ c.
Proof.
  intros c dim.
  simpl; Msimpl; reflexivity.
Qed.

Lemma uskip_id_r : forall (c : ucom),
   (c ; uskip) ≡ c.
Proof.
  intros c dim.
  simpl; Msimpl; reflexivity.
Qed.

Close Scope C_scope.
Close Scope R_scope.

Ltac unify_matrices := 
  match goal with
  | |- @Mmult ?m ?n ?o ?A ?B = @Mmult ?m' ?n' ?o' ?A ?B => 
    try replace m with m' by unify_pows_two;
    try replace n with n' by unify_pows_two;
    try replace o with o' by unify_pows_two;
    reflexivity
  | |- @kron ?m ?n ?o ?p ?A ?B = @kron ?m' ?n' ?o' ?p' ?A ?B => 
    try replace m with m' by unify_pows_two;
    try replace n with n' by unify_pows_two;
    try replace o with o' by unify_pows_two;
    try replace p with p' by unify_pows_two;
    reflexivity
  | |- @adjoint ?m ?n ?A ?B = @adjoint ?m' ?n' ?A ?B => 
    try replace m with m' by unify_pows_two;
    try replace n with n' by unify_pows_two;
    reflexivity                               
  end.

Ltac restore_dims_strong :=
  repeat match goal with
  | [ |- context[@Mmult ?m ?n ?o ?A ?B]] => progress match type of A with 
                                          | Matrix ?m' ?n' =>
                                            match type of B with 
                                            | Matrix ?n'' ?o' =>
                                              replace (@Mmult m n o A B) with
                                                  (@Mmult m' n' o' A B) by unify_matrices 
                                            end
                                          end
  | [ |- context[@kron ?m ?n ?o ?p ?A ?B]] => progress match type of A with 
                                            | Matrix ?m' ?n' =>
                                              match type of B with 
                                              | Matrix ?o' ?p' =>
                                                replace (@kron m n o p A B) with
                                                    (@kron m' n' o' p' A B) by unify_matrices 
                                              end
                                            end
  | [ |- context[@adjoint ?m ?n ?A]]       => progress match type of A with
                                            | Matrix ?m' ?n' =>
                                              replace (@adjoint m n A) with (@adjoint m' n' A) by unify_matrices
                                            end
         end.

(* For handling non well-typed cases. (Shouldn't Msimpl do this?) *)
Ltac remove_zero_gates :=
  repeat rewrite Mmult_0_l;
  repeat rewrite Mmult_0_r;
  repeat rewrite Mmult_0_l; (* hacky *)
  repeat rewrite Mmult_0_r;
  repeat rewrite kron_0_l;
  repeat rewrite kron_0_r;
  repeat rewrite kron_0_l;
  repeat rewrite kron_0_r.

(* Remove extra identity gates. (Shouldn't Msimpl do this too?) *)
Ltac remove_id_gates :=
  repeat rewrite Mmult_1_l;
  repeat rewrite Mmult_1_r;
  try auto with wf_db.


Local Notation "a *= U" := (uapp U [a]) (at level 0) : ucom_scope. 

Lemma slide1 : forall (m n : nat) (U V : Unitary 1),
  m <> n ->
  (m *= U ; n *= V) ≡ (n *= V ; m *= U). 
Proof.
  intros m n U V NE dim.
  simpl.
  simpl in *.
  unfold ueval1. 
  repeat match goal with
  | [|- context [pad m _ ?U ]] => remember U as U'
  | [|- context [pad n _ ?V ]] => remember V as V'
  end.
  assert (WFU : WF_Matrix U') by 
      (destruct U; subst; auto with wf_db).
  assert (WFV : WF_Matrix V') by 
      (destruct V; subst; auto with wf_db).
  clear HeqU' HeqV' U V.
  unfold pad.
  bdestruct (n + 1 <=? dim); bdestruct (m + 1 <=? dim);
    remove_zero_gates; trivial.
  bdestruct (m <? n).
  - remember (n - m - 1) as k.
    replace n with (m + 1 + k) by lia.
    replace (2 ^ (m+1+k)) with (2^m * 2 * 2^k) by unify_pows_two.
    remember (dim - 1 - (m + 1 + k)) as j.
    replace (dim - 1 - m) with (k + 1 + j) by lia.
    replace (2 ^ (k + 1 + j)) with (2^k * 2 * 2^ j) by unify_pows_two.
    simpl in *.
    repeat rewrite <- id_kron.
    restore_dims.
    repeat (rewrite kron_assoc; restore_dims).
    replace (2^dim) with (2 ^ m * 2 * 2 ^ k * 2 * 2 ^ j) by unify_pows_two.
    clear -WFU WFV.
    restore_dims_strong. 
    Msimpl.
    reflexivity.
  - rename m into n, n into m.
    remember (n - m - 1) as k.
    replace n with (m + 1 + k) by lia.
    replace (2 ^ (m+1+k)) with (2^m * 2 * 2^k) by unify_pows_two.
    remember (dim - 1 - (m + 1 + k)) as j.
    replace (dim - 1 - m) with (k + 1 + j) by lia.
    replace (2 ^ (k + 1 + j)) with (2^k * 2 * 2^ j) by unify_pows_two.
    repeat rewrite <- id_kron.
    simpl in *.
    repeat rewrite kron_assoc.
    repeat rewrite Nat.mul_assoc.
    restore_dims.
    repeat (rewrite kron_assoc; restore_dims).
    replace (2^dim) with (2 ^ m * 2 * 2 ^ k * 2 * 2 ^ j) by unify_pows_two.
    clear -WFU WFV.
    restore_dims_strong.
    Msimpl.
    reflexivity.
Qed.


(* Several of the type rewrites are just associativity issues, and lia
   is a little slow solving these. *)
Ltac rewrite_assoc :=
  repeat rewrite mult_assoc;
  easy.

(* More general version of slide1.

   NOTE: This is a work in progress, we should be able to clean it up
   with restore_dims! *)
Lemma slide12 : forall (m q : nat) (l : list nat) (U : Unitary 1) (V : Unitary m),
  (inb q l) = false ->
  (uapp U [q] ; uapp V l) ≡ (uapp V l ; uapp U [q]). 
Proof.
  intros m q l U V NE dim.
  destruct V;
  (* use slide1 to prove all single-qubit gate cases *)
  try (
    destruct l; try (destruct l); simpl;
    remove_zero_gates; trivial;
    simpl in NE;
    rewrite orb_false_r in NE;
    apply beq_nat_false in NE;
    apply not_eq_sym in NE;
    apply slide1;
    easy
  ).
  (* all that's left is the CNOT case *)
  destruct l; try (destruct l); try (destruct l); simpl; remove_zero_gates; trivial.
  unfold ueval1, ueval_cnot. 
  match goal with
  | [|- context [pad q _ ?U ]] => remember U as U'
  end.
  assert (WFU : WF_Matrix U') by 
      (destruct U; subst; auto with wf_db).
  clear HeqU' U.
  simpl in NE;
  rewrite orb_false_r in NE;
  apply orb_false_elim in NE;
  destruct NE as [NE1 NE2];
  apply beq_nat_false in NE1;
  apply beq_nat_false in NE2.
  bdestruct (n <? n0).
  - unfold pad.
    remember (n0 - n - 1) as i.
    replace (2 ^ (n0 - n)) with (2 ^ i * 2) by unify_pows_two.
    repeat rewrite <- id_kron.
    rewrite <- (kron_assoc _ _ (I 2)).
    bdestruct (q + 1 <=? dim); bdestruct (n + (1 + i + 1) <=? dim); 
    remove_zero_gates; trivial.
    bdestruct (n0 <? q).
    (* Case 1/6: n < n0 < q *)
    + remember (q - (1 + i + 1) - n) as j.
      remember (dim - 1 - q) as k.
      replace (2 ^ q) with (2 ^ n * (2 * 2 ^ i * 2) * 2 ^ j) by unify_pows_two.
      replace (2 ^ (dim - (1 + i + 1) - n)) with (2 ^ j * 2 * 2 ^ k) by unify_pows_two.
      repeat rewrite <- id_kron.
      rewrite <- (kron_assoc _ _ (I (2 ^ k))).
      rewrite <- (kron_assoc _ _ (I 2)).  
      (* * *) replace (2 ^ (1 + i + 1)) with (2 * 2 ^ i * 2) by unify_pows_two.
      (* * *) replace (2 ^ dim) with (2 ^ n * (2 * 2 ^ i * 2) * 2 ^ j * 2 * 2 ^ k) by unify_pows_two.
      (* * *) replace (2 ^ n * (2 * 2 ^ i * 2) * (2 ^ j * 2)) with (2 ^ n * (2 * 2 ^ i * 2) * 2 ^ j * 2) by rewrite_assoc.
      (* * *) replace (2 ^ 1) with 2 by easy.
      repeat rewrite kron_mixed_product; remove_id_gates.
      rewrite Mmult_plus_distr_l.
      rewrite Mmult_plus_distr_r.
      repeat rewrite kron_mixed_product; remove_id_gates.
    + apply le_lt_eq_dec in H2; destruct H2; 
        try (contradict e; apply not_eq_sym; easy).
      bdestruct (n <? q).
      (* Case 2/6: n < q < n0 *)
      * remember (q - n - 1) as j.
        remember (i - j - 1) as k.
        remember (dim - (1 + i + 1) - n) as m.
        (* * *) replace (2 ^ (1 + i + 1)) with (2 * 2 ^ i * 2) by unify_pows_two.
        (* TODO: You can use unify_pows_two here, but it's super slow! 
                 How can we help Coq solve these faster? GO GO LIA!!! *)
        replace (2 ^ q) with (2 ^ n * 2 * 2 ^ j) by unify_pows_two. 
        replace (2 ^ i) with (2 ^ j * 2 * 2 ^ k) by unify_pows_two.    
        replace (2 ^ (dim - 1 - q)) with (2 ^ k * 2 * 2 ^ m) by unify_pows_two.
        repeat rewrite <- id_kron.
        repeat rewrite <- kron_assoc.
        rewrite (kron_assoc (I (2 ^ n)) _ (I (2 ^ j))).
        
        (* Something along these lines may help 
        repeat (restore_dims; rewrite kron_assoc).
        (* * *) replace (2 ^ dim) with (2 ^ n * (2 * 2 ^ j * 2 * 2 ^ k * 2) * 2 ^ m) by unify_pows_two.
        clear -WFU.
        restore_dims_strong.
        *)


        (* * *) replace (2 ^ n * 2 * 2 ^ j) with (2 ^ n * (2 * 2 ^ j)) by rewrite_assoc.
        rewrite (kron_assoc (I (2 ^ n)) _ U').
        (* * *) replace (2 ^ 1) with 2 by easy.
        (* * *) replace (2 ^ n * (2 * 2 ^ j) * 2) with (2 ^ n * (2 * 2 ^ j * 2)) by rewrite_assoc.
        rewrite (kron_assoc (I (2 ^ n)) _ (I (2 ^ k))).
        (* * *) replace (2 ^ n * (2 * 2 ^ j * 2) * 2 ^ k) with (2 ^ n * (2 * 2 ^ j * 2 * 2 ^ k)) by rewrite_assoc.
        rewrite (kron_assoc (I (2 ^ n)) _ (I 2)).
        (* * *) replace (2 ^ dim) with (2 ^ n * (2 * 2 ^ j * 2 * 2 ^ k * 2) * 2 ^ m) by unify_pows_two.
        (* * *) replace (2 * (2 ^ j * 2 * 2 ^ k) * 2) with (2 * 2 ^ j * 2 * 2 ^ k * 2) by rewrite_assoc.
        (* * *) replace (2 ^ n * (2 * 2 ^ j * 2) * (2 ^ k * 2)) with (2 ^ n * (2 * 2 ^ j * 2 * 2 ^ k * 2)) by rewrite_assoc.
        rewrite kron_mixed_product.
        repeat rewrite kron_mixed_product; remove_id_gates.
        rewrite Mmult_plus_distr_l.
        rewrite Mmult_plus_distr_r.
        (* * *) replace (2 * (2 ^ j * 2 * 2 ^ k)) with (2 * 2 ^ j * 2 ^ 1 * 2 ^ k) by rewrite_assoc.
        repeat rewrite kron_mixed_product. 
        (* * *) replace (2 * (2 ^ j * 2)) with (2 * 2 ^ j * 2) by rewrite_assoc.
        repeat rewrite kron_mixed_product; remove_id_gates.
      (* Case 3/6: q < n < n0 *)
      * admit.
  - bdestruct (n0 <? n); remove_zero_gates; trivial.
    unfold pad.
    remember (n - n0 - 1) as i.
    (* * *) replace (2 ^ (1 + i + 1)) with (2 * 2 ^ i * 2) by unify_pows_two.
    bdestruct (q + 1 <=? dim); bdestruct (n0 + (1 + i + 1) <=? dim); 
    remove_zero_gates; trivial.
    bdestruct (n <? q).
    (* Case 4/6: n0 < n < q *)
    + admit.
    + apply le_lt_eq_dec in H3; destruct H3; 
        try (contradict e; apply not_eq_sym; easy).
      bdestruct (n0 <? q).
      (* Case 5/6: n0 < q < n *)
      * admit.
      * apply le_lt_eq_dec in H3; destruct H3; 
        try (contradict e; apply not_eq_sym; easy).
        (* Case 6/6: q < n0 < n *)
        admit.
Admitted.

Lemma XX_id : forall q dim, 
  uc_well_typed dim (X q) -> uc_eval dim uskip = uc_eval dim (X q; X q).
Proof. 
  intros q dim WT. 
  simpl; unfold ueval1, pad. 
  inversion WT; subst. 
  assert (q < dim). { apply H4. left. easy. }
  replace (q + 1 <=? dim) with true by (symmetry; apply Nat.leb_le; lia).
  restore_dims_strong; Msimpl.
  replace (σx × σx) with (I 2) by solve_matrix.
  repeat rewrite id_kron.
  apply f_equal.
  unify_pows_two.
Qed.

Lemma X_CNOT_comm : forall c t, X t; CNOT c t ≡ CNOT c t ; X t.
Proof.
  intros c t dim.
  simpl; unfold ueval1, pad. 
  bdestruct (t + 1 <=? dim); remove_zero_gates; trivial. 
  unfold ueval_cnot, pad. 
  bdestruct (c <? t).
  - bdestruct (c + (1 + (t - c - 1) + 1) <=? dim); remove_zero_gates; trivial. 
    (* c < t *)
    remember (t - c - 1) as i.
    replace (dim - (1 + i + 1) - c) with (dim - 1 - t) by lia.
    remember (dim - 1 - t) as j.
    replace (2 ^ t) with (2 ^ c * 2 * 2 ^ i) by unify_pows_two.
    replace (2 ^ (t - c)) with (2 ^ i * 2) by unify_pows_two.
    repeat rewrite <- id_kron.
    rewrite (kron_assoc (I (2 ^ c)) _ (I (2 ^ i))).
    replace dim with (c + (1 + i + 1) + j) by lia.
    clear.
    restore_dims_strong.
    rewrite (kron_assoc (I (2 ^ c)) _ σx).
    restore_dims_strong.
    repeat rewrite kron_mixed_product; remove_id_gates.
    rewrite <- (kron_assoc ∣0⟩⟨0∣ (I (2 ^ i)) (I 2)).
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r.
    repeat rewrite kron_mixed_product; remove_id_gates.
  - bdestruct (t <? c); remove_zero_gates; trivial.
    bdestruct (t + (1 + (c - t - 1) + 1) <=? dim); remove_zero_gates; trivial.
    (* t < c *)
    remember (c - t - 1) as i.
    replace (dim - (1 + i + 1) - t) with (dim - 1 - c) by lia.
    remember (dim - 1 - c) as j.
    replace (2 ^ (dim - 1 - t)) with (2 ^ i * 2 * 2 ^ j) by unify_pows_two.
    replace (2 ^ (c - t)) with (2 * 2 ^ i) by unify_pows_two.
    repeat rewrite <- id_kron.
    rewrite (kron_assoc (I (2 ^ t)) σx _).
    rewrite <- (kron_assoc σx _ (I (2 ^ j))).
    rewrite <- (kron_assoc σx (I (2 ^ i)) (I 2)).
    replace dim with (t + (1 + i + 1) + j) by lia.
    clear.
    restore_dims_strong.
    rewrite <- (kron_assoc (I (2 ^ t)) _ (I (2 ^ j))).
    restore_dims_strong.
    repeat rewrite kron_mixed_product; remove_id_gates.
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r.
    repeat rewrite kron_mixed_product; remove_id_gates.
Qed.

Lemma pad_dims : forall c n k,
  uc_well_typed n c ->
  (uc_eval n c) ⊗ I (2^k) = uc_eval (n + k) c.  
Proof.
  intros c n k H.
  induction c.
  - simpl. rewrite id_kron. unify_pows_two. reflexivity.
  - inversion H; subst.
    simpl. rewrite <- IHc1, <- IHc2; trivial.
    restore_dims_strong; Msimpl; reflexivity.
  - simpl.
    unfold ueval.
    destruct n0 as [|[|[|]]]; simpl; remove_zero_gates; trivial.
    + destruct l as [| a []]; remove_zero_gates; trivial.
      unfold ueval1.
      repeat match goal with
      | [|- context [pad _ _ ?U ]] => remember U as U'
      end.
      unfold pad.
      assert(L : a + 1 <= n).
      { inversion H; subst.
        specialize (H5 a (or_introl eq_refl)).
        lia.
      }
      bdestruct (a + 1 <=? n); bdestructΩ (a + 1 <=? n+k).
      restore_dims.
      rewrite (kron_assoc (I (2^a) ⊗ U')).
      rewrite id_kron. unify_pows_two.
      replace (n - 1 - a + k) with (n + k - 1 - a) by lia.
      reflexivity.
    + destruct l as [| a [|b[|]]]; remove_zero_gates; trivial.
      unfold ueval_cnot.
      inversion H; subst.
      assert (La : a < n) by (apply H5; simpl; auto).
      assert (Lb : b < n) by (apply H5; simpl; auto).
      clear -La Lb.
      unfold pad.
      bdestruct (a <? b); bdestructΩ (b <? a); remove_zero_gates; trivial.
      * bdestructΩ (a + S (b - a - 1 + 1) <=? n).
        bdestructΩ (a + S (b - a - 1 + 1) <=? n + k).
        restore_dims; rewrite (kron_assoc _ _  (I (2^k))).
        rewrite id_kron.
        unify_pows_two.
        rewrite Nat.sub_add by lia.
        rewrite Nat.add_sub_swap by lia.
        rewrite Nat.add_sub_swap by lia.
        reflexivity.
      * bdestructΩ (b + S (a - b - 1 + 1) <=? n).
        bdestructΩ (b + S (a - b - 1 + 1) <=? n + k).
        restore_dims; rewrite (kron_assoc _ _  (I (2^k))).
        rewrite id_kron.
        unify_pows_two.
        rewrite Nat.sub_add by lia.
        rewrite Nat.add_sub_swap by lia.
        rewrite Nat.add_sub_swap by lia.
        reflexivity.
Qed.

Ltac prove_wt :=
  repeat match goal with
         | |- context [ uc_well_typed ?d uskip ] => apply WT_uskip
         | |- context [ uc_well_typed ?d (useq ?c1 ?c2) ] => apply WT_seq
         | |- context [ uc_well_typed ?d (uapp ?u ?l) ] => try unfold CNOT; apply WT_app
         end.


Lemma typed_pad : forall (n k : nat)(c : ucom), uc_well_typed n c -> uc_well_typed (k + n) c.
Proof.
  intros. generalize dependent n.
  induction c; intros; prove_wt; induction k;
  [| apply IHc1 | apply IHc2 | apply IHc2 | | | | apply (in_bounds_pad _ _ 1%nat) | | ]; 
  inversion H; assumption.
Qed.


