Require Export SQIRE.
Require Export Quantum.
Require Import Setoid.

Local Open Scope matrix_scope.
Local Open Scope ucom_scope.

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

(** Automation **)

Local Close Scope C_scope.
Local Close Scope R_scope.

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
  
(* Several of the type rewrites are just associativity issues, and lia
   is a little slow solving these. *)
Ltac rewrite_assoc :=
  repeat rewrite mult_assoc;
  easy.
