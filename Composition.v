Require Import SQIMP.
Require Import UnitarySem.

(* Utilities for composing SQIMP programs. Our design is not intended to 
   be compositional (but rather a simple IR). In order to compose two SQIMP
   programs, the programmer (or compiler) needs to map qubits in both programs
   to the new global register. *)


(* TODO: extend the defs below to non-unitary circuits *)
(* TODO: move padding lemmas to this file? *)

Fixpoint map_qubits (f : nat -> nat) (c : ucom) :=
  match c with
  | uskip => uskip
  | c1; c2 => map_qubits f c1; map_qubits f c2
  | uapp u l => uapp u (map f l)
  end.

(* Combine two programs in parallel. Note that we have no way to enforce
   that dim1 and dim2 are actually the dimensions of the global registers
   of c1 and c2. *)
Definition inPar (c1 c2 : ucom) (dim1 dim2 : nat) :=
  c1; map_qubits (fun q => q + dim1) c2.

Require Import Coq.Logic.FinFun.

Lemma inPar_WT : forall c1 c2 dim1 dim2,
  uc_well_typed dim1 c1 -> uc_well_typed dim2 c2 -> uc_well_typed (dim1 + dim2) (inPar c1 c2 dim1 dim2).
Proof.
  intros c1 c2 dim1 dim2 WTc1 WTc2.
  unfold inPar.
  apply WT_seq.
  - replace (dim1 + dim2) with (dim2 + dim1) by lia. 
    apply typed_pad. assumption.
  - clear - WTc2. induction WTc2.
    + apply WT_uskip.
    + apply WT_seq. apply IHWTc2_1. apply IHWTc2_2.
    + apply WT_app.
      * rewrite map_length; assumption.
      * intros x Hin.
        apply in_map_iff in Hin.
        inversion Hin as [x0 [Hx0 Hinx0]].
        apply H0 in Hinx0.
        lia.
      * apply Injective_map_NoDup; try assumption.
        intros x y Hxy.
        lia.
Qed.

Lemma denote_pad : forall (n k : nat)(c : ucom), 
  uc_well_typed n c ->
  uc_eval n c ⊗ (I (2 ^ k)) = uc_eval (n + k) c.
Proof.
  intros. generalize dependent n.
  induction c; intros.
  - simpl; rewrite id_kron. 
    replace (2 ^ n * 2 ^ k) with (2 ^ (n + k)) by unify_pows_two.
    reflexivity.
  - simpl. inversion H; subst. 
    rewrite <- IHc1; try assumption.
    rewrite <- IHc2; try assumption.
    restore_dims_strong; Msimpl.
    reflexivity.
  - simpl.
Admitted.

(* I think you only need a well-typedness constraint on c1.
 
   The potential problem is when c1 is not well-typed in dim1, but is 
   well-typed in (dim1 + dim2). In this case, the LHS may be nonzero
   while the RHS is zero. *)
Lemma inPar_correct : forall c1 c2 dim1 dim2,
  uc_well_typed dim1 c1 ->
  uc_eval (dim1 + dim2) (inPar c1 c2 dim1 dim2) = (uc_eval dim1 c1) ⊗ (uc_eval dim2 c2).
Proof.
  intros c1 c2 dim1 dim2 WTc1.
  induction c2.
  - simpl. rewrite <- denote_pad; try assumption. Msimpl. reflexivity.
Admitted.