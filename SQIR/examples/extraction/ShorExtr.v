(* This file contains code for extracting the Shor's formalism to OCaml. We 
   currently extract Coq real numbers (used in U_R parameters) to OCaml floats.
   This is not ideal for two reasons: (1) floats are not a faithful 
   representation of real numbers, so we lose some guarantees from verification 
   and (2) once we extract to floats, gates get ugly, which could be a problem for
   compilers (e.g. the compiler may have a special rule for H, which we translate
   to U_R 3.14.. 0 1.57..).

   A potential solution to this is to switch the formalism and proofs to a
   different gate set like the following, which uses rationals instead of reals.

Inductive ext_Unitary : nat -> Set := 
  | U_R    : Q -> Q -> Q -> ext_Unitary 1
  | U_CNOT : ext_Unitary 2.

Definition H {dim} n : ext_ucom dim := uapp1 (U_R (1/2) 0 1) n.  
Definition X {dim} n : ext_ucom dim := uapp1 (U_R 1 0 1) n.
...

   That being said, the rest of the quantum software stack (e.g. OpenQASM
   format, simulator) use floating point numbers so we'll have to give up on
   perfect precision at some point.
*)

Require Coq.extraction.Extraction.
Require Import Shor.

(* Standard utilities for bools, options, etc. *)
Require Coq.extraction.ExtrOcamlBasic.

(* A few common functions not included in ExtrOcamlBasic. *)
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".
Extract Inlined Constant negb => "not".
Extract Inlined Constant length => "List.length".
Extract Inlined Constant app => "List.append".
Extract Inlined Constant rev => "List.rev".
Extract Inlined Constant rev_append => "List.rev_append".
Extract Inlined Constant fold_right => "(fun f a l -> List.fold_right f l a)".
Extract Inlined Constant forallb => "List.for_all".

(* Standard extraction from nat -> OCaml int. *)
Require Coq.extraction.ExtrOcamlNatInt.

(* Custom extraction from R -> OCaml float. *)
Extract Constant R => "float".
Extract Constant R0 => "0.0".
Extract Constant R1 => "1.0".
Extract Constant Rplus => "( +. )".
Extract Constant Rmult => "( *. )".
Extract Constant Ropp => "((-.) 0.0)".
Extract Constant Rinv => "((/.) 1.0)".
Extract Constant Rdiv => "( /. )".
Extract Inlined Constant cos => "cos".
Extract Inlined Constant sin => "sin".
Extract Constant PI => "Float.pi".
Extract Inlined Constant Rle_dec => "( <= )".

(* Set "dim" to be implicit everywhere. *)
Extraction Implicit H [dim].
Extraction Implicit X [dim].
Extraction Implicit ID [dim].
Extraction Implicit SKIP [dim].
Extraction Implicit Rz [dim].
Extraction Implicit T [dim].
Extraction Implicit TDAG [dim].
Extraction Implicit CNOT [dim].
Extraction Implicit SWAP [dim].


(* special extraction for modular exponentiation so we don't run into 
   efficiency issues (this is a littele hacky -- it would be better to
   extract all operations to OCaml's Z type). *)
Definition modexp a i N := a ^ (2 ^ i) mod N.
Extract Constant modexp => "fun a i n -> Z.to_int (Z.powm (Z.of_int a) (Z.pow (Z.of_int 2) i) (Z.of_int n))".

(* requires 0 < a < N, gcd a N = 1 
   returns a circuit + the number of qubits used *)
Definition shor_circuit a N := 
  let m := Nat.log2 (2 * N^2)%nat in
  let n := Nat.log2_up N in
  let anc := modmult_rev_anc n in
  let ainv := modinv a N in
  let f i := @bc2ucom (n + anc) (bcelim (modmult_rev N (modexp a i N) (modexp ainv i N) n)) in
  (QPE_var m (n + anc) f, (m + (n + anc))%nat).

Local Open Scope ucom_scope.
Require Export Reals.ROrderedType.
Fixpoint remove_skips {dim} (u : base_ucom dim) :=
  match u with
  | u1 ; u2 =>
      match remove_skips u1, remove_skips u2 with
      | uapp1 g q, u2' => 
          match g with
          | U_R θ ϕ λ => if Reqb θ 0 && Reqb ϕ 0 && Reqb λ 0
                        then u2' else uapp1 g q ; u2'
          | _ => uapp1 g q ; u2'
          end
      | u1', uapp1 g q =>  
          match g with
          | U_R θ ϕ λ => if Reqb θ 0 && Reqb ϕ 0 && Reqb λ 0
                        then u1' else u1' ; uapp1 g q
          | _ => u1' ; uapp1 g q
          end
      | u1', u2' => u1' ; u2'
      end
  | _ => u 
  end.

Lemma Reqb_reflect : forall (x y : R), reflect (x = y) (Reqb x y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Reqb_eq.
Qed.

Hint Resolve Reqb_reflect : bdestruct.

Lemma pad_id : forall n dim,
  (n < dim)%nat -> @pad 1 n dim (I 2) = I (2 ^ dim).
Proof. intros. unfold pad. gridify. reflexivity. Qed.

Lemma remove_skips_WT : forall {dim} (u : base_ucom dim),
  uc_well_typed u -> uc_well_typed (remove_skips u).
Proof.
  intros dim u WT.
  induction u; auto.
  inversion WT; subst.
  apply IHu1 in H1.
  apply IHu2 in H2.
  simpl.
  destruct (remove_skips u1) as [| g1 | g1 | g1];
  destruct (remove_skips u2) as [| g2 | g2 | g2];
  try dependent destruction g1;
  try dependent destruction g2;
  try (constructor; auto).
  all: repeat match goal with
       | |- context[Reqb ?a ?b] => bdestruct (Reqb a b)
       end; try reflexivity.
  all: subst; simpl.
  all: try (constructor; auto).
  all: inversion H1; inversion H2; subst; auto.
Qed.

Lemma remove_skips_preserves_semantics : forall {dim} (u : base_ucom dim),
  uc_well_typed u -> u ≡ remove_skips u.
Proof.
  intros dim u WT.
  induction WT; try reflexivity.
  unfold uc_equiv in *. 
  simpl.
  rewrite IHWT1, IHWT2.
  assert (H1 : uc_well_typed (remove_skips c1)).
  apply remove_skips_WT; auto.
  assert (H2 : uc_well_typed (remove_skips c2)).
  apply remove_skips_WT; auto.
  destruct (remove_skips c1) as [| g1 | g1 | g1];
  destruct (remove_skips c2) as [| g2 | g2 | g2];
  try reflexivity;
  try dependent destruction g1;
  try dependent destruction g2.
  all: repeat match goal with
       | |- context[Reqb ?a ?b] => bdestruct (Reqb a b)
       end; try reflexivity.
  all: subst; simpl.
  all: inversion WT1; inversion WT2; inversion H1; inversion H2; subst.
  all: rewrite I_rotation, pad_id by auto.
  all: Msimpl; reflexivity.
Qed.

Definition post_process (a N x : nat) := 
  (). (* TODO: something to do with r_recoverable *)

Extraction Implicit remove_skips [dim].
Extract Inlined Constant Reqb => "( = )".

Separate Extraction shor_circuit post_process remove_skips.

(* Shor's algorithm:

1. Run the circuit generated by (shor_circuit a N) on input  ∣0⟩_m ∣1⟩_n ∣0⟩_anc.
2. Measure the first m qubits, resulting in the m-bit number x.
3. Run (post_process a N x) to obtain Some(p,q) where p and q are nontrivial factors of N or None 
     (... or something like that)

The main correctness theorem in Shor.v (Shor_correct_full_implementation) 
guarantees that there exists a β > 0 s.t.for any 0 < a < N with gcd a N = 1,
the above algorithm returns Some(p,q) with probability >= β / (Nat.log2 N)^4. 
    (... or something like that)
    
TODO: Add proofs here of the claim above.
(The proofs will likely just call Shor_correct_full_implementation.)
*)
 

