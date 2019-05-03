Require Import QWIRE.Dirac.
Require Import UnitarySem.
Open Scope ucom.

(*********************************)
(** Boolean Circuit Compilation **)
(*********************************)
(* Current progress on reproducing QWIRE/Oracles.v. 

   Note that the b_not construct is not necessary (b_not b ≡ b_xor b_t b).
*)

Inductive bexp := 
| b_t   : bexp
| b_f   : bexp
| b_var : nat -> bexp
| b_not : bexp -> bexp
| b_and : bexp -> bexp -> bexp 
| b_xor : bexp -> bexp -> bexp.

Reserved Notation "⌈ b | f ⌉" (at level 0). 

Fixpoint interpret_bexp (b : bexp) (f : nat -> bool) : bool :=
  match b with
  | b_t         => true 
  | b_f         => false 
  | b_var v     => f v 
  | b_not b     => ¬ ⌈ b | f ⌉
  | b_and b1 b2 => ⌈ b1 | f ⌉ && ⌈ b2 | f ⌉
  | b_xor b1 b2 => ⌈ b1 | f ⌉ ⊕ ⌈ b2 | f ⌉
  end where "⌈ b | f ⌉" := (interpret_bexp b f).  

(* This def. of Toffoli is from https://en.wikipedia.org/wiki/Toffoli_gate *)
Definition TDAG a := uapp (U_R (- PI / 4)) [a].
Definition TOFFOLI (a b c : nat) : ucom :=
  H c; 
  CNOT b c; TDAG c; 
  CNOT a c; T c; 
  CNOT b c; TDAG c; 
  CNOT a c; T b; T c; H c;
  CNOT a b; T a; TDAG b; 
  CNOT a b.

(* TODO: prove that the Toffoli gate implements the Toffoli spec. *)

Opaque TOFFOLI.

(* How many input variables does this expression reference? *)
Fixpoint max_var b v :=
  match b with 
  | b_var v' => max v v'
  | b_not b => max_var b v
  | b_and b1 b2 => max (max_var b1 v) (max_var b2 v)
  | b_xor b1 b2 => max (max_var b1 v) (max_var b2 v)
  | _ => v
  end.

Fixpoint no_vars b :=
  match b with
  | b_var _ => false
  | b_not b => no_vars b
  | b_and b1 b2 => no_vars b1 && no_vars b2
  | b_xor b1 b2 => no_vars b1 && no_vars b2
  | _ => true
  end.

Definition num_inputs b : nat := if (no_vars b) then 0 else (max_var b 0) + 1.

(* How many ancillary qubits are needed to represent this expression? *)
Fixpoint num_ancillae b : nat :=
  match b with
  | b_not b => 1 + (num_ancillae b)
  | b_and b1 b2 => 2 + (num_ancillae b1) + (num_ancillae b2)
  | b_xor b1 b2 => max (num_ancillae b1) (num_ancillae b2) 
  | _ => 0
  end.

(* Total number of qubits required. *)
Definition b_dim (b : bexp) : nat := (num_inputs b) + 1 + (num_ancillae b).

(* Translate boolean expression into a unitary circuit. 

   i = index of result
   j = index of next available ancilla *)
Fixpoint compile' (b : bexp) (i j : nat) : ucom :=
  match b with
  | b_t         => X i
  | b_f         => uskip
  | b_var v     => CNOT v i
  | b_not b     => X j;
                  compile' b j (j+1); 
                  CNOT j i;
                  compile' b j (j+1); 
                  X j
  | b_and b1 b2 => compile' b1 j (j+2); 
                  compile' b2 (j+1) (j+2); (* this probably shouldn't be j+2 *)
                                           (* maybe: j + 2 + num_ancillae b1 *)
                  TOFFOLI j (j+1) i;
                  compile' b2 (j+1) (j+2); 
                  compile' b1 j (j+2)
  | b_xor b1 b2 => compile' b1 i j; 
                  compile' b2 i j
  end.

Definition compile b := compile' b (num_inputs b) ((num_inputs b) + 1).

(* Using 'cbv' to get the evaluator to respect that TOFFFOLI is opaque. *)
Eval cbv in (compile (b_and b_t b_t)).
Definition b1 := b_and (b_xor b_t b_f) (b_and (b_var 0) (b_xor b_t (b_var 1))).
Eval cbv in (compile b1).

(* TODO: move nket and bool_to_nat coercion to main QWIRE library. *)
Fixpoint nket (n : nat) (ψ : Matrix 2 1) : Matrix (2^n) 1 :=
  match n with
  | 0 => I 1
  | S n' => (nket n' ψ) ⊗ ψ
  end.

Definition bool_to_nat (b : bool) : nat := if b then 1 else 0.
Coercion bool_to_nat : bool >-> nat.

Fixpoint inputs_to_vec' (f : nat -> bool) (i n : nat) :=
  match i with
  | 0 => ∣ (f (n - i))%nat ⟩
  | S i' => ∣ (f (n - i))%nat ⟩ ⊗ (inputs_to_vec' f i' n) 
  end.

Definition inputs_to_vec (f : nat -> bool) (n : nat) := inputs_to_vec' f (n - 1) (n - 1).

Definition build_state (b : bexp) (f : nat -> bool) (r : bool) : Vector (2 ^ (b_dim b)) :=
  if num_inputs b =? 0
  then if num_ancillae b =? 0
       then ∣ r ⟩
       else ∣ r ⟩ ⊗ (nket (num_ancillae b) ∣0⟩)
  else if num_ancillae b =? 0
       then (inputs_to_vec f (num_inputs b)) ⊗ ∣ r ⟩
       else (inputs_to_vec f (num_inputs b)) ⊗ ∣ r ⟩ ⊗ (nket (num_ancillae b) ∣0⟩).

Lemma compile_correct : forall (b : bexp) (f : nat -> bool) (r : bool), 
  (uc_eval (b_dim b) (compile b)) × (build_state b f r) = (build_state b f (r ⊕ ⌈ b | f ⌉)).
Proof.
  intros.
  induction b; simpl; 
  unfold ueval1, ueval_cnot, pad, build_state, num_inputs, b_dim; simpl.
  - (* b_t *)
    destruct r; simpl; autorewrite with M_db ket_db; reflexivity.
  - (* b_f *)
    destruct r; simpl; autorewrite with M_db ket_db; reflexivity.
  - (* b_var v *)
    replace (n <? n + 1) with true.
    2: { symmetry. apply Nat.ltb_lt. lia. }
    unfold num_inputs; simpl.
    replace (n + S (n + 1 - n - 1 + 1) <=? n + 1 + 1 + 0) with true.
    2: { symmetry. apply Nat.leb_le. lia. }
    bdestruct (n + 1 =? 0). contradict H. lia.
    admit.
  - (* b_not b *)
    admit.
  - (* b_and b1 b2 *) 
    admit.
  - (* b_xor b1 b2 *)
    admit.
Admitted.