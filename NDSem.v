Require Import Quantum.
Require Import List.
Require Import SQIMP.
Require Import UnitarySem.

(* Also move *)

Definition norm {n} (ψ : Vector n) :=
  sqrt (fst (ψ ∘ ψ†)).  

(* With scaling *)
Reserved Notation "c '/' ψ '⇩' ψ'"
                  (at level 40, ψ at level 39).

Inductive nd_eval {dim : nat} : com -> Vector (2^dim) -> Vector (2^dim) -> Prop :=
  | nd_skip : forall ψ, nd_eval skip ψ ψ
  | nd_app : forall n (u : Unitary n) (l : list nat) (ψ : Vector (2^dim)),
      (app u l) / ψ ⇩ ((ueval dim u l) × ψ)
  | nd_meas0 : forall n (ψ : Vector (2^dim)),
      let ψ' := @pad 2 n dim (∣0⟩⟨0∣) × ψ in 
      norm ψ' <> 0%R ->
      (meas n) / ψ ⇩ (scale (/(norm ψ')) ψ') 
  | nd_meas1 : forall n (ψ : Vector (2^dim)),
      let ψ' := @pad 2 n dim (∣1⟩⟨1∣) × ψ in
      norm ψ' <> 0%R ->
      (meas n) / ψ ⇩ (scale (/(norm ψ')) ψ') 
  | nd_reset0 : forall n (ψ : Vector (2^dim)),
      let ψ' := @pad 2 n dim (∣0⟩⟨0∣) × ψ in 
      (meas n) / ψ ⇩ (scale (/(norm ψ')) ψ') 
  | nd_reset1 : forall n (ψ : Vector (2^dim)),
      let ψ' := @pad 2 n dim (∣0⟩⟨1∣) × ψ in (* is this right? *)
      norm ψ' <> 0%R ->
      (meas n) / ψ ⇩ (scale (/(norm ψ')) ψ')

where "c '/' ψ '⇩' ψ'" := (nd_eval c ψ ψ').              
