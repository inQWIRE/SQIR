Require Import Quantum.
Require Import List.
Require Import SQIMP.
Require Import UnitarySem.

(* But also move *)

Definition norm {n} (ψ : Vector n) :=
  sqrt (fst (ψ ∘ ψ†)).  

Inductive nd_eval : forall dim, com -> Vector (2^dim) -> Vector (2^dim) -> Prop :=
  | nd_app : forall dim n (u : Unitary n) (l : list nat) (ψ : Vector (2^dim)),
      nd_eval dim (app u l) ψ ((ueval dim u l) × ψ)
  | nd_meas0 : forall dim n (ψ : Vector (2^dim)),
      let ψ' := @pad 2 n dim (∣0⟩⟨0∣) × ψ in 
      nd_eval dim (meas n) ψ (scale (/(norm ψ')) ψ') 
  | nd_meas1 : forall dim n (ψ : Vector (2^dim)),
      let ψ' := @pad 2 n dim (∣1⟩⟨1∣) × ψ in
      norm ψ' <> 0%R ->
      nd_eval dim (meas n) ψ (scale (/(norm ψ')) ψ') 
.



Reserved Notation "dim '$' c '/' ψ '||' ψ'" (at level 80).

Inductive nd_eval : forall dim, com -> Vector (2^dim) -> Vector (2^dim) -> Prop :=
  | nd_app : forall dim n (u : Unitary n) (l : list nat) (ψ : Vector (2^dim)),
    (dim $ app u l / ψ || ((ueval dim u l) × ψ))

where "dim '$' c '/' ψ '||' ψ'" := (nd_eval dim c ψ ψ').
                                                                              
