Require Export SQIR.UnitaryOps.

Module Common.

Local Open Scope ucom.

(** A toffoli gate but controlled on the first qubit 
    being zero. *)
Definition ZCCX {dim} (a b c : nat) : base_ucom dim :=
  X a;
  CCX a b c;
  X a.

Lemma zero_3_f_to_vec : 
  ∣0,0,0⟩ = f_to_vec 3 (fun _ => false).
Proof.
  lma'. simpl. auto with wf_db.
Qed.

Lemma one_3_f_to_vec : 
  ∣1,0,0⟩ = f_to_vec 3 (fun n => n =? 0).
Proof.
  lma'. simpl. auto with wf_db.
Qed.

Lemma two_3_f_to_vec : 
  ∣0,1,0⟩ = f_to_vec 3 (fun n => n =? 1).
Proof.
  lma'. simpl. auto with wf_db.
Qed.

Lemma three_3_f_to_vec : 
  ∣1,1,0⟩ = f_to_vec 3 (fun n => orb (n =? 0) (n =? 1)).
Proof.
  lma'. simpl. auto with wf_db.
Qed.

Lemma four_3_f_to_vec : 
  ∣0,0,1⟩ = f_to_vec 3 (fun n => n =? 2).
Proof.
  lma'. simpl. auto with wf_db.
Qed.

Lemma five_3_f_to_vec : 
  ∣1,0,1⟩ = f_to_vec 3 (fun n => orb (n =? 0) (n =? 2)).
Proof.
  lma'. simpl. auto with wf_db.
Qed.

Lemma six_3_f_to_vec : 
  ∣0,1,1⟩ = f_to_vec 3 (fun n => orb (n =? 1) (n =? 2)).
Proof.
  lma'. simpl. auto with wf_db.
Qed.

Lemma seven_3_f_to_vec : 
  ∣1,1,1⟩ = f_to_vec 3 (fun _ => true).
Proof.
  lma'. simpl. auto with wf_db.
Qed.

#[export] Hint Rewrite
  zero_3_f_to_vec
  one_3_f_to_vec
  two_3_f_to_vec
  three_3_f_to_vec
  four_3_f_to_vec
  five_3_f_to_vec
  six_3_f_to_vec
  seven_3_f_to_vec
  : f_to_vec_3_db.


Ltac f_to_vec_simpl_light :=
  first
  [ rewrite f_to_vec_H
  | rewrite f_to_vec_CCX
  | rewrite f_to_vec_CNOT
  ];
  try lia;
  simpl update;
  do 2 (
    repeat rewrite Mmult_plus_distr_l;
    repeat rewrite Mscale_mult_dist_r
  ).

End Common.
