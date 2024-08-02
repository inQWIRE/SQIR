Require Export SQIR.UnitaryOps.

Module Common.

Open Scope ucom.

(** A toffoli gate but controlled on the first qubit 
    being zero. *)
Definition ZCCX {dim} (a b c : nat) : base_ucom dim :=
  X a;
  CCX a b c;
  X a.

Lemma zero_9_f_to_vec : 
  ∣0,0,0⟩ = f_to_vec 3 (fun _ => false).
Proof.
  lma'. simpl. auto with wf_db.
Qed.

Lemma nine_9_f_to_vec : 
  ∣1,1,1⟩ = f_to_vec 3 (fun _ => true).
Proof.
  lma'. simpl. auto with wf_db.
Qed.
  

End Common.
