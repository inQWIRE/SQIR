Require Export SQIR.UnitaryOps.

Module Common.

Open Scope ucom.

(** A toffoli gate but controlled on the first qubit 
    being zero. *)
Definition ZCCX {dim} (a b c : nat) : base_ucom dim :=
  X a;
  CCX a b c;
  X a.

End Common.
