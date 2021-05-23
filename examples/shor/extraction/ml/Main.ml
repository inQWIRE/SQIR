open AltGateSet
open AltShor
open Nat
open Shor

(** val n : int -> int **)

let n n0 =
  PeanoNat.Nat.log2
    (mul (Pervasives.succ (Pervasives.succ 0))
      (PeanoNat.Nat.pow n0 (Pervasives.succ (Pervasives.succ 0))))

(** val k : int -> int **)

let k n0 =
  num_qubits
    (PeanoNat.Nat.log2 (mul (Pervasives.succ (Pervasives.succ 0)) n0))

(** val shor_circuit : int -> int -> coq_U ucom **)

let shor_circuit =
  shor_circuit

(** val cont_frac_exp : int -> int -> int -> int **)

let cont_frac_exp a n0 o =
  coq_OF_post a n0 o (n n0)

(** val run_circuit : int -> int -> coq_U ucom -> int **)

let run_circuit = Run.run_circuit

(** val factor : int -> int -> int -> int option **)

let factor a n0 r =
  let cand1 =
    PeanoNat.Nat.gcd
      (sub
        (PeanoNat.Nat.pow a
          (PeanoNat.Nat.div r (Pervasives.succ (Pervasives.succ 0))))
        (Pervasives.succ 0)) n0
  in
  let cand2 =
    PeanoNat.Nat.gcd
      (add
        (PeanoNat.Nat.pow a
          (PeanoNat.Nat.div r (Pervasives.succ (Pervasives.succ 0))))
        (Pervasives.succ 0)) n0
  in
  if (&&) (PeanoNat.Nat.ltb (Pervasives.succ 0) cand1)
       (PeanoNat.Nat.ltb cand1 n0)
  then Some cand1
  else if (&&) (PeanoNat.Nat.ltb (Pervasives.succ 0) cand2)
            (PeanoNat.Nat.ltb cand2 n0)
       then Some cand2
       else None

(** val end_to_end_shors : int -> int -> int option **)

let end_to_end_shors a n0 =
  let n1 = n n0 in
  let k0 = k n0 in
  let circ = shor_circuit a n0 in
  let x = run_circuit (add n1 k0) n1 circ in
  let r = cont_frac_exp a n0 x in factor a n0 r
