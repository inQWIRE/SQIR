open AltGateSet
open AltShor
open Nat
open Run
open Shor

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

(** val process : int -> int -> int option **)

let process n0 out =
  let n1 = n n0 in
  let k0 = k n0 in
  let a =
    fst_join
      (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) (add n1 k0)) out
  in
  let x =
    snd_join
      (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) (add n1 k0)) out
  in
  if (=) (PeanoNat.Nat.gcd a n0) (Pervasives.succ 0)
  then factor a n0
         (coq_OF_post a n0
           (fst_join
             (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) k0) x)
           n1)
  else Some (PeanoNat.Nat.gcd a n0)

(** val shor_body : int -> float -> int option **)

let shor_body n0 rnd =
  let n1 = n n0 in
  let k0 = k n0 in
  let distr =
    join (uniform (Pervasives.succ 0) n0) (fun a ->
      run (add n1 k0) (to_base_ucom (add n1 k0) (shor_circuit a n0)))
  in
  let out = sample distr rnd in process n0 out

(** val end_to_end_shors : int -> float list -> int option **)

let end_to_end_shors n0 rnds =
  iterate rnds (shor_body n0)
