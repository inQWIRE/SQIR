open AltGateSet
open DiscreteProb
open ExtrShor
open Nat
open Shor

(** val factor : Z.t -> Z.t -> Z.t -> Z.t option **)

let factor a n r =
  let cand1 =
    Z.gcd
      (sub (PeanoNat.Nat.pow a (Z.div r (Z.succ (Z.succ Z.zero)))) (Z.succ
        Z.zero)) n
  in
  let cand2 =
    Z.gcd
      (add (PeanoNat.Nat.pow a (Z.div r (Z.succ (Z.succ Z.zero)))) (Z.succ
        Z.zero)) n
  in
  if (&&) (Z.lt (Z.succ Z.zero) cand1) (Z.lt cand1 n)
  then Some cand1
  else if (&&) (Z.lt (Z.succ Z.zero) cand2) (Z.lt cand2 n)
       then Some cand2
       else None

(** val run : Z.t -> coq_U ucom -> float -> Z.t **)

let run = Run.run_circuit

(** val shor_body : Z.t -> float -> Z.t option **)

let shor_body n rnd =
  let n0 = shor_output_nqs n in
  let k = modmult_nqs n in
  let adist = uniform (Z.succ Z.zero) n in
  let a = sample adist rnd in
  if Z.equal (Z.gcd a n) (Z.succ Z.zero)
  then let c = shor_circuit a n in
       let rnd' = compute_new_rnd rnd adist a in
       let x = run (shor_nqs n) c rnd' in
       factor a n (coq_OF_post a n (fst k x) n0)
  else Some (Z.gcd a n)

(** val end_to_end_shors : Z.t -> float list -> Z.t option **)

let end_to_end_shors n rnds =
  iterate rnds (shor_body n)
