Require Coq.extraction.Extraction.
Require Import ZArith.

(* Custom extraction from nat -> OCaml Z (arbitrary precision integers) *)
Extract Inductive nat => "Z.t" [ "Z.zero" "Z.succ" ]
  "(fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))".
Extract Constant Nat.pred => "(fun a -> Z.max (Z.pred a) Z.zero)".
Extract Inlined Constant Nat.add => "Z.add".
Extract Constant Nat.sub => "(fun a b -> Z.max (Z.sub a b) Z.zero)".
Extract Inlined Constant Nat.mul => "Z.mul".
Extract Inlined Constant Nat.div => "Z.div".
Extract Inlined Constant Nat.modulo => "Z.rem".
Extract Constant Nat.pow => "(fun a b -> Z.pow a (Z.to_int b))".
Extract Inlined Constant Nat.gcd => "Z.gcd".
Extract Constant Nat.log2 => "fun n -> (Z.of_int (Z.log2 n))".
Extract Inlined Constant Nat.eqb => "Z.equal".
Extract Inlined Constant Nat.leb => "Z.leq".
Extract Inlined Constant Nat.ltb => "Z.lt".