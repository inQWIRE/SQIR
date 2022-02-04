Require Coq.extraction.Extraction.
Require Import DiscreteProb.
Require Import Shor.
Require Import Main.

(* Standard utilities for bools, options, etc. *)
Require Coq.extraction.ExtrOcamlBasic.

(* Custom extraction files *)
Require ExtrOcamlList.
Require ExtrOcamlR.
Require ExtrOcamlNatZ.

(* Extract Coq's Pos, N, and Z types to OCaml's Z type. *)
Extract Inductive positive => "Z.t" [ "(fun p->Z.succ (Z.mul (Z.of_int 2) p))" "(fun p->(Z.mul (Z.of_int 2) p))" "Z.one" ]
  "(fun f2p1 f2p f1 p -> if Z.leq p Z.one then f1 () else if Z.is_even p then f2p (Z.div p (Z.of_int 2)) else f2p1 (Z.div p (Z.of_int 2)))".
Extract Inductive N => "Z.t" [ "Z.zero" "" ]
  "(fun f0 fp n -> if Z.equal n Z.zero then f0 () else fp n)".
Extract Inductive BinNums.Z => "Z.t" [ "Z.zero" "" "Z.neg" ]
  "(fun f0 fp fn z -> if Z.equal z Z.zero then f0 () else if Z.gt z Z.zero then fp z else fn (Z.neg z))".
Extract Inlined Constant N.of_nat => "". (* no-op *)

(* Extract two number theory functions to their OCaml Z equivalents. *)
Extract Inlined Constant NumTheory.modinv => "Z.invert".
Extract Inlined Constant modexp => "Z.powm".

(* Special extraction to run quantum programs using a simulator *)
Extract Constant run => "Run.run_circuit".

(* Special extraction for sample - same as the original w/ an added print statement *)
Extract Constant sample => "
  let rec aux l r =
    match l with
    | [] -> Z.zero
    | x :: l' ->
      if r < x then Z.zero else Z.succ (aux l' (r -. x)) in
  fun l r -> 
  let x = aux l r in
  (Printf.printf ""Random sampling selected a = %d\n%!"" (Z.to_int x); x)".

(* Avoid conflicts with OCaml standard library *)
Extraction Blacklist List.

Separate Extraction Main.end_to_end_shors.