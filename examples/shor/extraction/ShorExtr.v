Require Coq.extraction.Extraction.
Require Import AltGateSet.
Require Import Shor.
Require Import AltShor.
Require Import Main.

(* Standard utilities for bools, options, etc. *)
Require Coq.extraction.ExtrOcamlBasic.

(* Standard extraction from nat -> OCaml int. *)
Require Coq.extraction.ExtrOcamlNatInt.

(* Custom extraction files. *)
Require ExtrOcamlList.
Require ExtrOcamlR.
Extract Inlined Constant R2 => "2.0".
Extract Inlined Constant R4 => "4.0".

(* special extraction for modular exponentiation so we don't run into 
   efficiency issues (this is a littele hacky -- it would be better to
   extract all operations to OCaml's Z type). -KH *)
Extract Constant modexp => "fun a x n -> Z.to_int (Z.powm (Z.of_int a) (Z.of_int x) (Z.of_int n))".

(* Extract Constant run_circuit => "Run.run_circuit". *)

Separate Extraction Main.end_to_end_shors.
