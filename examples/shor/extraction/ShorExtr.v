Require Coq.extraction.Extraction.
Require Import AltGateSet.
Require Import Shor.
Require Import AltShor.
Require Import Main.

(* Standard utilities for bools, options, etc. *)
Require Coq.extraction.ExtrOcamlBasic.

(* A few common functions not included in ExtrOcamlBasic. *)
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".
Extract Inlined Constant negb => "not".
Extract Inlined Constant length => "List.length".
Extract Inlined Constant app => "List.append".
Extract Inlined Constant rev => "List.rev".
Extract Inlined Constant rev_append => "List.rev_append".
Extract Inlined Constant List.map => "List.map".
Extract Inlined Constant fold_right => "(fun f a l -> List.fold_right f l a)".
Extract Inlined Constant forallb => "List.for_all".

(* Standard extraction from nat -> OCaml int. *)
Require Coq.extraction.ExtrOcamlNatInt.

(* Custom extraction from R -> OCaml float. *)
Extract Inlined Constant R => "float".
Extract Inlined Constant R0 => "0.0".
Extract Inlined Constant R1 => "1.0".
Extract Inlined Constant R2 => "2.0".
Extract Inlined Constant R4 => "4.0".
Extract Inlined Constant Rplus => "( +. )".
Extract Inlined Constant Rmult => "( *. )".
Extract Inlined Constant Ropp => "((-.) 0.0)".
Extract Inlined Constant Rinv => "((/.) 1.0)".
Extract Inlined Constant Rminus => "( -. )".
Extract Inlined Constant Rdiv => "( /. )".
Extract Inlined Constant pow => "(fun a b -> a ** Float.of_int b)".
Extract Inlined Constant cos => "cos".
Extract Inlined Constant sin => "sin".
Extract Inlined Constant tan => "tan".
Extract Inlined Constant atan => "atan".
Extract Inlined Constant acos => "acos".
Extract Inlined Constant PI => "Float.pi".
Extract Inlined Constant IZR => "Float.of_int".
(* Extracting the following to dummy values to supress warnings *)
Extract Constant ClassicalDedekindReals.sig_forall_dec  => "failwith ""Invalid extracted value"" ".
Extract Constant ClassicalDedekindReals.DRealRepr  => "failwith ""Invalid extracted value"" ".

(* special extraction for modular exponentiation so we don't run into 
   efficiency issues (this is a littele hacky -- it would be better to
   extract all operations to OCaml's Z type). -KH *)
Extract Constant modexp => "fun a x n -> Z.to_int (Z.powm (Z.of_int a) (Z.of_int x) (Z.of_int n))".

Extract Constant run_circuit => "Run.run_circuit".

Separate Extraction Main.end_to_end_shors.