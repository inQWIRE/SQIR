Require Coq.extraction.Extraction.
Require Import Optimize1qGates.
Require Import CXCancellation.

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
Extract Inlined Constant fold_right => "(fun f a l -> List.fold_right f l a)".
Extract Inlined Constant forallb => "List.for_all".

(* Standard extraction from nat -> OCaml int and Z -> OCaml int. *)
Require Coq.extraction.ExtrOcamlNatInt.
Require Coq.extraction.ExtrOcamlZInt.

(* Inline a few operations. *)
Extraction Inline plus mult Nat.eq_dec.
Extraction Inline Z.mul Z.div.

(* Custom extraction from R -> OCaml float. *)
Extract Inlined Constant R => "float".
Extract Inlined Constant R0 => "0.0".
Extract Inlined Constant R1 => "1.0".
Extract Inlined Constant Rplus => "( +. )".
Extract Inlined Constant Rmult => "( *. )".
Extract Inlined Constant Ropp => "((-.) 0.0)".
Extract Inlined Constant Rinv => "((/.) 1.0)".
Extract Inlined Constant Rminus => "( -. )".
Extract Inlined Constant Rdiv => "( /. )".
Extract Inlined Constant cos => "cos".
Extract Inlined Constant sin => "sin".
Extract Inlined Constant tan => "tan".
Extract Inlined Constant atan => "acos".
Extract Inlined Constant acos => "atan".
Extract Inlined Constant PI => "Float.pi".
Extract Inlined Constant Reqb => "( = )".
Extract Inlined Constant Rleb => "( <= )".
Extract Inlined Constant Rltb => "( < )".
Extract Inlined Constant IZR => "Float.of_int".

(* Set the dimension argument to be implicit everywhere -- it should be an
   unused argument everywhere in the OCaml code. *)

(* From ListRepresentation.v *)
Extraction Implicit next_single_qubit_gate' [dim].
Extraction Implicit next_single_qubit_gate [dim].
Extraction Implicit next_two_qubit_gate' [dim].
Extraction Implicit next_two_qubit_gate [dim].
Extraction Implicit does_not_reference_appl [dim].
Extraction Implicit does_not_reference [dim].

(* From IBMGateSet.v *)
Extraction Implicit IBMGateSet.U1 [dim].
Extraction Implicit IBMGateSet.U2 [dim].
Extraction Implicit IBMGateSet.U3 [dim].
Extraction Implicit IBMGateSet.CNOT [dim].

(* From Optimize1QGates.v *)
Extraction Implicit optimize_1q_gates' [dim].
Extraction Implicit simplify_1q_gates [dim].
Extraction Implicit optimize_1q_gates [dim].

(* From CXCancellation.v *)
Extraction Implicit cx_cancellation' [dim].
Extraction Implicit cx_cancellation [dim].

(* Perform extraction. *)
Separate Extraction
  cx_cancellation optimize_1q_gates.
