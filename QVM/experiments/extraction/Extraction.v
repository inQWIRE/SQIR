Require Coq.extraction.Extraction.
Require Import AltGateSet2.
Require Import AltVSQIR.
Require Import CLArith.
Require Import ModMult.
Require Import RZArith.

(* Standard utilities for bools, options, etc. *)
Require Coq.extraction.ExtrOcamlBasic.

(* Standard extraction from nat -> OCaml int. *)
Require Coq.extraction.ExtrOcamlNatInt.

(* Custom extraction files. *)
Require ExtrOcamlList.
Require ExtrOcamlR.
Extract Inlined Constant R2 => "2.0".
Extract Inlined Constant R4 => "4.0".

(* Perform extraction *)
Separate Extraction 
    (*AltShor.bc2ucom*)
    AltVSQIR.trans_pexp
    AltVSQIR.bc2ucom
    CLArith.modmult_rev 
    ModMult.modmult_rev 
    RZArith.rz_modmult_full.