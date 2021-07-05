Require Coq.extraction.Extraction.
Require Import AltGateSet2.
Require Import AltPQASM.
Require Import CLArith.
Require Import ModMult.
Require Import RZArith.
Require Import OracleExample.

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
    ModMult.modmult_rev 
    AltPQASM.bc2ucom
    AltPQASM.trans_modmult_rev
    AltPQASM.trans_rz_modmult_rev
    AltPQASM.trans_rz_modmult_rev_alt
    OracleExample.sin_prog
    AltPQASM.prog_to_sqir_real.
