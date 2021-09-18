Require Coq.extraction.Extraction.
Require Import AltGateSet.
Require Import AltPQASM.
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
    (* RCIR modular multiplier *)
    ModMult.modmult_rev 
    AltPQASM.bc2ucom
    
    (* QVM classical modular multiplier *)
    AltPQASM.trans_modmult_rev
    
    (* QVM QFT-based modular multiplier *)
    AltPQASM.trans_rz_modmult_rev
    
    (* QVM classical adders/multipliers *)
    AltPQASM.trans_cl_adder
    AltPQASM.trans_cl_const_mul
    AltPQASM.trans_cl_mul
    
    (* QVM QFT-based adders/multpliers *)
    AltPQASM.trans_rz_const_adder
    AltPQASM.trans_rz_adder
    AltPQASM.trans_rz_const_mul
    AltPQASM.trans_rz_mul
    
    (* QVM TOFF-based divmod *)
    AltPQASM.trans_cl_mod
    AltPQASM.trans_cl_div
    AltPQASM.trans_cl_div_mod
    
    (* QVM QFT-based divmod *)
    AltPQASM.trans_rz_mod
    AltPQASM.trans_rz_div
    AltPQASM.trans_rz_div_mod
    
    (* QIMP examples*)
    AltPQASM.trans_dmc_qft
    AltPQASM.trans_dmc_cl
    AltPQASM.trans_dmq_qft
    AltPQASM.trans_dmq_cl
    
    (* decomposition pass *)
    AltGateSet.decompose_CU1_and_C3X.
