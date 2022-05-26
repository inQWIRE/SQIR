Require Coq.extraction.Extraction.
Require Import ExtrGHZ.

(* Standard utilities for bools, options, etc. *)
Require Coq.extraction.ExtrOcamlBasic.

(* Standard extraction of nat -> int *)
Require Coq.extraction.ExtrOcamlNatInt.

(* Custom extraction files *)
Require ExtrOcamlList.
Require ExtrOcamlR.

Separate Extraction ExtrGHZ.ghz.