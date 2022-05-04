Require Coq.extraction.Extraction.
Require Import AltGHZ.

(* Standard utilities for bools, options, etc. *)
Require Coq.extraction.ExtrOcamlBasic.

(* Standard extraction of nat -> int *)
Require Coq.extraction.ExtrOcamlNatInt.

(* Custom extraction files *)
Require ExtrOcamlList.
Require ExtrOcamlR.

Separate Extraction AltGHZ.ghz.