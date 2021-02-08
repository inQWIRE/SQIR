open BinNums
open Rdefinitions

(** val pow : coq_R -> int -> coq_R **)

let rec pow r n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_IZR (Zpos Coq_xH))
    (fun n0 -> coq_Rmult r (pow r n0))
    n
