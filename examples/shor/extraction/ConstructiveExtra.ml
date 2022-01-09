open BinNums
open BinPos

(** val coq_Z_inj_nat_rev : int -> coq_Z **)

let coq_Z_inj_nat_rev n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Z0)
    (fun _ ->
    match Pos.of_nat n with
    | Coq_xI p -> Zneg (Pos.succ p)
    | Coq_xO p -> Zpos p
    | Coq_xH -> Zneg Coq_xH)
    n
