open BinNums

(** val coq_INR : int -> float **)

let rec coq_INR n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Float.of_int Z0)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Float.of_int (Zpos Coq_xH))
      (fun _ -> ( +. ) (coq_INR n0) (Float.of_int (Zpos Coq_xH)))
      n0)
    n
