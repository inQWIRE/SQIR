
(** val sum_f_R0 : (Z.t -> float) -> Z.t -> float **)

let rec sum_f_R0 f n =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> f Z.zero)
    (fun i -> ( +. ) (sum_f_R0 f i) (f (Z.succ i)))
    n
