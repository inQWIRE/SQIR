open Rfunctions

(** val coq_Rsum : Z.t -> (Z.t -> float) -> float **)

let coq_Rsum n f =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> Z.to_float Z.zero)
    (fun n0 -> sum_f_R0 f n0)
    n
