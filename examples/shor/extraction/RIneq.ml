open Rdefinitions

(** val coq_Rlt_le_dec : float -> float -> bool **)

let coq_Rlt_le_dec r1 r2 =
  let h = total_order_T r1 r2 in (match h with
                                  | Some x -> x
                                  | None -> false)
