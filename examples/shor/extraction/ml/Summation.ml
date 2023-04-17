
type 'g coq_Monoid = { coq_Gzero : 'g; coq_Gplus : ('g -> 'g -> 'g) }

(** val big_sum : 'a1 coq_Monoid -> (Z.t -> 'a1) -> Z.t -> 'a1 **)

let rec big_sum h f n =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> h.coq_Gzero)
    (fun n' -> h.coq_Gplus (big_sum h f n') (f n'))
    n
