open ExtractionGateSet

(** val ghz : int -> coq_U ucom **)

let rec ghz n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_H 0)
      (fun n'' -> Coq_useq ((ghz n'), (coq_CX n'' n')))
      n')
    n
