open Nat0

(** val fact : int -> int **)

let rec fact n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Pervasives.succ 0)
    (fun n0 -> mul (Pervasives.succ n0) (fact n0))
    n
