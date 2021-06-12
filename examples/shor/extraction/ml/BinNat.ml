open BinNums
open BinPos

module N =
 struct
  (** val of_nat : int -> coq_N **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> N0)
      (fun n' -> Npos (Pos.of_succ_nat n'))
      n
 end
