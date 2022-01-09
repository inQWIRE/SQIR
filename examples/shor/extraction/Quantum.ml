open BinNums
open Complex
open Matrix

(** val qubit0 : coq_Matrix **)

let qubit0 x y =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_RtoC (Float.of_int (Zpos Coq_xH)))
      (fun _ -> coq_RtoC (Float.of_int Z0))
      y)
    (fun n ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> coq_RtoC (Float.of_int Z0))
        (fun _ -> coq_RtoC (Float.of_int Z0))
        y)
      (fun _ -> coq_RtoC (Float.of_int Z0))
      n)
    x

(** val qubit1 : coq_Matrix **)

let qubit1 x y =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_RtoC (Float.of_int Z0))
      (fun _ -> coq_RtoC (Float.of_int Z0))
      y)
    (fun n ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> coq_RtoC (Float.of_int (Zpos Coq_xH)))
        (fun _ -> coq_RtoC (Float.of_int Z0))
        y)
      (fun _ -> coq_RtoC (Float.of_int Z0))
      n)
    x

(** val _UU03c3_x : coq_Matrix **)

let _UU03c3_x x y =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_RtoC (Float.of_int Z0))
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> coq_RtoC (Float.of_int (Zpos Coq_xH)))
        (fun _ -> coq_RtoC (Float.of_int Z0))
        n)
      y)
    (fun n ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> coq_RtoC (Float.of_int (Zpos Coq_xH)))
        (fun _ -> coq_RtoC (Float.of_int Z0))
        y)
      (fun _ -> coq_RtoC (Float.of_int Z0))
      n)
    x

(** val rotation : float -> float -> float -> coq_Matrix **)

let rotation _UU03b8_ _UU03d5_ _UU03bb_ x y =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      coq_RtoC (cos (( /. ) _UU03b8_ (Float.of_int (Zpos (Coq_xO Coq_xH))))))
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        coq_Cmult (coq_Copp (coq_Cexp _UU03bb_))
          (coq_RtoC
            (sin (( /. ) _UU03b8_ (Float.of_int (Zpos (Coq_xO Coq_xH)))))))
        (fun _ -> coq_RtoC (Float.of_int Z0))
        n)
      y)
    (fun n ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        coq_Cmult (coq_Cexp _UU03d5_)
          (coq_RtoC
            (sin (( /. ) _UU03b8_ (Float.of_int (Zpos (Coq_xO Coq_xH)))))))
        (fun n0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          coq_Cmult (coq_Cexp (( +. ) _UU03d5_ _UU03bb_))
            (coq_RtoC
              (cos (( /. ) _UU03b8_ (Float.of_int (Zpos (Coq_xO Coq_xH)))))))
          (fun _ -> coq_RtoC (Float.of_int Z0))
          n0)
        y)
      (fun _ -> coq_RtoC (Float.of_int Z0))
      n)
    x
