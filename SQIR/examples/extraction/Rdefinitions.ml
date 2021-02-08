open BinNums

type coq_R = float

(** val coq_R0 : coq_R **)

let coq_R0 = 0.0

(** val coq_R1 : coq_R **)

let coq_R1 = 1.0

(** val coq_Rplus : coq_R -> coq_R -> coq_R **)

let coq_Rplus = ( +. )

(** val coq_Rmult : coq_R -> coq_R -> coq_R **)

let coq_Rmult = ( *. )

(** val coq_Ropp : coq_R -> coq_R **)

let coq_Ropp = ((-.) 0.0)

(** val coq_Rminus : coq_R -> coq_R -> coq_R **)

let coq_Rminus r1 r2 =
  coq_Rplus r1 (coq_Ropp r2)

(** val coq_Rdiv : coq_R -> coq_R -> coq_R **)

let coq_Rdiv = ( /. )

(** val coq_IPR_2 : positive -> coq_R **)

let rec coq_IPR_2 = function
| Coq_xI p0 ->
  coq_Rmult (coq_Rplus coq_R1 coq_R1) (coq_Rplus coq_R1 (coq_IPR_2 p0))
| Coq_xO p0 -> coq_Rmult (coq_Rplus coq_R1 coq_R1) (coq_IPR_2 p0)
| Coq_xH -> coq_Rplus coq_R1 coq_R1

(** val coq_IPR : positive -> coq_R **)

let coq_IPR = function
| Coq_xI p0 -> coq_Rplus coq_R1 (coq_IPR_2 p0)
| Coq_xO p0 -> coq_IPR_2 p0
| Coq_xH -> coq_R1

(** val coq_IZR : coq_Z -> coq_R **)

let coq_IZR = function
| Z0 -> coq_R0
| Zpos n -> coq_IPR n
| Zneg n -> coq_Ropp (coq_IPR n)
