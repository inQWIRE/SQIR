open BinNums
open Complex
open Nat

type coq_Matrix = int -> int -> coq_C

(** val coq_Zero : int -> int -> coq_Matrix **)

let coq_Zero _ _ _ _ =
  coq_RtoC (Float.of_int Z0)

(** val coq_I : int -> coq_Matrix **)

let coq_I n x y =
  if (&&) ((=) x y) (PeanoNat.Nat.ltb x n)
  then coq_RtoC (Float.of_int (Zpos Coq_xH))
  else coq_RtoC (Float.of_int Z0)

(** val coq_Mplus : int -> int -> coq_Matrix -> coq_Matrix -> coq_Matrix **)

let coq_Mplus _ _ a b x y =
  coq_Cplus (a x y) (b x y)

(** val coq_Mmult :
    int -> int -> int -> coq_Matrix -> coq_Matrix -> coq_Matrix **)

let coq_Mmult _ n _ a b x z =
  coq_Csum (fun y -> coq_Cmult (a x y) (b y z)) n

(** val kron :
    int -> int -> int -> int -> coq_Matrix -> coq_Matrix -> coq_Matrix **)

let kron _ _ o p a b x y =
  coq_Cmult (a (PeanoNat.Nat.div x o) (PeanoNat.Nat.div y p))
    (b (PeanoNat.Nat.modulo x o) (PeanoNat.Nat.modulo y p))

(** val adjoint : int -> int -> coq_Matrix -> coq_Matrix **)

let adjoint _ _ a x y =
  coq_Cconj (a y x)

(** val vec_to_list' : int -> int -> coq_Matrix -> coq_C list **)

let rec vec_to_list' nmax n v =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n' -> (v (sub nmax n) 0) :: (vec_to_list' nmax n' v))
    n

(** val vec_to_list : int -> coq_Matrix -> coq_C list **)

let vec_to_list n v =
  vec_to_list' n n v
