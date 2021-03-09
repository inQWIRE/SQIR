
(** val atan2 : float -> float -> float **)

let atan2 y x =
  if ( < ) (Float.of_int 0) x
  then atan (( /. ) y x)
  else if ( < ) x (Float.of_int 0)
       then if not (( < ) y (Float.of_int 0))
            then ( +. ) (atan (( /. ) y x)) Float.pi
            else ( -. ) (atan (( /. ) y x)) Float.pi
       else if ( < ) (Float.of_int 0) y
            then ( /. ) Float.pi (Float.of_int ((fun p->2*p) 1))
            else if ( < ) y (Float.of_int 0)
                 then ( /. ) (((-.) 0.0) Float.pi)
                        (Float.of_int ((fun p->2*p) 1))
                 else Float.of_int 0

(** val rm02 : float -> float -> float -> float **)

let rm02 x y z =
  ( +. ) (( *. ) (sin x) (cos z)) (( *. ) (( *. ) (cos x) (cos y)) (sin z))

(** val rm12 : float -> float -> float -> float **)

let rm12 _ y z =
  ( *. ) (sin y) (sin z)

(** val rm22 : float -> float -> float -> float **)

let rm22 x y z =
  ( -. ) (( *. ) (cos x) (cos z)) (( *. ) (( *. ) (sin x) (cos y)) (sin z))

(** val rm10 : float -> float -> float -> float **)

let rm10 _ y z =
  ( *. ) (sin y) (cos z)

(** val rm11 : float -> float -> float -> float **)

let rm11 _ y _ =
  cos y

(** val rm20_minus : float -> float -> float -> float **)

let rm20_minus x y z =
  ( +. ) (( *. ) (cos x) (sin z)) (( *. ) (( *. ) (sin x) (cos y)) (cos z))

(** val rm21 : float -> float -> float -> float **)

let rm21 x y _ =
  ( *. ) (sin x) (sin y)

(** val yzy_to_zyz : float -> float -> float -> (float * float) * float **)

let yzy_to_zyz x y z =
  if ( < ) (rm22 x y z) (Float.of_int 1)
  then if ( < ) (Float.of_int ((~-) 1)) (rm22 x y z)
       then (((atan2 (rm12 x y z) (rm02 x y z)), (acos (rm22 x y z))),
              (atan2 (rm21 x y z) (rm20_minus x y z)))
       else (((((-.) 0.0) (atan2 (rm10 x y z) (rm11 x y z))), Float.pi),
              (Float.of_int 0))
  else (((atan2 (rm10 x y z) (rm11 x y z)), (Float.of_int 0)),
         (Float.of_int 0))
