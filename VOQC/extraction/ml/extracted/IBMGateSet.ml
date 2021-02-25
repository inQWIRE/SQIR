open UnitaryListRepresentation

module IBMGateSet =
 struct
  type coq_IBM_Unitary =
  | UIBM_U1 of float
  | UIBM_U2 of float * float
  | UIBM_U3 of float * float * float
  | UIBM_CNOT
 end

(** val coq_U1 : float -> int -> IBMGateSet.coq_IBM_Unitary gate_app **)

let coq_U1 a q =
  App1 ((IBMGateSet.UIBM_U1 a), q)

(** val coq_U2 :
    float -> float -> int -> IBMGateSet.coq_IBM_Unitary gate_app **)

let coq_U2 a b q =
  App1 ((IBMGateSet.UIBM_U2 (a, b)), q)

(** val coq_U3 :
    float -> float -> float -> int -> IBMGateSet.coq_IBM_Unitary gate_app **)

let coq_U3 a b c q =
  App1 ((IBMGateSet.UIBM_U3 (a, b, c)), q)

type coq_IBM_ucom_l = IBMGateSet.coq_IBM_Unitary gate_list

(** val atan2 : float -> float -> float **)

let atan2 y x =
  if ( < ) (Float.of_int 0) x
  then atan (( /. ) y x)
  else if ( < ) x (Float.of_int 0)
       then if ( <= ) (Float.of_int 0) y
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

(** val to_zyz_theta : float -> float -> float -> float **)

let to_zyz_theta _UU03b8_1 _UU03be_ _UU03b8_2 =
  if ( < ) (rm22 _UU03b8_1 _UU03be_ _UU03b8_2) (Float.of_int 1)
  then if ( < ) (Float.of_int ((~-) 1)) (rm22 _UU03b8_1 _UU03be_ _UU03b8_2)
       then acos (rm22 _UU03b8_1 _UU03be_ _UU03b8_2)
       else Float.pi
  else Float.of_int 0

(** val to_zyz_phi : float -> float -> float -> float **)

let to_zyz_phi _UU03b8_1 _UU03be_ _UU03b8_2 =
  if ( < ) (rm22 _UU03b8_1 _UU03be_ _UU03b8_2) (Float.of_int 1)
  then if ( < ) (Float.of_int ((~-) 1)) (rm22 _UU03b8_1 _UU03be_ _UU03b8_2)
       then atan2 (rm12 _UU03b8_1 _UU03be_ _UU03b8_2)
              (rm02 _UU03b8_1 _UU03be_ _UU03b8_2)
       else ((-.) 0.0)
              (atan2 (rm10 _UU03b8_1 _UU03be_ _UU03b8_2)
                (rm11 _UU03b8_1 _UU03be_ _UU03b8_2))
  else atan2 (rm10 _UU03b8_1 _UU03be_ _UU03b8_2)
         (rm11 _UU03b8_1 _UU03be_ _UU03b8_2)

(** val to_zyz_lambda : float -> float -> float -> float **)

let to_zyz_lambda _UU03b8_1 _UU03be_ _UU03b8_2 =
  if ( < ) (rm22 _UU03b8_1 _UU03be_ _UU03b8_2) (Float.of_int 1)
  then if ( < ) (Float.of_int ((~-) 1)) (rm22 _UU03b8_1 _UU03be_ _UU03b8_2)
       then atan2 (rm21 _UU03b8_1 _UU03be_ _UU03b8_2)
              (rm20_minus _UU03b8_1 _UU03be_ _UU03b8_2)
       else Float.of_int 0
  else Float.of_int 0

(** val compose_u3 :
    float -> float -> float -> float -> float -> float ->
    IBMGateSet.coq_IBM_Unitary **)

let compose_u3 _UU03b8_1 _UU03d5_1 _UU03bb_1 _UU03b8_2 _UU03d5_2 _UU03bb_2 =
  IBMGateSet.UIBM_U3
    ((to_zyz_theta _UU03b8_1 (( +. ) _UU03d5_1 _UU03bb_2) _UU03b8_2),
    (( +. ) (to_zyz_lambda _UU03b8_1 (( +. ) _UU03d5_1 _UU03bb_2) _UU03b8_2)
      _UU03d5_2),
    (( +. ) _UU03bb_1
      (to_zyz_phi _UU03b8_1 (( +. ) _UU03d5_1 _UU03bb_2) _UU03b8_2)))
