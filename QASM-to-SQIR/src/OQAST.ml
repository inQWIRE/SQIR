type id = string [@@deriving show]
type real = float [@@deriving show]
type nninteger = int [@@deriving show]

type binaryop  =
  | Plus
  | Minus
  | Mult
  | Div
  | Pow
[@@deriving show]

type unaryop =
  | Sin
  | Cos
  | Tan
  | Exp
  | Ln
  | Sqrt
  | Neg
[@@deriving show]

type exp =
  | Real of real
  | Nninteger of nninteger
  | Pi
  | Id of id
  | Binaryop of exp * binaryop * exp
  | Unaryop of unaryop * exp
[@@deriving show]

type argument = id * nninteger option [@@deriving show]

type uop  =
  | U of exp list * argument
  | CX of argument * argument
  | X of argument
  | Y of argument
  | Z of argument
  | H of argument
  | Gate of id * exp list * argument list
[@@deriving show]

type qop  =
  | Uop of uop
  | Meas of argument * argument
  | Reset of argument
[@@deriving show]

type gop  =
  | Uop of uop
  (* | Barrier of id list *)
[@@deriving show]

type gatedecl = id * id list option * id list
[@@deriving show]

type decl =
  | Qreg of id * nninteger
  | Creg of id * nninteger
[@@deriving show]

type statement  =
  | Decl of decl
  | Newgate of gatedecl * gop list
  | Opaque of id * id list option * id list
  | Qop of qop
  | If of id * nninteger * qop
  | Barrier of argument list
[@@deriving show]

type program = statement list
[@@deriving show]
