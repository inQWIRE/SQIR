type id = string
type real = float
type nninteger = int

type binaryop  =
  | Plus
  | Minus
  | Mult
  | Div
  | Pow

type unaryop =
  | Sin
  | Cos
  | Tan
  | Exp
  | Ln
  | Sqrt
  | Neg

type exp =
  | Real of real
  | Nninteger of nninteger
  | Pi
  | Id of id
  | Binaryop of exp * binaryop * exp
  | Unaryop of unaryop * exp

type argument = id * nninteger option

type uop  =
  | U of exp list * argument
  | CX of argument * argument
  | Gate of id * exp list * argument list

type qop  =
  | Uop of uop
  | Meas of argument * argument
  | Reset of argument

type gop  =
  | Uop of uop
  (* | Barrier of id list *)

type gatedecl = id * id list option * id list

type decl =
  | Qreg of id * nninteger
  | Creg of id * nninteger

type statement  =
  | Decl of decl
  | Newgate of gatedecl * gop list
  | Opaque of id * id list option * id list
  | Qop of qop
  | If of id * nninteger * qop
  | Barrier of argument list

type program = statement list
